#!/usr/bin/env python3
# SPDX-License-Identifier: AGPL-3.0-or-later
# Forked from v2.0.0 of github.com/JesseNaser/DuoBreak

import argparse
import base64
import getpass
import hashlib
import hmac
import importlib
import json
import os
import re
import sys
import time
from collections import OrderedDict, deque
from contextlib import closing, contextmanager, redirect_stdout, suppress
from copy import deepcopy
from datetime import datetime, timezone
from email.utils import format_datetime
from pathlib import Path
from queue import Empty
from threading import Condition, Event, Thread
from time import monotonic
from urllib.parse import urlencode

from atomicreplace import DirectorySyncError, replace_bytes

import portalocker
import pyotp
import requests
from Crypto.Cipher import AES
from Crypto.Hash import SHA512
from Crypto.Protocol.KDF import scrypt
from Crypto.PublicKey import RSA
from Crypto.Signature import pkcs1_15
from keyring.errors import PasswordDeleteError
from prompt_toolkit import PromptSession
from prompt_toolkit.history import DummyHistory
from prompt_toolkit.input import create_input
from prompt_toolkit.input.typeahead import get_typeahead
from prompt_toolkit.keys import Keys
from prompt_toolkit.layout import HSplit, Window
from prompt_toolkit.layout.controls import FormattedTextControl
from prompt_toolkit.output.defaults import create_output
from prompt_toolkit.utils import is_dumb_terminal
from questionary import Choice, select

DB_V2 = b"DBv2"  # Authenticated AES-SIV with scrypt.
SALT_SIZE = NONCE_SIZE = TAG_SIZE = 16
SCRYPT_N, SCRYPT_R, SCRYPT_P = 2**17, 8, 1
REQUEST_TIMEOUT = (5, 30)
POLL_SECONDS = 5
EXIT_KEYS = {Keys.ControlC: KeyboardInterrupt, Keys.ControlD: EOFError, Keys.ControlZ: EOFError}
PUSH_PATH = "/push/v2/device/transactions"
PUSH_DEFAULTS = {"fips_status": "1", "hsm_status": "true", "pkpush": "rsa-sha512"}
PUSH_ERRORS = (requests.RequestException, ValueError, KeyError, TypeError)
ACTIVATION_URL = re.compile(r"(?i:https://m-([0-9a-f]+)\.duosecurity\.com)/activate/([A-Za-z0-9_-]+)", re.ASCII)

UNSUPPORTED_STORAGE = "Secure storage is unsupported on this OS."
INVALID_VAULT = "Invalid or unsupported vault, expected DBv2 format."
VAULT_CHANGED = "Vault was changed by another process"
INVALID_KEY = "Invalid key data."
CONNECTION_FAILED = "connection failed"
LISTENING = "Listening for pushes ({} keys)"
LISTEN_HINTS = ("- Enter: refresh passcodes", "- m: menu", "- Backspace: exit", "- Ctrl+C: stop")


def menu_prompt(title, *options, back="Back", default=None, back_value=0, **settings):
    if default is not None and not 1 <= default <= len(options):
        raise ValueError("The default must identify a menu option")
    choices = [item if isinstance(item, Choice) else Choice(item, value=i) for i, item in [*enumerate(options, 1), (0, back)]]
    back_choice = choices[back_value - 1] if back_value else choices[-1]
    question = select(
        title, choices=choices, default=choices[default - 1].value if default else 0,
        instruction=f"(Arrows: move, Enter: select, Backspace: {back_choice.title})",
        use_shortcuts=len(choices) <= 36, use_jk_keys=False, **settings,
    )

    @question.application.key_bindings.add(Keys.Backspace, eager=True)
    def go_back(event):
        event.app.exit(result=back_choice.value)

    return question


class EnterInput:

    def __init__(self):
        self.input, self.pending, self.previous, self.codes, self.step = None, deque(), None, {}, int(time.time()) // 30
        with suppress(OSError, ValueError, AttributeError):
            if sys.stdin.isatty():
                self.input = create_input()

    def __call__(self):
        if self.input is None:
            return False
        self.pending.extend(self.input.read_keys())
        if self.input.closed:
            raise EOFError
        while self.pending:
            key = self.pending.popleft().key
            previous, self.previous = self.previous, key
            if error := EXIT_KEYS.get(key):
                raise error
            action = {"m": "menu", "M": "menu", Keys.Backspace: "stop", Keys.Enter: True, Keys.ControlJ: True}.get(key)
            if action and not (key == Keys.ControlJ and previous == Keys.Enter):
                return action
        return False

    def close(self):
        if self.input is not None:
            self.input.close()

    def get(self, listener):
        refresh = self()
        if refresh in ("menu", "stop"):
            return refresh
        step = int(time.time()) // 30
        if not refresh and step != self.step:
            timed = {name: row for name, row in self.codes.items() if row[0] == "TOTP"}
            if timed:
                print(*passcode_lines(timed), sep="\n")
        self.step = step
        return None if refresh else listener.get(timeout=0.25)


class LiveDisplay:

    def __init__(self, title):
        self.title, self.codes, self.status, self.poll_errors, self.count = title, {}, "", {}, 0
        self.question = None
        self.session = PromptSession(output=create_output(), input=create_input(), history=DummyHistory(), erase_when_done=True, refresh_interval=0.25)

    def render(self, prompt=""):
        sections = (
            "\n".join((f"Vault: {self.title}", *passcode_lines(self.codes))),
            "\n".join((LISTENING.format(self.count), *(LISTEN_HINTS[-1:] if prompt else ()))),
            self.status,
            "\n".join(filter(None, self.poll_errors.values())),
        )
        return "\n\n".join(filter(None, sections)) + "\n" + prompt

    def get(self, listener):
        def poll(app):
            if app.is_done:
                return
            try:
                app.exit(result=listener.get(timeout=0))
            except Empty:
                pass
            except Exception as error:
                app.exit(exception=error)

        if self.question is None:
            self.question = menu_prompt(
                "Passcode screen", "Refresh passcodes", "Main menu", back="Exit", default=1,
                input=self.session.app.input, output=self.session.app.output,
                refresh_interval=self.session.refresh_interval, erase_when_done=True,
            )
            app = self.question.application
            app.layout.container = HSplit([Window(FormattedTextControl(self.render), dont_extend_height=True), app.layout.container])
            app.before_render += poll
        result = self.question.unsafe_ask()
        if isinstance(result, tuple):
            return result  # Keep the highlighted action when polling redraws the menu.
        self.question = None
        return ("stop", None, "menu")[result]

    def _discard_input(self):
        # Input intended for a previous screen shouldn't approve new pushes.
        source = self.session.app.input
        for key in get_typeahead(source) + source.read_keys() + source.flush_keys():
            if error := EXIT_KEYS.get(key.key):
                raise error
        if source.closed:
            raise EOFError

    def ask(self, prompt):
        return self.session.prompt(lambda: self.render(prompt), pre_run=self._discard_input)

    def close(self):
        self.question = None
        self.codes.clear()
        self.status = ""
        self.poll_errors.clear()
        self.session.default_buffer.reset()
        get_typeahead(self.session.app.input)
        self.session.app.input.close()


class PasswordStoreError(RuntimeError):
    """Native password storage failed."""


class PasswordStore:
    """Lazily use an OS keyring, separate from the original client's storage."""

    service = "LocalDuoStorage vault passwords (keyring)"

    def __init__(self, vault_path, *, platform=None):
        self._platform = platform or sys.platform
        canonical_path = os.path.normcase(str(Path(vault_path).expanduser().resolve()))
        self._identity = hashlib.sha256(os.fsencode(canonical_path)).hexdigest()

    @contextmanager
    def _open(self, error_message):
        platform = "linux" if self._platform.startswith("linux") else self._platform
        backends = {"win32": ("Windows", "WinVaultKeyring"), "darwin": ("macOS", "Keyring"), "linux": ("SecretService", "Keyring")}
        if platform not in backends:
            raise PasswordStoreError(UNSUPPORTED_STORAGE)
        message = "OS secure storage unavailable. Unlock manually."
        try:
            module, name = backends[platform]
            backend = getattr(importlib.import_module(f"keyring.backends.{module}"), name)()
            if platform == "win32":
                backend.persist = "local machine"
            message = error_message
            yield backend
        except EOFError:
            raise
        except Exception:
            raise PasswordStoreError(message) from None

    def load(self):
        with self._open("Cannot read saved password. Unlock manually.") as backend:
            password = backend.get_password(self.service, self._identity)
            if password is not None and not isinstance(password, str):
                raise TypeError
            return password or None

    def save(self, password):
        if not isinstance(password, str) or not password:
            raise PasswordStoreError("Password must be a nonempty string.")
        with self._open("Cannot save and verify the password in OS secure storage.") as backend:
            backend.set_password(self.service, self._identity, password)
            if backend.get_password(self.service, self._identity) != password:
                raise ValueError

    def forget(self):
        with self._open("Cannot remove saved password.") as backend:
            with suppress(PasswordDeleteError):
                backend.delete_password(self.service, self._identity)
            if backend.get_password(self.service, self._identity) is not None:
                raise ValueError


def key_otp(key):
    """Build the configured OTP, HOTP starts at the next unused counter."""
    response = key["response"]
    raw_secret = response["hotp_secret"]
    use_totp = response.get("use_totp", False)
    if not isinstance(raw_secret, str) or not raw_secret or type(use_totp) is not bool:
        raise ValueError("Invalid OTP data")
    secret = base64.b32encode(raw_secret.encode("ascii")).decode("ascii")
    if use_totp:
        return pyotp.TOTP(secret)
    counter = key.get("hotp_counter", 0)
    if type(counter) is not int or not 0 <= counter < 2**64 - 1:
        raise ValueError("Invalid HOTP counter")
    return pyotp.HOTP(secret, initial_count=counter + 1)


def passcode_hidden(key):
    return isinstance(key, dict) and key.get("hide_passcode") is True


def passcode_lines(codes):
    now = time.time()
    timestamp = datetime.fromtimestamp(now, timezone.utc)
    expires = datetime.fromtimestamp((int(now) // 30 + 1) * 30, timezone.utc).astimezone()
    for kind, heading in (("TOTP", f"Passcodes (TOTP, expires {expires:%H:%M:%S})"), ("HOTP", "Passcodes (HOTP)"), ("", "Unavailable")):
        group = [(name, value) for name, (mode, value) in codes.items() if mode == kind]
        if group:
            yield heading
            for name, value in group:
                yield f"- [{name}] {value.at(timestamp) if kind == 'TOTP' else value}"


class PushResponseError(ValueError):
    """A mobile-push response failure with a safe, locally generated message."""


def push_transactions(result):
    if not isinstance(result, dict):
        raise PushResponseError("invalid mobile push response")
    if result.get("stat", "OK") != "OK":
        raise PushResponseError("Duo rejected the mobile push poll")
    response = result.get("response")
    if not isinstance(response, dict):
        raise PushResponseError("missing mobile push transaction list")
    transactions = response.get("transactions")
    if transactions is None and result.get("stat") == "OK":
        return []
    if not isinstance(transactions, list):
        raise PushResponseError("invalid mobile push transaction list")
    return transactions


def response_json(response):
    if response.status_code in range(300, 400):
        raise ValueError("Duo request redirected unexpectedly")
    response.raise_for_status()
    result = response.json()
    if not isinstance(result, dict):
        raise ValueError("Invalid Duo response")
    return result


class PushListener:
    """Independent polling workers, at most one unread result per key."""

    def __init__(self, keys, poll, interval=5):
        if interval < 0:
            raise ValueError("Polling interval cannot be negative")
        self._keys, self._poll, self._interval, self._stop, self._condition, self._updates, self._pending, self._threads, self._started = deepcopy(keys), poll, interval, Event(), Condition(), OrderedDict(), {}, [], False

    def __enter__(self):
        if self._started or self._stop.is_set():
            raise RuntimeError("A push listener cannot be restarted")
        self._started = True
        try:
            for name, key in self._keys.items():
                worker = Thread(target=self._run, args=(name, key), daemon=True)
                worker.start()
                self._threads.append(worker)
        except BaseException:
            self.close()
            raise
        return self

    def _run(self, name, key):
        while not self._stop.is_set():
            try:
                result = push_transactions(self._poll(key))
                pending = {transaction["urgid"] for transaction in result if isinstance(transaction, dict) and isinstance(transaction.get("urgid"), str)}
            except Exception as error:  # noqa: BLE001 - isolate worker failures
                result = DuoAuthenticator.request_error(error)
            with self._condition:
                if self._stop.is_set():
                    return
                if isinstance(result, list):
                    self._pending[name] = pending
                self._updates[name] = result
                self._condition.notify()
            if self._stop.wait(self._interval):
                return

    def get(self, timeout=0.25):
        """Return (key name, latest result), raise queue.Empty on timeout."""
        with self._condition:
            if not self._condition.wait_for(lambda: self._updates, timeout):
                raise Empty
            return self._updates.popitem(last=False)

    def is_pending(self, name, urgid):
        """Check the latest validated snapshot, exclude malformed entries."""
        with self._condition:
            return isinstance(urgid, str) and urgid in self._pending.get(name, ())

    def close(self):
        """Discard late results, join all daemon workers within one second."""
        with self._condition:
            self._stop.set()
        deadline = monotonic() + 1
        for worker in self._threads:
            worker.join(max(0, deadline - monotonic()))

    def __exit__(self, exc_type, exc_value, traceback):
        self.close()


class DuoAuthenticator:
    def __init__(self, config_file=None, password_store=None):
        self.config_file = Path(config_file) if config_file else None
        self.config = {}
        self.salt = self.encryption_key = self.vault_digest = None
        self.lock_file = None
        self.password_store = password_store
        self.display = None
        self.passcodes = {}

    def say(self, message):
        if self.display is None:
            print(message)
        else:
            self.display.status = message.strip()

    def ask(self, prompt):
        with suppress(EOFError, KeyboardInterrupt):
            return (self.display.ask if self.display is not None else input)(prompt).strip()
        if self.display is None:
            print()

    def confirm(self, prompt, *, default=False):
        answer = self.ask(f"{prompt} [{'Y/n' if default else 'y/N'}]: ")
        return answer is not None and (answer.lower() != "n" if default else answer.lower() == "y")

    @staticmethod
    def menu(*args, **kwargs):
        """Return an option's value, or None for Back/cancellation."""
        with suppress(EOFError, KeyboardInterrupt):
            value = menu_prompt(*args, **kwargs).unsafe_ask()
            return None if value == 0 else value

    @staticmethod
    def password(prompt, confirm=False, *, min_length=12, allow_empty=False):
        with suppress(EOFError, KeyboardInterrupt):
            while True:
                password = getpass.getpass(prompt)
                if not password or not confirm:
                    return password if password or allow_empty else None
                if len(password) < min_length:
                    print(f"Use at least {min_length} characters for the vault password.")
                    continue
                if password == getpass.getpass("Confirm password: "):
                    return password
                print("Passwords do not match.")
        print()

    @staticmethod
    def vault_filename(name):
        if not name:
            return None
        if (
            name.endswith((".", " "))
            or re.search(r'[<>:"/\\|?*\x00-\x1f]', name)
            or re.match(r"(?i:con|prn|aux|nul|com[1-9¹²³]|lpt[1-9¹²³]|conin\$|conout\$) *(?:\.|$)", name)
        ):
            print("Enter a valid filename, without a path.")
            return None
        return name if name.lower().endswith(".duo") else name + ".duo"

    def select_vault(self, *, create=True):
        for directory in (Path.cwd(), Path(__file__).resolve().parent):
            vaults = sorted((path for path in directory.glob("*") if path.name.lower().endswith(".duo") and path.is_file()), key=lambda path: path.name.lower())
            if vaults:
                choice = 1 if len(vaults) == 1 else self.menu("Vaults", *(path.name for path in vaults), back="Exit")
                if choice:
                    self.config_file = vaults[choice - 1]
                return bool(choice)

        if not create:
            print("No Duo vault found.")
            return False
        print("No Duo vault found. Create one to continue.")
        while name := self.ask("Vault name (leave empty to exit): "):
            if filename := self.vault_filename(name):
                self.config_file = Path(filename)
                return True
        return False

    @staticmethod
    def derive_key(password, salt):
        try:
            return bytearray(scrypt(password.encode(), salt, 64, SCRYPT_N, SCRYPT_R, SCRYPT_P))
        except (MemoryError, ValueError, UnicodeError) as error:
            raise RuntimeError("Vault key derivation failed") from error

    @staticmethod
    def wipe(value):
        if isinstance(value, bytearray):
            value[:] = b"\0" * len(value)

    @staticmethod
    def valid_vault_header(blob):
        return isinstance(blob, bytes) and blob.startswith(DB_V2) and len(blob) > 4 + SALT_SIZE + NONCE_SIZE + TAG_SIZE

    def decrypt_vault(self, blob, password):
        if not self.valid_vault_header(blob):
            raise ValueError(INVALID_VAULT)
        key = plaintext = None
        try:
            salt, nonce = blob[4:20], blob[20:36]
            key = self.derive_key(password, salt)
            cipher = AES.new(key, AES.MODE_SIV, nonce=nonce)
            cipher.update(blob[:36])
            plaintext = bytearray(cipher.decrypt_and_verify(blob[52:], blob[36:52]))
            config = json.loads(plaintext.decode("utf-8"))
            if not isinstance(config, dict) or not isinstance(config.setdefault("keys", {}), dict):
                raise ValueError("Invalid vault data")
            return config, key, salt
        except BaseException:
            self.wipe(key)
            raise
        finally:
            self.wipe(plaintext)

    @staticmethod
    def acquire_vault_lock(path):
        lock = portalocker.Lock(str(Path(path).absolute()) + ".lock", mode="a+b", timeout=0, opener=lambda path, flags: os.open(path, flags, 0o600))
        with suppress(OSError, portalocker.exceptions.LockException):
            lock.acquire()
            return lock

    def lock_vault(self):
        if self.lock_file is None and self.config_file:
            self.lock_file = self.acquire_vault_lock(self.config_file)
        return self.lock_file is not None

    def load_config(self):
        if not self.lock_vault():
            print("This vault is already open or could not be locked.")
            return False
        loaded = False
        try:
            path = self.config_file
            if not path.exists():
                password = self.password("Create a vault password (leave empty to cancel): ", confirm=True)
                if password is None:
                    return False
                self.config = {"keys": {}}
                self.reencrypt_vault(password)
                loaded = True
                return True

            blob = path.read_bytes()
            if not self.valid_vault_header(blob):
                print(INVALID_VAULT)
                return False
            self.vault_digest = hashlib.sha256(blob).digest()

            try:
                saved_password = self.get_password_store().load()
            except PasswordStoreError:
                saved_password = None
                print("Saved password unavailable. Enter the vault password manually.")
            had_saved_password = saved_password is not None
            for _ in range(3 + int(had_saved_password)):
                using_saved_password = saved_password is not None
                password, saved_password = saved_password, None
                if not using_saved_password:
                    password = self.password("Vault password (leave empty to cancel): ")
                if password is None:
                    return False
                try:
                    self.config, self.encryption_key, self.salt = self.decrypt_vault(blob, password)
                except (ValueError, TypeError):
                    if using_saved_password:
                        print("Saved password did not unlock this vault. Enter it manually.")
                    else:
                        print("Wrong password or damaged vault.")
                    continue

                loaded = True
                if had_saved_password and not using_saved_password:
                    self.save_password(password)
                return True

            print("Too many failed password attempts.")
        except RuntimeError:
            print("Not enough resources to secure or unlock the vault.")
        except (OSError, ValueError):
            print("Could not read or save the encrypted vault.")
        finally:
            if not loaded:
                self.close()
        return False

    def reencrypt_vault(self, password):
        """Commit a fresh encryption key before replacing the unlocked key."""
        salt = os.urandom(SALT_SIZE)
        key = self.derive_key(password, salt)
        try:
            self.save_config(key=key, salt=salt)
            self.salt, self.encryption_key, key = salt, key, self.encryption_key
        finally:
            self.wipe(key)

    def save_config(self, key=None, salt=None):
        if not self.lock_vault():
            raise OSError("Vault is already open in another process")
        key = key if key is not None else self.encryption_key
        salt = salt if salt is not None else self.salt
        if key is None or salt is None or len(key) != 64 or len(salt) != SALT_SIZE:
            raise ValueError("Vault is not unlocked")

        plaintext = bytearray(json.dumps(self.config, separators=(",", ":")).encode("utf-8"))
        try:
            nonce = os.urandom(NONCE_SIZE)
            header = DB_V2 + salt + nonce
            cipher = AES.new(key, AES.MODE_SIV, nonce=nonce)
            cipher.update(header)
            ciphertext, tag = cipher.encrypt_and_digest(plaintext)
            encrypted = header + tag + ciphertext

            path = self.config_file
            try:
                current_digest = hashlib.sha256(path.read_bytes()).digest()
            except FileNotFoundError:
                current_digest = None
            if current_digest != self.vault_digest:
                raise OSError(VAULT_CHANGED)
            with suppress(DirectorySyncError):
                replace_bytes(path, encrypted, permissions=0o600, allow_hardlinks=True, durability="full" if os.name == "posix" else "data")
            self.vault_digest = hashlib.sha256(encrypted).digest()
        finally:
            self.wipe(plaintext)

    def get_password_store(self):
        if self.password_store is None:
            self.password_store = PasswordStore(self.config_file)
        return self.password_store

    def verified_password(self, password=None):
        """Verify a supplied password, or prompt for the current one."""
        if password is None and (password := self.password("Current vault password (leave empty to cancel): ")) is None:
            return None
        key = None
        try:
            key = self.derive_key(password, self.salt)
            if hmac.compare_digest(key, self.encryption_key):
                return password
            print("Incorrect vault password.")
        except (RuntimeError, TypeError):
            print("Could not verify the vault password.")
        finally:
            self.wipe(key)

    def save_password(self, password):
        try:
            self.get_password_store().save(password)
            return True
        except PasswordStoreError:
            print("Could not securely save the password. Use manual unlock.")
            self.forget_password()
            return False

    def remember_password(self):
        print("This OS account will be able to unlock the vault automatically.")
        password = self.verified_password()
        if password is not None and self.save_password(password):
            print("Vault password saved securely on this device.")

    def forget_password(self):
        try:
            self.get_password_store().forget()
            print("Saved password forgotten. Next launch requires manual unlock.")
        except PasswordStoreError:
            print("Could not forget the saved password. Try again.")

    def vault_settings(self):
        actions = [
            Choice("Rename vault", value=self.rename_vault),
            Choice("Remember vault password on this device", value=self.remember_password),
            Choice("Forget saved password", value=self.forget_password),
            Choice("Change vault password", value=self.change_password),
        ]
        while action := self.menu("Vault settings", *actions):
            action()

    def rename_vault(self):
        name = self.vault_filename(self.ask("New vault name (empty to cancel): "))
        if not name:
            return
        source = self.config_file
        target = source.with_name(name)
        if os.path.normcase(str(source.absolute())) == os.path.normcase(str(target.absolute())):
            return
        lock = None
        try:
            if not self.lock_vault() or source.is_symlink():
                raise OSError("Vault cannot be renamed")
            lock = self.acquire_vault_lock(target)
            if lock is None:
                raise OSError("Destination vault is locked")
            if hashlib.sha256(source.read_bytes()).digest() != self.vault_digest:
                raise OSError(VAULT_CHANGED)
            if os.name == "nt":
                os.rename(source, target)  # Windows refuses an existing target.
            else:
                os.link(source, target)  # Atomically create without overwriting.
                try:
                    source.unlink()
                except OSError:
                    target.unlink()
                    raise
            self.lock_file, lock = lock, self.lock_file
        except (OSError, portalocker.exceptions.LockException):
            print("Could not rename vault. Check permissions and open copies.")
            return
        finally:
            if lock is not None:
                with suppress(OSError, ValueError, portalocker.exceptions.LockException):
                    lock.release()
        old_store = self.get_password_store()
        self.config_file = target
        self.password_store = PasswordStore(target)
        self.migrate_password(old_store)
        print(f"Vault renamed to {target.name}.")

    def migrate_password(self, old_store):
        """Move a verified saved password, never replace another store entry."""
        clear_old = True
        try:
            password = old_store.load()
            clear_old = password is not None
            if password is None:
                return
            if self.verified_password(password) is None:
                raise PasswordStoreError("Saved password is stale")
            if self.password_store.load() is not None:
                raise PasswordStoreError("Destination already has a saved password")
            self.save_password(password)
        except (PasswordStoreError, RuntimeError, TypeError):
            print("Saved password not moved. Unlock manually, then remember it again.")
        finally:
            if clear_old:
                try:
                    old_store.forget()
                except PasswordStoreError:
                    print("Could not clear the old vault's saved password.")

    def change_password(self):
        if self.verified_password() is None:
            return
        password = self.password("New vault password (leave empty to cancel): ", confirm=True)
        if password is None:
            return
        try:
            self.reencrypt_vault(password)
        except RuntimeError:
            print("Not enough resources to change the vault password.")
            return
        except (OSError, ValueError):
            print("Could not change the vault password.")
            return
        try:
            if self.get_password_store().load() is not None:
                self.save_password(password)
        except PasswordStoreError:
            print("Saved password could not be read, clearing it for manual unlock.")
            self.forget_password()
        print("Vault password changed.")

    @staticmethod
    def parse_activation_url(activation_url):
        if not isinstance(activation_url, str) or not (match := ACTIVATION_URL.fullmatch(activation_url)):
            raise ValueError("invalid Duo activation URL")
        return match[2], f"api-{match[1].lower()}.duosecurity.com"

    def activate(self, code, host):
        key_pair = RSA.generate(2048)
        public_key = key_pair.publickey().export_key("PEM").decode("ascii")
        headers = {"User-Agent": "DuoMobileApp/4.117.1 (arm64; iOS 26.6); Client: Foundation", "Accept": "*/*", "Accept-Language": "en-us"}
        data = {
            "app_id": "com.duosecurity.DuoMobile",
            "app_version": "4.117.1",
            "ble_status": "allowed",
            "build_version": "23G71",
            "customer_protocol": "1",
            "device_name": "iPhone",
            "jailbroken": "false",
            "language": "en",
            "manufacturer": "Apple",
            "model": "arm64",
            "notification_status": "not_determined",
            "passcode_status": "true",
            "pkpush": "rsa-sha512",
            "platform": "iOS",
            "pubkey": public_key,
            "region": "US",
            "security_patch_level": "",
            "touchid_status": "true",
            "version": "26.6",
        }
        try:
            response = requests.post(f"https://{host}/push/v2/activation/{code}", headers=headers, data=data, timeout=REQUEST_TIMEOUT, allow_redirects=False)
            activation = response_json(response).get("response")
            if not isinstance(activation, dict):
                raise ValueError("Activation was rejected")
            return activation, public_key, key_pair.export_key("PEM").decode("ascii")
        except (requests.RequestException, ValueError, TypeError):
            print("Duo activation failed. Check the code, host, and connection.")

    def add_key(self):
        print("\nWhen setting up a new Duo device, select Apple iOS tablet.")
        while (name := self.ask("Nickname (leave empty to cancel): ")) and name in self.config["keys"]:
            print("That nickname already exists.")
        if not name:
            return

        while url := self.ask("Activation URL (leave empty to cancel): "):
            try:
                code, host = self.parse_activation_url(url)
                break
            except ValueError as error:
                print(f"Invalid Duo activation URL: {error}")
        else:
            return

        while not (activated := self.activate(code, host)):
            if not self.confirm("Retry this activation?", default=True):
                return

        response, public_key, private_key = activated
        key = {"code": code, "host": host, "response": response, "pubkey": public_key, "privkey": private_key}
        while not self.save_changes(self.config["keys"], {name: key}):
            print("Save failed. This activation may be one-use, leaving permanently discards it.")
            if not self.confirm("Retry saving?", default=True):
                print("The activated key was not saved.")
                return
        print(f"Key '{name}' added.")

    def duo_request(self, key, method, path, data):
        # Duo verifies a canonical, alphabetically sorted parameter string.
        data = dict(sorted(data.items()))
        private_key = RSA.import_key(key["privkey"].encode("ascii"))
        duo_date = format_datetime(datetime.now(timezone.utc))
        message = "\n".join((duo_date, method, key["host"].lower(), path, urlencode(data))).encode("ascii")
        signature = base64.b64encode(pkcs1_15.new(private_key).sign(SHA512.new(message))).decode("ascii")
        headers = {"x-duo-date": duo_date, "host": key["host"]}
        if method == "POST":
            headers["txId"] = path.rsplit("/", 1)[-1]
        response = requests.request(
            method,
            f"https://{key['host']}{path}",
            auth=(key["response"]["pkey"], signature),
            headers=headers,
            params=data if method == "GET" else None,
            data=data if method == "POST" else None,
            timeout=REQUEST_TIMEOUT,
            allow_redirects=False,
        )
        if method == "POST" and response.status_code == 400:
            with suppress(ValueError, AttributeError):
                rejection = response.json()
                if rejection.get("stat") == "FAIL" and str(rejection.get("code")) == "40032":
                    return {"stat": "FAIL", "code": 40032}
        return response_json(response)

    @staticmethod
    def request_error(error):
        """Describe failures without printing request URLs, headers, or bodies."""
        if isinstance(error, PushResponseError):
            return str(error)
        if isinstance(error, requests.HTTPError) and error.response is not None:
            response = error.response
            detail = f"HTTP {response.status_code}"
            with suppress(ValueError, AttributeError):
                code = str(response.json().get("code", ""))
                if re.fullmatch(r"[0-9]{5}", code):
                    detail += f" (Duo {code})"
            return detail
        for kind, detail in (
            (requests.Timeout, "request timed out"),
            (requests.exceptions.SSLError, "TLS connection failed"),
            (requests.ConnectionError, CONNECTION_FAILED),
            (requests.exceptions.JSONDecodeError, "invalid JSON response"),
            ((ValueError, KeyError, TypeError), "invalid request or response data"),
        ):
            if isinstance(error, kind):
                return detail
        return "request failed"

    def validated_push_key(self, key_name):
        """Copy only the credentials needed by polling workers, never vault state."""
        key = self.config["keys"][key_name]
        try:
            response = {field: key["response"][field] for field in ("akey", "pkey")}
            if not re.fullmatch(r"api-[0-9a-f]+\.duosecurity\.com", key["host"].lower()) or not all(
                re.fullmatch(r"[A-Za-z0-9._~-]{1,512}", v) for v in response.values()
            ):
                raise ValueError
            RSA.import_key(key["privkey"].encode("ascii"))
            return {"host": key["host"], "privkey": key["privkey"], "response": response}
        except (ValueError, TypeError, KeyError, AttributeError, IndexError):
            print(f"[{key_name}] This key has invalid Duo Mobile Push data.")

    def push_request(self, key, transaction_id=None, **parameters):
        data = dict(PUSH_DEFAULTS, akey=key["response"]["akey"]) | parameters
        path = f"{PUSH_PATH}/{transaction_id}" if transaction_id else PUSH_PATH
        return self.duo_request(key, "POST" if transaction_id else "GET", path, data)

    @staticmethod
    def push_expired(transaction):
        expiration = transaction.get("expiration")
        return isinstance(expiration, (int, float)) and not isinstance(expiration, bool) and time.time() >= expiration

    def prompt_push_action(self, key_name, info=None):
        digits = info.get("num_digits") if isinstance(info, dict) else None
        if info is not None and (type(digits) is not int or not 3 <= digits <= 7):
            raise ValueError("invalid Verified Duo Push metadata")
        prompt = f"Enter the {digits}-digit verification code (blank to stop): " if info is not None else "[Enter/y] Approve, [s] skip, [q] stop: "
        while True:
            answer = self.ask(f"[{key_name}] {prompt}")
            if info is not None:
                if not answer:
                    return None
                if re.fullmatch(rf"[0-9]{{{digits}}}", answer):
                    return answer
                self.say(f"Enter exactly {digits} ASCII digits.")
            else:
                answer = answer.lower() if answer else answer
                if answer in (None, "q"):
                    return None
                if answer in ("y", "", "s", "n"):
                    return answer in ("", "y")
                self.say("Press Enter to approve, or enter y, s, or q.")

    def process_pushes(self, key_name, key, transactions, handled, is_pending=None):
        """Handle a poll on the main thread, False means stop listening."""
        valid = {}
        for transaction in transactions:
            if (
                not isinstance(transaction, dict)
                or not isinstance(transaction.get("urgid"), str)
                or not re.fullmatch(r"[A-Za-z0-9_-]{1,128}", transaction["urgid"])
            ):
                self.say(f"[{key_name}] Skipped a malformed Duo transaction.")
                continue
            valid[transaction["urgid"]] = transaction
        handled.intersection_update(valid)
        for transaction_id, transaction in valid.items():
            if transaction_id in handled:
                continue
            info = transaction.get("step_up_code_info")
            push_name = "Verified Duo Push" if info is not None else "Duo Mobile Push"
            label = f"[{key_name}] {push_name}"
            summary = transaction.get("summary") or transaction.get("type") or "Sign-in"
            if self.push_expired(transaction):
                self.say(f"[{key_name}] Skipped an expired Duo transaction.")
                handled.add(transaction_id)
                continue
            if is_pending is not None and not is_pending(key_name, transaction_id):
                continue
            self.say(f"\n{label}: {summary}")
            while not self.push_expired(transaction):
                try:
                    answer = self.prompt_push_action(key_name, info)
                except ValueError as error:
                    self.say(f"[{key_name}] Cannot process {push_name}: {error}.")
                    break
                if answer is None:
                    return False
                if answer is False:
                    self.say(f"{label} skipped.")
                    break
                # Input can outlive the transaction or a later poll may cancel it.
                if self.push_expired(transaction) or (is_pending is not None and not is_pending(key_name, transaction_id)):
                    self.say(f"{label} is no longer pending.")
                    break
                reply_data = {"answer": "approve"}
                if info is not None:
                    reply_data.update(step_up_code=answer, step_up_code_autofilled="false")
                try:
                    reply = self.push_request(key, transaction_id, **reply_data)
                except PUSH_ERRORS as error:
                    self.say(f"{label} approval could not be confirmed: {self.request_error(error)}. Still listening.")
                    return True
                if reply.get("stat") == "OK":
                    self.say(f"{label} approved.")
                    break
                if info is not None and str(reply.get("code")) == "40032":
                    self.say("Incorrect verification code.")
                    continue
                message = reply.get("message")
                self.say(f"{label} rejected" + (f": {message}" if message else "."))
                break
            else:
                self.say(f"{label} expired.")
            handled.add(transaction_id)
        return True

    def generate_passcodes(self):
        self.passcodes.clear()
        self.passcodes.update((name, self.make_passcode(name)) for name, key in list(self.config["keys"].items()) if not passcode_hidden(key))
        if self.display is None:
            print(f"\nVault: {self.config_file.name if self.config_file else '(unsaved)'}", *passcode_lines(self.passcodes), sep="\n")

    def passcode_screen(self):
        if not self.config["keys"]:
            print("No keys saved.")
            return "menu"
        keys = {name: key for name in self.config["keys"] if (key := self.validated_push_key(name)) is not None}
        handled = {name: set() for name in keys}
        poll_errors = {}
        if sys.stdin.isatty() and sys.stdout.isatty() and (sys.platform == "win32" or not is_dumb_terminal()):
            self.display = LiveDisplay(self.config_file.name if self.config_file else "(unsaved)")
            self.display.count = len(keys)
            self.display.poll_errors = poll_errors
        try:
            with closing(self.display or EnterInput()) as keyboard, PushListener(keys, self.push_request, interval=POLL_SECONDS) as listener:
                keyboard.codes = self.passcodes
                self.generate_passcodes()
                if not keys:
                    self.say("No keys support mobile push.")
                    if not any(kind for kind, _ in self.passcodes.values()):
                        return "menu"
                if self.display is None:
                    print("\n" + LISTENING.format(len(keys)), *LISTEN_HINTS, sep="\n")
                while True:
                    try:
                        update = keyboard.get(listener)
                    except Empty:
                        continue
                    if update in ("menu", "stop"):
                        return "menu" if update == "menu" else None
                    if update is None:
                        self.generate_passcodes()
                        continue
                    name, result = update
                    try:
                        if isinstance(result, str):
                            raise PushResponseError(result)
                        if poll_errors.pop(name, None) and self.display is None:
                            print(f"[{name}] Mobile push connection restored.")
                        if not self.process_pushes(name, keys[name], result, handled[name], listener.is_pending):
                            return
                    except PUSH_ERRORS as error:
                        detail = self.request_error(error)
                        if detail == CONNECTION_FAILED and name not in poll_errors:
                            poll_errors[name] = ""
                            continue  # Retry an isolated connection drop quietly.
                        message = f"[{name}] Mobile push check failed: {detail}, retrying."
                        if poll_errors.get(name) != message:
                            poll_errors[name] = message
                            if self.display is None:
                                print(message)
        except (KeyboardInterrupt, EOFError):
            print("\nStopped checking for mobile pushes.")
        finally:
            self.display = None
            self.passcodes.clear()

    def run_default(self):
        while self.passcode_screen() == "menu" and self.main_menu():
            pass

    def save_changes(self, mapping, changes, error=None):
        """Save an update, restoring the original objects if the write fails."""
        previous = mapping.copy()
        mapping.update(changes)
        try:
            self.save_config()
        except (OSError, ValueError):
            mapping.clear()
            mapping.update(previous)
            if error:
                print(error)
            return False
        return True

    def make_passcode(self, key_name):
        key = self.config["keys"][key_name]
        try:
            otp = key_otp(key)
            if isinstance(otp, pyotp.TOTP):
                return "TOTP", otp
            history = key.get("hotp_log", [])
            if not isinstance(history, list):
                raise ValueError
            code = otp.at(0)
        except (KeyError, TypeError, UnicodeError, ValueError):
            return "", "Passcodes not supported."

        entry = f"{datetime.now(timezone.utc):%Y-%m-%d %H:%M:%S} ({key_name}): {code}"
        if not self.save_changes(self.config["keys"], {key_name: dict(key, hotp_counter=otp.initial_count, hotp_log=[*history, entry])}):
            return "", "Passcode not generated: the vault could not be saved."
        return "HOTP", code

    def export_secret(self, name):
        try:
            otp = key_otp(self.config["keys"][name])
            uri = otp.provisioning_uri(name=name.replace(":", " -"), issuer_name="Duo")
        except (KeyError, TypeError, UnicodeError, ValueError):
            print("This key has invalid or unsupported OTP data.")
            return
        use_totp = isinstance(otp, pyotp.TOTP)
        print(
            f"\n[{name}] OTP export - keep this secret private.",
            f"Secret key (Base32): {otp.secret}",
            "TOTP: SHA-1, 6 digits, 30 seconds."
            if use_totp
            else f"HOTP: SHA-1, 6 digits, initial counter {otp.initial_count}.",
            f"Setup URI: {uri}",
            "KeePass: OTP Generator Settings > Import, paste the setup URI.",
            "KeePassXC: TOTP > Set up TOTP, paste the secret and use these settings."
            if use_totp
            else "KeePassXC does not support HOTP. After import, generate codes in KeePass only.",
            sep="\n",
        )

    def passcode_history(self, key_name):
        key = self.config["keys"][key_name]
        history = key.get("hotp_log", []) if isinstance(key, dict) else None
        if not isinstance(history, list) or not history:
            print("No Duo Mobile Passcode history." if isinstance(history, list) else "This key has invalid passcode history.")
            return
        while True:
            print(f"\nNewest 10 of {len(history)} saved Duo Mobile Passcodes:", *history[-10:], sep="\n")
            if not self.menu("History actions", "Delete older history (keep newest 10)"):
                return
            if len(history) <= 10:
                print("There is no older history to delete.")
                continue
            if not self.confirm(f"Delete {len(history) - 10} older entries?"):
                continue
            if self.save_changes(key, {"hotp_log": history[-10:]}, "Could not save the history change."):
                history = key["hotp_log"]
                print("Older passcode history deleted.")

    def set_key_password(self, name):
        key = self.config["keys"][name]
        if not isinstance(key, dict):
            print(INVALID_KEY)
            return
        password = self.password("Key password (blank to remove, Ctrl+C to cancel): ", confirm=True, min_length=0, allow_empty=True)
        if password is None:
            return
        updated = {field: value for field, value in key.items() if field != "password"}
        if password:
            updated["password"] = password
        if self.save_changes(self.config["keys"], {name: updated}, "Could not save the password change."):
            print("Password saved." if password else "Password removed.")

    def rename_key(self, name):
        keys = self.config["keys"]
        while (new_name := self.ask(f"New name for '{name}' (blank to cancel): ")) and new_name != name and new_name in keys:
            print("A key with that name already exists.")
        if not new_name or new_name == name:
            return
        renamed = {new_name if old_name == name else old_name: key for old_name, key in keys.items()}
        if self.save_changes(self.config, {"keys": renamed}, "Could not save the name change."):
            self.passcodes.pop(name, None)
            self.passcodes.pop(new_name, None)
            print(f"Key '{name}' renamed to '{new_name}'.")

    def toggle_passcode_visibility(self, name):
        key = self.config["keys"][name]
        if not isinstance(key, dict):
            print(INVALID_KEY)
            return
        hidden = not passcode_hidden(key)
        if self.save_changes(self.config["keys"], {name: dict(key, hide_passcode=hidden)}, "Could not save passcode visibility."):
            self.passcodes.pop(name, None)
            print(f"[{name}] Passcode {'hidden' if hidden else 'shown'}.")

    def delete_key(self, name):
        if not self.confirm(f"Delete '{name}' locally? This does not revoke it in Duo."):
            return
        if self.save_changes(self.config, {"keys": {n: key for n, key in self.config["keys"].items() if n != name}}, "Could not save the deletion."):
            print(f"Key '{name}' deleted.")

    def keys_menu(self):
        actions = [
            Choice("Duo Mobile Passcode history", value=self.passcode_history),
            Choice("Delete local key", value=self.delete_key),
            Choice("Rename key", value=self.rename_key),
            Choice("Export OTP secret", value=self.export_secret),
            Choice("Show/hide passcode", value=self.toggle_passcode_visibility),
            Choice("Set key password", value=self.set_key_password),
        ]
        while True:
            labels = [Choice("Add key", value=1)]
            for name, key in self.config["keys"].items():
                response = key.get("response") if isinstance(key, dict) else None
                organization = response.get("customer_name") if isinstance(response, dict) else None
                labels.append(Choice(name + (f" ({organization})" if organization else "") + (" [hidden]" if passcode_hidden(key) else ""), value=name))
            if (name := self.menu("Keys", *labels, default=1)) is None:
                return
            if name == 1:
                self.add_key()
                continue
            while name in self.config["keys"] and (action := self.menu(name, *actions, default=1)):
                action(name)

    def main_menu(self):
        while choice := self.menu("Main menu", "Passcode screen", "Keys", "Vault settings", back="Exit", default=1, back_value=1):
            if choice == 1:
                return True
            (self.keys_menu, self.vault_settings)[choice - 2]()

    def close(self):
        lock_file, self.lock_file = self.lock_file, None
        if lock_file:
            with suppress(OSError, ValueError, portalocker.exceptions.LockException):
                lock_file.release()
        self.wipe(self.encryption_key)
        self.salt = self.encryption_key = self.vault_digest = None
        self.config.clear()
        self.passcodes.clear()


def main(argv=None):
    parser = argparse.ArgumentParser(description="Show passcodes and listen for pushes. Select Main menu for settings.")
    options = parser.add_mutually_exclusive_group()
    options.add_argument("-k", dest="key", metavar="KEYNAME", help="print this key's OTP and exit")
    options.add_argument("-p", dest="password", metavar="KEYNAME", help="print this key's saved password and exit")
    args = parser.parse_args(argv)
    name = args.key if args.key is not None else args.password
    output = sys.stdout
    with closing(DuoAuthenticator()) as app, redirect_stdout(sys.stderr if name is not None else output):
        try:
            if not ((app.config_file or app.select_vault(create=name is None)) and app.load_config()):
                return 1
            if name is None:
                app.run_default()
                return 0
            if name not in app.config["keys"]:
                print(f"Unknown key: {name}")
                return 1
            if args.password is not None:
                key = app.config["keys"][name]
                value = key.get("password") if isinstance(key, dict) else None
                if not isinstance(value, str) or not value:
                    print(f"No password saved for key: {name}")
                    return 1
            else:
                kind, value = app.make_passcode(name)
                if not kind:
                    print(value)
                    return 1
                if kind == "TOTP":
                    value = value.at(datetime.fromtimestamp(time.time(), timezone.utc))
            print(value, file=output)
            return 0
        except (KeyboardInterrupt, EOFError):
            print("\nExited safely.")
            return 1


if __name__ == "__main__":
    raise SystemExit(main())
