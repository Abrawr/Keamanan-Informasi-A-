"""Key Distribution Center: gives a fresh AES session key to two users, sealed with Vigenere.

Also holds the helpers shared with user.py (prompts, Vigenere, network framing).
Run:  python kdc.py
"""

import os
import secrets
import socket
import string
import threading

KEY_SIZES = (16, 24, 32)
KEY_ALPHABET = string.ascii_letters + string.digits
FIRST_CHAR, CHARSET_SIZE = 32, 95


# Protocol check error
class ProtocolError(Exception):
    pass


# Prompts

# Terminal output
def show(text=""):
    print(text, flush=True)


# Terminal input with default value
def ask(prompt, default=None):
    suffix = f" [{default}]" if default else ""
    value = input(f"{prompt}{suffix}: ").strip()
    return value or default or ""


# Key validation
def check_key(text, sizes=KEY_SIZES):
    if not text or not text.isascii() or not text.isprintable():
        raise ValueError("key must be non-empty printable ASCII")
    if sizes and len(text) not in sizes:
        raise ValueError(f"key must be {'/'.join(map(str, sizes))} characters, got {len(text)}")
    return text.encode()


# Key input
def ask_key(prompt, default=None, sizes=KEY_SIZES):
    while True:
        try:
            return check_key(ask(prompt, default), sizes)
        except ValueError as e:
            show(f"[!] {e}")


# User ID input
def ask_id(prompt, default=None, allow_empty=False):
    while True:
        user_id = ask(prompt, default).lower()
        if (allow_empty and not user_id) or (user_id.isascii() and user_id.isalnum()):
            return user_id
        show("[!] ID must be letters/digits only")


# Port input
def ask_port(prompt, default):
    while True:
        try:
            return int(ask(prompt, default))
        except ValueError:
            show("[!] Port must be a number")


# Vigenere over the 95 printable ASCII characters (space .. ~)

# Vigenere cipher (encrypt / decrypt)
def vigenere(text, key, direction=1):
    out = []
    for i, ch in enumerate(text):
        shift = ord(key[i % len(key)]) - FIRST_CHAR
        out.append(chr((ord(ch) - FIRST_CHAR + direction * shift) % CHARSET_SIZE + FIRST_CHAR))
    return "".join(out)


# Vigenere encryption to hex
def seal_vigenere(text, key):
    return f"vig:{vigenere(text, key.decode()).encode('ascii').hex()}"


# Session key generator
def random_key(length=16):
    return "".join(secrets.choice(KEY_ALPHABET) for _ in range(length))


# Network: one ASCII line per message, fields separated by "|"

# TCP server socket
def listen_socket(port, backlog=5):
    server = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    if os.name != "nt":
        server.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
    server.bind(("0.0.0.0", port))
    server.listen(backlog)
    return server


# Socket send
def send_line(sock, *fields):
    sock.sendall(("|".join(fields) + "\n").encode("ascii"))


# Socket receive
class LineReader:
    def __init__(self, sock):
        self.sock = sock
        self.buffer = b""

    def read(self):
        while b"\n" not in self.buffer:
            chunk = self.sock.recv(4096)
            if not chunk:
                return None
            self.buffer += chunk
        line, self.buffer = self.buffer.split(b"\n", 1)
        return line.decode("ascii").split("|")


# Key Distribution Center
class KDC:
    def __init__(self):
        self.keys = {}
        self.session_length = 16
        self.lock = threading.Lock()

    # Accept connections
    def serve(self, server):
        while True:
            conn, addr = server.accept()
            threading.Thread(target=self.handle, args=(conn, addr[0]), daemon=True).start()

    # Handle one request
    def handle(self, conn, ip):
        with conn:
            try:
                request = LineReader(conn).read()
                if not request:
                    return
                try:
                    reply = self.answer(request, ip)
                except ProtocolError as e:
                    show(f"[!] {ip}: {e}")
                    reply = ("ERR", str(e))
                send_line(conn, *reply)
            except (OSError, ValueError) as e:
                show(f"[!] {ip}: {e}")

    # Steps 1-2: request in, sealed session key out
    def answer(self, request, ip):
        if len(request) != 4 or request[0] != "REQ":
            raise ProtocolError("bad request")
        _, id_a, id_b, n1 = request
        show(f"\n(1) <- {ip}: REQ|{id_a}|{id_b}|{n1}")
        with self.lock:
            ka, kb = self.keys.get(id_a), self.keys.get(id_b)
            length = self.session_length
        unknown = [i for i, k in ((id_a, ka), (id_b, kb)) if k is None]
        if unknown:
            raise ProtocolError(f"unknown ID: {', '.join(unknown)}")

        ks = random_key(length)
        for_a = seal_vigenere(f"{ks}|{id_a}|{id_b}|{n1}", ka)
        ticket = seal_vigenere(f"{ks}|{id_a}", kb)
        show(f"    Ks = {ks}")
        show(f"(2) -> {ip}: KDC_REP|{for_a}|{ticket}")
        return "KDC_REP", for_a, ticket

    # Master key registration
    def register(self, user_id):
        key = ask_key(f"Vigenere master key for {user_id} (printable ASCII)", sizes=None)
        with self.lock:
            self.keys[user_id] = key


# KDC program
def run_kdc():
    port = ask_port("Listen port", "5000")
    kdc = KDC()
    show("Register master keys (leave ID empty to finish).")
    for default in ("alice", "bob"):
        kdc.register(ask_id("ID", default))
    while user_id := ask_id("ID", allow_empty=True):
        kdc.register(user_id)

    server = listen_socket(port)
    threading.Thread(target=kdc.serve, args=(server,), daemon=True).start()
    show(f"[*] KDC listening on port {port}")

    while True:
        choice = ask(f"\n[1] list keys  [2] add/change key  [3] remove ID  "
                     f"[4] session key length ({kdc.session_length})  [0] stop\nChoice")
        if choice == "1":
            with kdc.lock:
                for user_id, key in kdc.keys.items():
                    show(f"  {user_id:10} {key.decode()}")
        elif choice == "2":
            kdc.register(ask_id("ID"))
        elif choice == "3":
            with kdc.lock:
                removed = kdc.keys.pop(ask("ID").lower(), None)
            show("  removed" if removed else "  not found")
        elif choice == "4":
            length = ask("Length (16/24/32)", str(kdc.session_length))
            if length in ("16", "24", "32"):
                kdc.session_length = int(length)
        elif choice == "0":
            return


if __name__ == "__main__":
    try:
        show("=== KDC ===")
        run_kdc()
    except (KeyboardInterrupt, EOFError):
        show()
