"""Alice / Bob: gets a session key from the KDC, authenticates the peer, then chats with AES.

Contains the AES implementation (FIPS-197) and everything that decrypts.
Run:  python user.py
"""

import secrets
import socket
import string
import threading

from kdc import (LineReader, ProtocolError, ask, ask_id, ask_key, ask_port, check_key,
                 listen_socket, send_line, show, vigenere)

BLOCK = 16
MODES = ("ecb", "cbc")
HEX_DIGITS = set(string.hexdigits)
ERRORS = (ProtocolError, OSError, ValueError)


# AES block cipher (FIPS-197)

MIX = [[2, 3, 1, 1], [1, 2, 3, 1], [1, 1, 2, 3], [3, 1, 1, 2]]
INV_MIX = [[14, 11, 13, 9], [9, 14, 11, 13], [13, 9, 14, 11], [11, 13, 9, 14]]


# GF(2^8) multiply by 2
def xtime(a):
    a <<= 1
    return a ^ 0x11B if a & 0x100 else a


# GF(2^8) multiplication
def gmul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a = xtime(a)
        b >>= 1
    return result


# S-box and inverse S-box
def build_sbox():
    exp, log = [0] * 255, [0] * 256
    x = 1
    for i in range(255):
        exp[i] = x
        log[x] = i
        x ^= xtime(x)
    sbox = [0] * 256
    for a in range(256):
        b = exp[(255 - log[a]) % 255] if a else 0
        s = b
        for shift in range(1, 5):
            s ^= ((b << shift) | (b >> (8 - shift))) & 0xFF
        sbox[a] = s ^ 0x63
    inv = [0] * 256
    for i, s in enumerate(sbox):
        inv[s] = i
    return sbox, inv


SBOX, INV_SBOX = build_sbox()


# SubBytes
def sub_bytes(state, box=SBOX):
    return [box[b] for b in state]


# ShiftRows
def shift_rows(state):
    return [state[r + 4 * ((c + r) % 4)] for c in range(4) for r in range(4)]


# InvShiftRows
def inv_shift_rows(state):
    return [state[r + 4 * ((c - r) % 4)] for c in range(4) for r in range(4)]


# MixColumns / InvMixColumns
def mix_columns(state, matrix=MIX):
    out = []
    for c in range(4):
        column = state[4 * c:4 * c + 4]
        for row in matrix:
            value = 0
            for m, b in zip(row, column):
                value ^= gmul(b, m)
            out.append(value)
    return out


# AddRoundKey
def add_round_key(state, round_key):
    return [a ^ b for a, b in zip(state, round_key)]


# Key expansion
def expand_key(key):
    if len(key) not in (16, 24, 32):
        raise ValueError("AES key must be 16, 24 or 32 bytes")
    nk = len(key) // 4
    nr = nk + 6
    words = [list(key[4 * i:4 * i + 4]) for i in range(nk)]
    rcon = 1
    for i in range(nk, 4 * (nr + 1)):
        temp = list(words[i - 1])
        if i % nk == 0:
            temp = [SBOX[b] for b in temp[1:] + temp[:1]]
            temp[0] ^= rcon
            rcon = xtime(rcon)
        elif nk > 6 and i % nk == 4:
            temp = [SBOX[b] for b in temp]
        words.append([a ^ b for a, b in zip(words[i - nk], temp)])
    return [sum(words[4 * r:4 * r + 4], []) for r in range(nr + 1)]


# AES block encryption
def encrypt_block(block, round_keys, trace=None):
    step = trace or (lambda *args: None)
    nr = len(round_keys) - 1
    state = add_round_key(list(block), round_keys[0])
    step(0, "AddRoundKey", state)
    for rnd in range(1, nr + 1):
        state = sub_bytes(state)
        step(rnd, "SubBytes", state)
        state = shift_rows(state)
        step(rnd, "ShiftRows", state)
        if rnd < nr:
            state = mix_columns(state)
            step(rnd, "MixColumns", state)
        state = add_round_key(state, round_keys[rnd])
        step(rnd, "AddRoundKey", state)
    return bytes(state)


# AES block decryption
def decrypt_block(block, round_keys):
    nr = len(round_keys) - 1
    state = add_round_key(list(block), round_keys[nr])
    for rnd in range(nr - 1, -1, -1):
        state = inv_shift_rows(state)
        state = sub_bytes(state, INV_SBOX)
        state = add_round_key(state, round_keys[rnd])
        if rnd > 0:
            state = mix_columns(state, INV_MIX)
    return bytes(state)


# Padding and modes of operation

# PKCS#7 padding
def pad(data):
    n = BLOCK - len(data) % BLOCK
    return data + bytes([n]) * n


# PKCS#7 unpadding
def unpad(data):
    n = data[-1]
    if not 1 <= n <= BLOCK or data[-n:] != bytes([n]) * n:
        raise ValueError("invalid padding (wrong key?)")
    return data[:-n]


# XOR
def xor_bytes(a, b):
    return bytes(x ^ y for x, y in zip(a, b))


# Split into 16-byte blocks
def split_blocks(data):
    return [data[i:i + BLOCK] for i in range(0, len(data), BLOCK)]


# AES encryption (ECB / CBC)
def encrypt(plaintext, key, mode="ecb", iv=None):
    round_keys = expand_key(key)
    parts = split_blocks(pad(plaintext))
    if mode == "ecb":
        return b"".join(encrypt_block(b, round_keys) for b in parts)
    if mode == "cbc":
        previous = iv or secrets.token_bytes(BLOCK)
        out = [previous]
        for b in parts:
            previous = encrypt_block(xor_bytes(b, previous), round_keys)
            out.append(previous)
        return b"".join(out)
    raise ValueError(f"unknown mode: {mode}")


# AES decryption (ECB / CBC)
def decrypt(ciphertext, key, mode="ecb"):
    round_keys = expand_key(key)
    if not ciphertext or len(ciphertext) % BLOCK:
        raise ValueError("ciphertext length must be a multiple of 16 bytes")
    parts = split_blocks(ciphertext)
    if mode == "ecb":
        data = b"".join(decrypt_block(b, round_keys) for b in parts)
    elif mode == "cbc":
        if len(parts) < 2:
            raise ValueError("CBC ciphertext needs an IV and at least one block")
        data = b"".join(xor_bytes(decrypt_block(parts[i], round_keys), parts[i - 1])
                        for i in range(1, len(parts)))
    else:
        raise ValueError(f"unknown mode: {mode}")
    return unpad(data)


# Ciphertext tokens: "ecb:<hex>", "cbc:<hex>" (AES) and "vig:<hex>" (Vigenere, from the KDC)

# AES encryption to hex
def seal(text, key, mode):
    return f"{mode}:{encrypt(text.encode('ascii'), key, mode).hex()}"


# Decryption by token type (AES / Vigenere)
def decrypt_token(data, key, mode):
    if mode == "vig":
        return vigenere(data.decode("ascii"), key.decode(), -1).encode("ascii")
    return decrypt(data, key, mode)


# Hex token decryption
def unseal(token, key):
    mode, _, hex_data = token.partition(":")
    return decrypt_token(bytes.fromhex(hex_data), key, mode).decode("ascii")


# Ciphertext input parser (hex / Wireshark)
def parse_ciphertext(text):
    text = "".join(text.split())
    if text and set(text) <= HEX_DIGITS and len(text) % 2 == 0:
        try:
            decoded = bytes.fromhex(text).decode("ascii").strip()
            if ":" in decoded:
                text = decoded
        except ValueError:
            pass
    token = text.split("|")[-1]
    mode, sep, hex_data = token.rpartition(":")
    if not sep:
        return None, bytes.fromhex(token)
    return mode.lower(), bytes.fromhex(hex_data)


# Nonce generator
def new_nonce():
    return secrets.randbits(48)


# Prompts

# Address parser
def parse_addr(text, default_port):
    host, _, port = text.strip().rpartition(":")
    if not host:
        return text.strip(), default_port
    return host, int(port)


# Address input
def ask_addr(prompt, default, default_port):
    while True:
        try:
            return parse_addr(ask(prompt, default), default_port)
        except ValueError:
            show("[!] Use ip:port, for example 192.168.1.10:5000")


# Mode input
def ask_mode(default="ecb"):
    while True:
        mode = ask("Mode (ecb/cbc)", default).lower()
        if mode in MODES:
            return mode
        show("[!] Choose ecb or cbc")


# Alice / Bob

# User settings
class Node:
    def __init__(self, user_id, master_key, kdc_addr, port):
        self.id = user_id
        self.master_key = master_key
        self.kdc = kdc_addr
        self.port = port
        self.mode = "ecb"
        self.peer_id = "bob" if user_id == "alice" else "alice"
        self.peer_addr = "127.0.0.1:6000"


# Steps 1-2: ask the KDC for a session key
def request_session_key(node, peer_id):
    n1 = new_nonce()
    with socket.create_connection(node.kdc, timeout=10) as kdc:
        send_line(kdc, "REQ", node.id, peer_id, str(n1))
        show(f"(1) -> KDC: REQ|{node.id}|{peer_id}|{n1}")
        reply = LineReader(kdc).read()
    if not reply:
        raise ProtocolError("KDC closed the connection")
    if reply[0] == "ERR":
        raise ProtocolError(f"KDC refused: {reply[-1]}")
    _, for_me, ticket = reply
    show(f"(2) <- KDC: KDC_REP|{for_me}|{ticket}")
    try:
        ks, id_a, id_b, echoed_n1 = unseal(for_me, node.master_key).split("|")
        check_key(ks)
    except ValueError:
        raise ProtocolError("cannot open the KDC reply (wrong master key?)")
    if (id_a, id_b, echoed_n1) != (node.id, peer_id, str(n1)):
        raise ProtocolError("KDC reply does not match the request")
    show(f"    Ks = {ks}  (IDs and N1 match)")
    return ks.encode(), ticket


# Connection between Alice and Bob
class Session:
    def __init__(self, node, sock):
        self.node = node
        self.sock = sock
        self.reader = LineReader(sock)
        self.peer_id = None
        self.ks = None
        self.pending_ks = None
        self.challenge = None
        self.ready = threading.Event()
        self.closed = threading.Event()
        self.send_lock = threading.Lock()
        threading.Thread(target=self.listen, daemon=True).start()

    # Socket send
    def send(self, *fields):
        with self.send_lock:
            send_line(self.sock, *fields)

    # Step 3: send ticket
    def start_key_exchange(self, ks, ticket):
        self.pending_ks = ks
        self.send("TICKET", ticket)
        show(f"(3) -> {self.peer_id}: TICKET|{ticket}")

    # New session key
    def rekey(self):
        self.start_key_exchange(*request_session_key(self.node, self.peer_id))

    # Socket receive loop
    def listen(self):
        handlers = {"TICKET": self.on_ticket, "CHAL": self.on_challenge,
                    "RESP": self.on_response, "MSG": self.on_message, "ERR": self.on_error}
        try:
            while (fields := self.reader.read()) is not None:
                kind, *args = fields
                handler = handlers.get(kind)
                if handler:
                    handler(args[0] if args else "")
        except ProtocolError as e:
            show(f"[!] {e}")
            try:
                self.send("ERR", str(e))
            except OSError:
                pass
        except (OSError, ValueError):
            pass
        if not self.closed.is_set():
            show("[*] Connection closed. Press Enter to return to the menu.")
        self.close()

    # Step 3 in, step 4 out: challenge
    def on_ticket(self, ticket):
        show(f"(3) <- TICKET|{ticket}")
        try:
            ks, id_a = unseal(ticket, self.node.master_key).split("|")
            check_key(ks)
        except ValueError:
            raise ProtocolError("cannot open the ticket (wrong master key?)")
        if self.peer_id and id_a != self.peer_id:
            raise ProtocolError(f"ticket belongs to {id_a}, not {self.peer_id}")
        n2 = new_nonce()
        self.challenge = (ks.encode(), id_a, n2)
        token = seal(str(n2), ks.encode(), self.node.mode)
        self.send("CHAL", token)
        show(f"    Ks = {ks}, IDA = {id_a}")
        show(f"(4) -> {id_a}: CHAL|{token}  (N2 = {n2})")

    # Step 4 in, step 5 out: response
    def on_challenge(self, token):
        show(f"(4) <- CHAL|{token}")
        if self.pending_ks is None:
            raise ProtocolError("unexpected challenge")
        try:
            n2 = int(unseal(token, self.pending_ks))
        except ValueError:
            raise ProtocolError("cannot open the challenge")
        reply = seal(str(n2 + 1), self.pending_ks, self.node.mode)
        with self.send_lock:
            send_line(self.sock, "RESP", reply)
            self.ks, self.pending_ks = self.pending_ks, None
        show(f"(5) -> {self.peer_id}: RESP|{reply}  (N2 = {n2}, f(N2) = {n2 + 1})")
        show(f"[*] Session key active: {self.ks.decode()}")
        self.ready.set()

    # Step 5 check
    def on_response(self, token):
        show(f"(5) <- RESP|{token}")
        if self.challenge is None:
            raise ProtocolError("unexpected response")
        ks, id_a, n2 = self.challenge
        self.challenge = None
        try:
            answer = int(unseal(token, ks))
        except ValueError:
            answer = None
        if answer != n2 + 1:
            raise ProtocolError("wrong f(N2), peer does not hold Ks")
        self.ks, self.peer_id = ks, id_a
        show(f"[*] {id_a} authenticated (f(N2) = {answer}). Session key active: {ks.decode()}")
        self.ready.set()

    # Chat receive
    def on_message(self, token):
        if self.ks is None:
            raise ProtocolError("message received before key exchange")
        try:
            text = unseal(token, self.ks)
        except ValueError:
            text = "<cannot decrypt>"
        show(f"[recv] {token}")
        show(f"[{self.peer_id}] {text}")

    # Error from peer
    def on_error(self, reason):
        show(f"[!] Peer refused: {reason}")
        self.close()

    # Chat send
    def send_message(self, text):
        token = seal(text, self.ks, self.node.mode)
        self.send("MSG", token)
        show(f"[sent] {token}")

    # Close connection
    def close(self):
        if self.closed.is_set():
            return
        self.closed.set()
        self.ready.set()
        try:
            self.sock.shutdown(socket.SHUT_RDWR)
        except OSError:
            pass
        self.sock.close()


# TCP client: connect to peer
def connect(node):
    node.peer_id = ask_id("Peer ID", node.peer_id)
    node.peer_addr = ask("Peer address (ip:port)", node.peer_addr)
    peer_addr = parse_addr(node.peer_addr, 6000)
    ks, ticket = request_session_key(node, node.peer_id)
    sock = socket.create_connection(peer_addr, timeout=10)
    sock.settimeout(None)
    session = Session(node, sock)
    session.peer_id = node.peer_id
    session.start_key_exchange(ks, ticket)
    return session


# TCP server: wait for peer
def wait_for_peer(node):
    with listen_socket(node.port, backlog=1) as server:
        server.settimeout(1)
        show(f"[*] Waiting for a peer on port {node.port} ... (Ctrl+C to cancel)")
        while True:
            try:
                sock, addr = server.accept()
                break
            except socket.timeout:
                continue
    sock.settimeout(None)
    show(f"[*] Connection from {addr[0]}")
    return Session(node, sock)


# Chat session
def chat(session):
    try:
        if session.ready.wait(30) and not session.closed.is_set():
            chat_loop(session)
        else:
            show("[!] Key distribution did not finish.")
    finally:
        session.close()


# Chat input and commands
def chat_loop(session):
    node = session.node
    show("\nType a message and press Enter.  Commands: /rekey  /mode  /key  /quit")
    while not session.closed.is_set():
        line = input()
        if session.closed.is_set():
            break
        try:
            if line == "/quit":
                break
            elif line == "/key":
                show(f"    Ks = {session.ks.decode()}, mode = {node.mode}")
            elif line == "/rekey":
                session.rekey()
            elif line == "/mode":
                node.mode = ask_mode("cbc" if node.mode == "ecb" else "ecb")
            elif not line.isascii():
                show("[!] Plaintext must be ASCII")
            elif line:
                session.send_message(line)
        except ERRORS as e:
            show(f"[!] {e}")


# AES tool

FIPS_VECTORS = [
    ("AES-128", "000102030405060708090a0b0c0d0e0f",
     "00112233445566778899aabbccddeeff", "69c4e0d86a7b0430d8cdb78070b4c55a"),
    ("AES-192", "000102030405060708090a0b0c0d0e0f1011121314151617",
     "00112233445566778899aabbccddeeff", "dda97ca4864cdfe06eaf70a0ec0d7191"),
    ("AES-256", "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f",
     "00112233445566778899aabbccddeeff", "8ea2b7ca516745bfeafc49904b496089"),
    ("AES-128", "2b7e151628aed2a6abf7158809cf4f3c",
     "3243f6a8885a308d313198a2e0370734", "3925841d02dc09fbdc118597196a0b32"),
]


# Plaintext input
def ask_plaintext():
    while True:
        text = input("Plaintext: ")
        if text.isascii():
            return text.encode()
        show("[!] Plaintext must be ASCII")


# Tool: encrypt
def tool_encrypt(state):
    key = ask_key("Key", state.get("key"))
    state["key"] = key.decode()
    mode = state["mode"] = ask_mode(state.get("mode", "ecb"))
    data = encrypt(ask_plaintext(), key, mode)
    if mode == "cbc":
        show(f"IV         : {data[:16].hex()}")
        show(f"Ciphertext : {data[16:].hex()}")
    else:
        show(f"Ciphertext : {data.hex()}")
    show(f"Token      : {mode}:{data.hex()}")


# Tool: decrypt
def tool_decrypt(state):
    key = ask_key("Key (master key for vig: tokens)", state.get("key"), sizes=None)
    state["key"] = key.decode()
    mode, data = parse_ciphertext(input("Ciphertext (hex, mode:hex, or a line from Wireshark): "))
    if mode is None:
        mode = ask_mode(state.get("mode", "ecb"))
    plaintext = decrypt_token(data, key, mode)
    show(f"Plaintext  : {plaintext.decode('ascii', errors='replace')}")


# Tool: round-by-round trace
def tool_trace(state):
    key = ask_key("Key", state.get("key"))
    state["key"] = key.decode()
    block = pad(ask_plaintext())[:BLOCK]
    round_keys = expand_key(key)
    show(f"\nInput block : {block.hex()}")
    for i, rk in enumerate(round_keys):
        show(f"Round key {i:2}: {bytes(rk).hex()}")
    show()

    def trace(rnd, step, s):
        show(f"Round {rnd:2}  {step:12} {bytes(s).hex()}")

    show(f"\nCiphertext  : {encrypt_block(block, round_keys, trace).hex()}")


# Tool: FIPS-197 test vectors
def tool_selftest(_state):
    for name, key, plain, expected in FIPS_VECTORS:
        round_keys = expand_key(bytes.fromhex(key))
        cipher = encrypt_block(bytes.fromhex(plain), round_keys).hex()
        back = decrypt_block(bytes.fromhex(cipher), round_keys).hex()
        ok = cipher == expected and back == plain
        show(f"{name}  {cipher}  {'PASS' if ok else 'FAIL'}")


# AES tool menu
def run_tool():
    actions = {"1": tool_encrypt, "2": tool_decrypt, "3": tool_trace, "4": tool_selftest}
    state = {}
    while True:
        choice = ask("\n[1] encrypt  [2] decrypt  [3] trace one block  [4] test vectors  [0] exit\nChoice", "1")
        if choice == "0":
            return
        if choice in actions:
            try:
                actions[choice](state)
            except ValueError as e:
                show(f"[!] {e}")


# User program
def main():
    show("=== User (Alice / Bob) ===")
    user_id = ask_id("Your ID", "alice")
    master_key = ask_key("Your Vigenere master key (shared with the KDC)", sizes=None)
    kdc_addr = ask_addr("KDC address (ip:port)", "127.0.0.1:5000", 5000)
    port = ask_port("Listen port", "6000")
    node = Node(user_id, master_key, kdc_addr, port)

    while True:
        choice = ask(f"\n[1] connect to peer  [2] wait for peer  [3] change master key  "
                     f"[4] mode ({node.mode})  [5] AES tool  [0] exit\nChoice", "1")
        try:
            if choice == "1":
                chat(connect(node))
            elif choice == "2":
                chat(wait_for_peer(node))
            elif choice == "3":
                node.master_key = ask_key("New Vigenere master key", sizes=None)
            elif choice == "4":
                node.mode = ask_mode(node.mode)
            elif choice == "5":
                run_tool()
            elif choice == "0":
                return
        except ERRORS as e:
            show(f"[!] {e}")
        except KeyboardInterrupt:
            show("\n[*] Cancelled")


if __name__ == "__main__":
    try:
        main()
    except (KeyboardInterrupt, EOFError):
        show()
