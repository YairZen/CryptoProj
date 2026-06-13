import os
import hashlib
import json
import base64

# ==============================================================================
# PART 1: CRYPTOGRAPHIC FUNCTIONS (According to project guidelines)
# ==============================================================================

def derive_key_scrypt(password: str, salt: bytes) -> bytes:
    """
    REPORT: "scrypt (Key Derivation)"
    According to the instructions, using built-in libraries for key generation is allowed.
    This function takes the user's password and salt, and generates a strong SECRET SYMMETRIC KEY.
    dklen=32 ensures the output is exactly 32 bytes (256 bits).
    """
    return hashlib.scrypt(password.encode('utf-8'), salt=salt, n=16384, r=8, p=1, dklen=32)

def pure_threefish_ctr_process(data: bytes, key: bytes, nonce: bytes) -> bytes:
    """
    REPORT: "Threefish in CTR Mode (Symmetric Encryption)"
    REPORT: "transforms the block cipher into a fast stream cipher"
    """

    C240 = 0x1BD11BDAA9FC1A22

    def ROTL64(x, y):
        return ((x << y) & 0xFFFFFFFFFFFFFFFF) | (x >> (64 - y))

    def bytes_to_words(b):
        return [int.from_bytes(b[i*8:(i+1)*8], 'little') for i in range(len(b)//8)]

    def words_to_bytes(w):
        return b''.join(x.to_bytes(8, 'little') for x in w)

    ROT = (
        (14, 16),
        (52, 57),
        (23, 40),
        (5, 37),
        (25, 33),
        (46, 12),
        (58, 22),
        (32, 32)
    )

    key_words = bytes_to_words(key)
    k_0, k_1, k_2, k_3 = key_words
    k_4 = k_0 ^ k_1 ^ k_2 ^ k_3 ^ C240
    K_ext = (k_0, k_1, k_2, k_3, k_4)

    t_0 = 0
    t_1 = 0
    t_2 = t_0 ^ t_1
    T_ext = (t_0, t_1, t_2)

    result = bytearray()
    counter = 0

    for i in range(0, len(data), 32):
        counter_bytes = counter.to_bytes(16, 'little')
        block_bytes = nonce + counter_bytes
        v_words = bytes_to_words(block_bytes)
        v_0, v_1, v_2, v_3 = v_words

        for d in range(72):
            if d % 4 == 0:
                s = d // 4
                sk_0 = K_ext.__getitem__(s % 5)
                sk_1 = (K_ext.__getitem__((s + 1) % 5) + T_ext.__getitem__(s % 3)) & 0xFFFFFFFFFFFFFFFF
                sk_2 = (K_ext.__getitem__((s + 2) % 5) + T_ext.__getitem__((s + 1) % 3)) & 0xFFFFFFFFFFFFFFFF
                sk_3 = (K_ext.__getitem__((s + 3) % 5) + s) & 0xFFFFFFFFFFFFFFFF

                v_0 = (v_0 + sk_0) & 0xFFFFFFFFFFFFFFFF
                v_1 = (v_1 + sk_1) & 0xFFFFFFFFFFFFFFFF
                v_2 = (v_2 + sk_2) & 0xFFFFFFFFFFFFFFFF
                v_3 = (v_3 + sk_3) & 0xFFFFFFFFFFFFFFFF

            rot_d = ROT.__getitem__(d % 8)
            r_0 = rot_d.__getitem__(0)
            r_1 = rot_d.__getitem__(1)

            y_0 = (v_0 + v_1) & 0xFFFFFFFFFFFFFFFF
            y_1 = ROTL64(v_1, r_0) ^ y_0

            y_2 = (v_2 + v_3) & 0xFFFFFFFFFFFFFFFF
            y_3 = ROTL64(v_3, r_1) ^ y_2

            v_0, v_1, v_2, v_3 = y_0, y_3, y_2, y_1

        s = 72 // 4
        sk_0 = K_ext.__getitem__(s % 5)
        sk_1 = (K_ext.__getitem__((s + 1) % 5) + T_ext.__getitem__(s % 3)) & 0xFFFFFFFFFFFFFFFF
        sk_2 = (K_ext.__getitem__((s + 2) % 5) + T_ext.__getitem__((s + 1) % 3)) & 0xFFFFFFFFFFFFFFFF
        sk_3 = (K_ext.__getitem__((s + 3) % 5) + s) & 0xFFFFFFFFFFFFFFFF

        v_0 = (v_0 + sk_0) & 0xFFFFFFFFFFFFFFFF
        v_1 = (v_1 + sk_1) & 0xFFFFFFFFFFFFFFFF
        v_2 = (v_2 + sk_2) & 0xFFFFFFFFFFFFFFFF
        v_3 = (v_3 + sk_3) & 0xFFFFFFFFFFFFFFFF

        keystream = words_to_bytes((v_0, v_1, v_2, v_3))
        chunk = data[i:i+32]

        for b_data, b_key in zip(chunk, keystream):
            result.append(b_data ^ b_key)

        counter += 1

    return bytes(result)

# ==============================================================================
# PURE PYTHON ED25519 MATH (From RFC 8032)
# ==============================================================================
_b = 256
_q = 2**255 - 19
_l = 2**252 + 27742317777372353535851937790883648493

def _inv(x): return pow(x, _q-2, _q)
_d = -121665 * _inv(121666) % _q
_I = pow(2, (_q-1)//4, _q)

def _xrecover(y):
    xx = (y*y-1) * _inv(_d*y*y+1)
    x = pow(xx, (_q+3)//8, _q)
    if (x*x - xx) % _q != 0: x = (x*_I) % _q
    if x % 2 != 0: x = _q-x
    return x

_By = 4 * _inv(5) % _q
_Bx = _xrecover(_By)
_B = [_Bx % _q, _By % _q]

def _edwards_add(P, Q):
    x1, y1 = P
    x2, y2 = Q
    x3 = (x1*y2 + x2*y1) * _inv(1 + _d*x1*x2*y1*y2) % _q
    y3 = (y1*y2 + x1*x2) * _inv(1 - _d*x1*x2*y1*y2) % _q
    return [x3, y3]

def _scalarmult(P, e):
    if e == 0: return (0, 1)
    Q = _scalarmult(P, e // 2)
    Q = _edwards_add(Q, Q)
    if e & 1: Q = _edwards_add(Q, P)
    return Q

def _encodeint(y):
    bits = [(y >> i) & 1 for i in range(_b)]
    return bytes([sum([bits[i * 8 + j] << j for j in range(8)]) for i in range(_b // 8)])

def _encodepoint(P):
    x, y = P
    bits = [(y >> i) & 1 for i in range(_b - 1)] + [x & 1]
    return bytes([sum([bits[i * 8 + j] << j for j in range(8)]) for i in range(_b // 8)])

def _bit(h, i): return (h[i//8] >> (i%8)) & 1

def _publickey(sk):
    h = hashlib.sha512(sk).digest()
    a = 2**(_b-2) + sum(2**i * _bit(h,i) for i in range(3, _b-2))
    A = _scalarmult(_B, a)
    return _encodepoint(A)

def _Hint(m):
    h = hashlib.sha512(m).digest()
    return sum(2**i * _bit(h,i) for i in range(2*_b))

def _signature(m, sk, pk):
    h = hashlib.sha512(sk).digest()
    a = 2**(_b-2) + sum(2**i * _bit(h,i) for i in range(3, _b-2))
    r = _Hint(bytes([h[i] for i in range(_b//8, _b//4)]) + m)
    R = _scalarmult(_B, r)
    S = (r + _Hint(_encodepoint(R) + pk + m) * a) % _l
    return _encodepoint(R) + _encodeint(S)

def _isoncurve(P):
    x, y = P
    return (-x*x + y*y - 1 - _d*x*x*y*y) % _q == 0

def _decodeint(s): return sum(2**i * _bit(s,i) for i in range(0, _b))

def _decodepoint(s):
    y = sum(2**i * _bit(s,i) for i in range(0, _b-1))
    x = _xrecover(y)
    if x & 1 != _bit(s, _b-1): x = _q-x
    P = [x, y]
    if not _isoncurve(P): raise Exception("Not on curve")
    return P

def _checkvalid(s, m, pk):
    if len(s) != _b//4: return False
    if len(pk) != _b//8: return False
    try:
        R = _decodepoint(s[:_b//8])
        A = _decodepoint(pk)
        S = _decodeint(s[_b//8:_b//4])
        h = _Hint(_encodepoint(R) + pk + m)
        return _encodepoint(_scalarmult(_B, S)) == _encodepoint(_edwards_add(R, _scalarmult(A, h)))
    except:
        return False

# ==============================================================================
# ed25519   Usage:
# ==============================================================================

def pure_ed25519_generate_keys():
    """
    REPORT: "generates an Ed25519 PRIVATE KEY (kept secret) and a PUBLIC KEY"
    """
    private_key = os.urandom(32)
    public_key = _publickey(private_key)
    return private_key, public_key

def pure_ed25519_sign(private_key: bytes, message: bytes) -> bytes:
    """
    REPORT: "Device A signs the encrypted vault using its PRIVATE KEY"
    """
    public_key = _publickey(private_key)
    return _signature(message, private_key, public_key)

def pure_ed25519_verify(public_key: bytes, message: bytes, signature: bytes) -> bool:
    """
    REPORT: "uses it to verify the digital signature"
    """
    return _checkvalid(signature, message, public_key)


# ==============================================================================
# PART 2: SYSTEM FLOW (Exactly matching the Report steps)
# ==============================================================================

def main():
    print("=====================================================")
    print("   Secure Password Vault Application (Topic 13)      ")
    print("=====================================================")

    # Original data and user password
    original_vault_data = b"Bank: 123456, Email: Pass!@#, Facebook: Sec99"
    user_master_password = "masterPassword123!"

    print(f"\n[INFO] Original Plaintext Vault: '{original_vault_data.decode('utf-8')}'")
    print(f"[INFO] User Master Password: '{user_master_password}'")

    # --------------------------------------------------------------------------
    # REPORT: Step 1 (Setup)
    # --------------------------------------------------------------------------
    print("\n--- Step 1: Setup (Device A) ---")

    # REPORT: "The system generates a random salt"
    salt = os.urandom(16)
    print(f"[*] Generated Salt (16 bytes / 128 bits) [Hex]:\n    {salt.hex()}")

    # REPORT: "derives a SECRET SYMMETRIC KEY using scrypt"
    secret_symmetric_key_A = derive_key_scrypt(user_master_password, salt)
    print(f"[*] Derived SECRET SYMMETRIC KEY (32 bytes / 256 bits) [Hex]:\n    {secret_symmetric_key_A.hex()}")

    # REPORT: "generates an Ed25519 PRIVATE KEY (kept secret) and a PUBLIC KEY"
    private_key_A, public_key_A = pure_ed25519_generate_keys()
    print(f"[*] Generated Ed25519 PRIVATE KEY (32 bytes / 256 bits) [Hex]:\n    {private_key_A.hex()}")
    print(f"[*] Generated Ed25519 PUBLIC KEY (32 bytes / 256 bits) [Hex]:\n    {public_key_A.hex()}")

    # --------------------------------------------------------------------------
    # REPORT: Step 2 (Encryption)
    # --------------------------------------------------------------------------
    print("\n--- Step 2: Encryption (Device A) ---")
    nonce = os.urandom(16) # Required for CTR mode
    print(f"[*] Generated Nonce for CTR Mode (16 bytes / 128 bits) [Hex]:\n    {nonce.hex()}")

    # REPORT: "The local password vault on Device A is encrypted using Threefish in CTR mode"
    encrypted_vault = pure_threefish_ctr_process(original_vault_data, secret_symmetric_key_A, nonce)
    print(f"[*] Encrypted Vault Ciphertext [Hex]:\n    {encrypted_vault.hex()}")

    # --------------------------------------------------------------------------
    # REPORT: Step 3 (Signing)
    # --------------------------------------------------------------------------
    print("\n--- Step 3: Signing (Device A) ---")

    # REPORT: "Device A signs the encrypted vault using its PRIVATE KEY, generating a digital signature"
    data_to_sign = nonce + encrypted_vault
    digital_signature = pure_ed25519_sign(private_key_A, data_to_sign)
    print(f"[*] Digital Signature (64 bytes / 512 bits) [Hex]:\n    {digital_signature.hex()}")

    # --------------------------------------------------------------------------
    # REPORT: Step 4 (Export)
    # --------------------------------------------------------------------------
    print("\n--- Step 4: Export (Device A -> Device B) ---")

    # REPORT: "explicitly contains four elements: 1) encrypted vault, 2) digital signature, 3) PUBLIC KEY, and 4) random salt"
    export_package = {
        "encrypted_vault": base64.b64encode(encrypted_vault).decode('utf-8'),
        "signature": base64.b64encode(digital_signature).decode('utf-8'),
        "public_key": base64.b64encode(public_key_A).decode('utf-8'),
        "salt": base64.b64encode(salt).decode('utf-8'),
        "nonce": base64.b64encode(nonce).decode('utf-8')
    }

    print("[*] Exporting the following JSON package to Device B:")
    print(json.dumps(export_package, indent=4))

    # ==========================================================================
    # --- TRANSITION TO DEVICE B ---
    # ==========================================================================

    # Receiving the package and unpacking the data
    package_json = json.dumps(export_package)
    received_pkg = json.loads(package_json)

    recv_enc_vault = base64.b64decode(received_pkg["encrypted_vault"])
    recv_signature = base64.b64decode(received_pkg["signature"])
    recv_pub_key   = base64.b64decode(received_pkg["public_key"])
    recv_salt      = base64.b64decode(received_pkg["salt"])
    recv_nonce     = base64.b64decode(received_pkg["nonce"])

    # --------------------------------------------------------------------------
    # REPORT: Step 5 (Verification)
    # --------------------------------------------------------------------------
    print("\n--- Step 5: Verification (Device B) ---")

    # REPORT: "extracts Device A's PUBLIC KEY from the package and uses it to verify the digital signature"
    recv_data_to_verify = recv_nonce + recv_enc_vault
    is_valid = pure_ed25519_verify(recv_pub_key, recv_data_to_verify, recv_signature)

    # REPORT: "If the signature is invalid, the system halts immediately to prevent attacks"
    if not is_valid:
        print("[!] CRITICAL ERROR: Digital signature is invalid! Halting system.")
        return

    print("[+] Signature verified successfully! File is authentic and unaltered.")

    # --------------------------------------------------------------------------
    # REPORT: Step 6 (Decryption)
    # --------------------------------------------------------------------------
    print("\n--- Step 6: Decryption (Device B) ---")

    # REPORT: "If the signature is valid, the user inputs their master password on Device B"
    print(f"[*] User inputs master password on Device B: '{user_master_password}'")

    # REPORT: "system uses the received salt and scrypt to reconstruct the exact same SECRET SYMMETRIC KEY"
    secret_symmetric_key_B = derive_key_scrypt(user_master_password, recv_salt)
    print(f"[*] Reconstructed SECRET SYMMETRIC KEY on Device B (32 bytes / 256 bits) [Hex]:\n    {secret_symmetric_key_B.hex()}")

    if secret_symmetric_key_A == secret_symmetric_key_B:
        print("[+] SUCCESS: The reconstructed key matches the original key perfectly!")

    # REPORT: "Finally, Device B decrypts the vault using Threefish in CTR mode"
    decrypted_vault = pure_threefish_ctr_process(recv_enc_vault, secret_symmetric_key_B, recv_nonce)

    print(f"\n[+] Vault decrypted successfully! \n[+] Original contents revealed: '{decrypted_vault.decode('utf-8')}'")


if __name__ == "__main__":
    main()