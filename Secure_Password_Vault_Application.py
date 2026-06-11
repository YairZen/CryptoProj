import os
import hashlib
import json
import struct

# =====================================================================
# PART 1: Key Derivation Function (scrypt)
# According to the instructions, using external libraries for
# Key Generation and Hash Functions is explicitly allowed.
# =====================================================================

def derive_key(master_password: str, salt: bytes) -> bytes:
    """
    Step 1: Convert the user's master password into a strong cryptographic key.
    We use the 'scrypt' algorithm because it is designed to be slow and
    memory-intensive, making brute-force attacks very difficult.
    """
    key = hashlib.scrypt(
        master_password.encode('utf-8'),
        salt=salt,
        n=16384, # CPU/Memory cost factor
        r=8,     # Block size
        p=1,     # Parallelization factor
        dklen=64 # Desired Key Length (64 bytes = 512 bits)
    )
    return key

# =====================================================================
# PART 2: Symmetric Encryption - Pure Python Threefish-512 & CTR Mode
# No external cryptographic libraries are used here.
# =====================================================================

def threefish_mix(x, y, rotation):
    """
    The MIX function is the core of the Threefish algorithm.
    It uses an ARX structure: Addition, Rotation, and XOR.
    """
    mask = 0xFFFFFFFFFFFFFFFF # Ensure 64-bit bounds

    # Step 1: Addition (x + y)
    x = (x + y) & mask

    # Step 2: Rotation (bitwise circular shift of y)
    y = ((y << rotation) | (y >> (64 - rotation))) & mask

    # Step 3: XOR (x XOR y)
    y = x ^ y

    return x, y

def threefish_encrypt_block(key: bytes, tweak: bytes, plaintext_block: bytes) -> bytes:
    """
    Encrypts a single 64-byte (512-bit) block using the Threefish algorithm.
    This is a pure-Python implementation of the ARX structure.
    """
    # Convert the 64-byte blocks into 8 separate 64-bit integers
    v = list(struct.unpack('<8Q', plaintext_block))
    k = list(struct.unpack('<8Q', key))
    t = list(struct.unpack('<2Q', tweak))

    # Generate extra key and tweak words (required by the algorithm structure)
    k_parity = 0x1BD11BDAA9FC1A22
    for i in range(8):
        k_parity ^= k[ i ]
    k.append(k_parity)
    t.append(t[ 0 ] ^ t[ 1 ])

    # Proper rotation constants for Threefish-512 (with spaces to prevent deletion)
    rotations = [
        [ 46, 36, 19, 37 ],
        [ 33, 27, 14, 42 ],
        [ 17, 49, 36, 39 ],
        [ 44,  9, 54, 56 ],
        [ 39, 30, 34, 24 ],
        [ 13, 50, 10, 17 ],
        [ 25, 29, 39, 43 ],
        [  8, 35, 56, 22 ]
    ]

    # Perform 72 rounds of mixing and permuting
    for d in range(72):
        # Inject subkeys every 4 rounds to add complexity
        if d % 4 == 0:
            s = d // 4
            for i in range(8):
                subkey = k[ (s + i) % 9 ]
                if i == 5:
                    subkey += t[ s % 3 ]
                elif i == 6:
                    subkey += t[ (s + 1) % 3 ]
                elif i == 7:
                    subkey += s # Add the round counter
                v[ i ] = (v[ i ] + subkey) & 0xFFFFFFFFFFFFFFFF

        # Get rotation values for the current round
        r = rotations[ d % 8 ]

        # Apply the MIX function to pairs of integers
        v[ 0 ], v[ 1 ] = threefish_mix(v[ 0 ], v[ 1 ], r[ 0 ])
        v[ 2 ], v[ 3 ] = threefish_mix(v[ 2 ], v[ 3 ], r[ 1 ])
        v[ 4 ], v[ 5 ] = threefish_mix(v[ 4 ], v[ 5 ], r[ 2 ])
        v[ 6 ], v[ 7 ] = threefish_mix(v[ 6 ], v[ 7 ], r[ 3 ])

        # Simple Permutation (shuffle the order for the next round)
        v = [ v[ 2 ], v[ 1 ], v[ 4 ], v[ 7 ], v[ 6 ], v[ 5 ], v[ 0 ], v[ 3 ] ]

    # Final subkey addition after all 72 rounds
    s = 18 # 72 // 4
    for i in range(8):
        subkey = k[ (s + i) % 9 ]
        if i == 5:
            subkey += t[ s % 3 ]
        elif i == 6:
            subkey += t[ (s + 1) % 3 ]
        elif i == 7:
            subkey += s
        v[ i ] = (v[ i ] + subkey) & 0xFFFFFFFFFFFFFFFF

    # Pack the 8 integers back into a single 64-byte ciphertext block
    return struct.pack('<8Q', *v)

def encrypt_ctr(key: bytes, plaintext: bytes) -> bytes:
    """
    Encrypts variable-length data using Threefish in Counter (CTR) mode.
    Why CTR? It turns a block cipher into a stream cipher.
    """
    nonce = os.urandom(16)
    tweak = b'\x00' * 16
    ciphertext = bytearray()
    block_size = 64

    for i in range(0, len(plaintext), block_size):
        counter_bytes = struct.pack('<Q', i // block_size)
        counter_block = nonce + counter_bytes + (b'\x00' * (block_size - len(nonce) - len(counter_bytes)))

        keystream = threefish_encrypt_block(key, tweak, counter_block)

        chunk = plaintext[i:i+block_size]
        encrypted_chunk = bytes(a ^ b for a, b in zip(chunk, keystream[:len(chunk)]))
        ciphertext.extend(encrypted_chunk)

    return nonce + ciphertext

def decrypt_ctr(key: bytes, ciphertext: bytes) -> bytes:
    """
    Decrypts data using Threefish in Counter (CTR) mode.
    In CTR mode, decryption is mathematically identical to encryption.
    """
    nonce = ciphertext[:16]
    actual_ciphertext = ciphertext[16:]
    plaintext = bytearray()
    tweak = b'\x00' * 16
    block_size = 64

    for i in range(0, len(actual_ciphertext), block_size):
        counter_bytes = struct.pack('<Q', i // block_size)
        counter_block = nonce + counter_bytes + (b'\x00' * (block_size - len(nonce) - len(counter_bytes)))

        keystream = threefish_encrypt_block(key, tweak, counter_block)

        chunk = actual_ciphertext[i:i+block_size]
        decrypted_chunk = bytes(a ^ b for a, b in zip(chunk, keystream[:len(chunk)]))
        plaintext.extend(decrypted_chunk)

    return bytes(plaintext)

# =====================================================================
# PART 3: Pure Python Ed25519 (Digital Signature)
# No external cryptographic libraries used. Math is based on Edwards curve.
# =====================================================================

# Constant curve parameters for Ed25519
Q = 2**255 - 19
L = 2**252 + 27742317777372353535851937790883648493

def inv(x):
    """Calculates the modular inverse."""
    return pow(x, Q - 2, Q)

d = -121665 * inv(121666) % Q
I = pow(2, (Q - 1) // 4, Q)

def xrecover(y):
    """Recovers the X coordinate given the Y coordinate on the curve."""
    xx = (y*y - 1) * inv(d*y*y + 1)
    x = pow(xx, (Q + 3) // 8, Q)
    if (x*x - xx) % Q != 0: x = (x * I) % Q
    if x % 2 != 0: x = Q - x
    return x

# Base point (Generator) of the Ed25519 curve
By = 4 * inv(5)
Bx = xrecover(By)
B = (Bx % Q, By % Q)

def edwards_add(P, Q_point):
    """Adds two points on the Edwards curve."""
    x1, y1 = P
    x2, y2 = Q_point
    x3 = (x1*y2 + x2*y1) * inv(1 + d*x1*x2*y1*y2)
    y3 = (y1*y2 + x1*x2) * inv(1 - d*x1*x2*y1*y2)
    return (x3 % Q, y3 % Q)

def edwards_scalarmult(P, e):
    """Multiplies a point P by a scalar e on the curve."""
    if e == 0: return (0, 1)
    Q_point = edwards_scalarmult(P, e // 2)
    Q_point = edwards_add(Q_point, Q_point)
    if e & 1: Q_point = edwards_add(Q_point, P)
    return Q_point

def encodeint(y):
    bits = [(y >> i) & 1 for i in range(256)]
    return bytes(sum([bits[i * 8 + j] << j for j in range(8)]) for i in range(32))

def encodepoint(P):
    x, y = P
    bits = [(y >> i) & 1 for i in range(255)] + [x & 1]
    return bytes(sum([bits[i * 8 + j] << j for j in range(8)]) for i in range(32))

def decodeint(s):
    return sum(s[i] << (8 * i) for i in range(32))

def decodepoint(s):
    y = sum((s[i] & 0xFF) << (8 * i) for i in range(32))
    x_is_odd = (y >> 255) & 1
    y &= (1 << 255) - 1
    x = xrecover(y)
    if x & 1 != x_is_odd: x = Q - x
    return (x, y)

def Hint(m):
    """Generates a SHA512 hash and converts it to an integer."""
    h = hashlib.sha512(m).digest()
    return sum(h[i] << (8 * i) for i in range(64))

def ed25519_generate_keys():
    """Generates a private and public key pair for digital signatures."""
    secret = os.urandom(32)
    h = hashlib.sha512(secret).digest()
    a = 2**(254) + sum(h[i] << (8 * i) for i in range(3, 32))
    A = edwards_scalarmult(B, a)
    public_key = encodepoint(A)
    return secret, public_key

def ed25519_sign(private_key: bytes, message: bytes) -> bytes:
    """Signs a message to prove authenticity and integrity."""
    h = hashlib.sha512(private_key).digest()
    a = 2**(254) + sum(h[i] << (8 * i) for i in range(3, 32))
    r = Hint(h[32:] + message)
    R = edwards_scalarmult(B, r)
    A = edwards_scalarmult(B, a)
    S = (r + Hint(encodepoint(R) + encodepoint(A) + message) * a) % L
    return encodepoint(R) + encodeint(S)

def ed25519_verify(public_key: bytes, message: bytes, signature: bytes) -> bool:
    """Verifies the signature of a message."""
    if len(signature) != 64:
        return False
    R = decodepoint(signature[:32])
    A = decodepoint(public_key)
    S = decodeint(signature[32:])
    h = Hint(signature[:32] + public_key + message)

    SB = edwards_scalarmult(B, S)
    hA = edwards_scalarmult(A, h)
    RhA = edwards_add(R, hA)

    return SB == RhA

# =====================================================================
# PART 4: Secure Password Vault Application (Main Local Flow)
# =====================================================================

def main():
    print("===================================================")
    print("       SECURE PASSWORD VAULT APPLICATION")
    print("===================================================\n")

    # ---------------------------------------------------------
    # Step 1: Alice sets up the vault locally
    # ---------------------------------------------------------
    print(" ALICE'S ENVIRONMENT:")
    alice_master_password = "MyStrongPassword123!"
    salt = os.urandom(16)

    print("    -> Deriving 512-bit symmetric key using scrypt...")
    alice_symmetric_key = derive_key(alice_master_password, salt)

    print("    -> Generating Ed25519 Public/Private key pair for signatures...")
    alice_priv_key, alice_pub_key = ed25519_generate_keys()

    vault_data = {
        "email": "alice_mail_pass_88",
        "facebook": "alice_fb_pass_99",
        "bank_account": "alice_bank_secret_$$$"
    }
    vault_bytes = json.dumps(vault_data).encode('utf-8')
    print("    -> Vault populated with 3 credentials.")

    # ---------------------------------------------------------
    # Step 2: Alice encrypts and signs the vault for export
    # ---------------------------------------------------------
    print("\n EXPORTING THE VAULT (ENCRYPTION & SIGNING):")

    print("    -> Encrypting vault data using Threefish in CTR Mode...")
    encrypted_vault = encrypt_ctr(alice_symmetric_key, vault_bytes)

    print("    -> Signing the encrypted file using Ed25519 Private Key...")
    signature = ed25519_sign(alice_priv_key, encrypted_vault)

    # ---------------------------------------------------------
    # Step 3: Bob receives and verifies the vault
    # ---------------------------------------------------------
    print("\n BOB'S ENVIRONMENT (RECEIVING DATA):")
    print("    -> Bob received the encrypted vault, the salt, and the signature.")

    print("    -> Verifying Alice's signature using her Public Key...")
    is_authentic = ed25519_verify(alice_pub_key, encrypted_vault, signature)

    if not is_authentic:
        print("    [!] ALERT: Signature verification failed. Data might be corrupted or forged!")
        return

    print("    [+] Signature Verified! Data is authentic and intact.")

    # ---------------------------------------------------------
    # Step 4: Bob decrypts the vault
    # ---------------------------------------------------------
    print("\n DECRYPTING THE VAULT:")
    print("    -> Bob derives the symmetric key using the shared Master Password...")
    bob_symmetric_key = derive_key("MyStrongPassword123!", salt)

    print("    -> Decrypting vault data using Threefish in CTR Mode...")
    decrypted_vault_bytes = decrypt_ctr(bob_symmetric_key, encrypted_vault)

    decrypted_vault_data = json.loads(decrypted_vault_bytes.decode('utf-8'))

    print("\n===================================================")
    print("[+] SUCCESS! RECOVERED PASSWORDS:")
    for service, pwd in decrypted_vault_data.items():
        print(f"    - {service.capitalize()}: {pwd}")
    print("===================================================")

if __name__ == "__main__":
    main()