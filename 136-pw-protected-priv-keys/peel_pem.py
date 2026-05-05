#!/usr/bin/env python3

# pip install cryptography

# ./peel_pem.py input.pem -o output.der
# openssl asn1parse -inform DER -in output.der -i

import argparse
import base64
import binascii
import getpass
import hashlib
import re
import sys
from pathlib import Path

from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes

SUPPORTED_CIPHERS = {
    # Legacy OpenSSL PEM name: (key length, IV length, cipher constructor)
    "DES-EDE3-CBC": (24, 8, algorithms.TripleDES),
    # A few common variants, included for convenience.
    "AES-128-CBC": (16, 16, algorithms.AES),
    "AES-192-CBC": (24, 16, algorithms.AES),
    "AES-256-CBC": (32, 16, algorithms.AES),
}

def parse_legacy_pem(pem_text: str) -> tuple[str, bytes, bytes]:
    """
    Parse a traditional OpenSSL encrypted PEM.

    Returns:
        cipher_name, iv, ciphertext

    This does not decrypt or parse ASN.1.
    """

    dek_match = re.search(
        r"^DEK-Info:\s*([^,\s]+),([0-9A-Fa-f]+)\s*$",
        pem_text,
        flags=re.MULTILINE,
    )
    if not dek_match:
        raise ValueError("No DEK-Info header found. This may not be legacy encrypted PEM.")

    cipher_name = dek_match.group(1)
    iv_hex = dek_match.group(2)

    if cipher_name not in SUPPORTED_CIPHERS:
        raise ValueError(
            f"Unsupported cipher {cipher_name!r}. "
            f"Supported: {', '.join(SUPPORTED_CIPHERS)}"
        )

    try:
        iv = binascii.unhexlify(iv_hex)
    except binascii.Error as exc:
        raise ValueError(f"Invalid IV/salt hex in DEK-Info: {iv_hex!r}") from exc

    _, expected_iv_len, _ = SUPPORTED_CIPHERS[cipher_name]
    if len(iv) != expected_iv_len:
        raise ValueError(
            f"Cipher {cipher_name} expects IV length {expected_iv_len}, "
            f"but DEK-Info provided {len(iv)} bytes."
        )

    b64_lines = []
    inside = False

    for line in pem_text.splitlines():
        line = line.strip()

        if line.startswith("-----BEGIN "):
            inside = True
            continue

        if line.startswith("-----END "):
            inside = False
            continue

        if not inside:
            continue

        if not line:
            continue

        if ":" in line:
            # PEM header line such as Proc-Type or DEK-Info.
            continue

        b64_lines.append(line)

    if not b64_lines:
        raise ValueError("No base64 payload found in PEM.")

    b64_blob = "".join(b64_lines)

    try:
        ciphertext = base64.b64decode(b64_blob, validate=True)
        fpath = 'ciphertext.bin'
        print(f'writing: {fpath}')
        with open(fpath, 'wb') as fp:
            fp.write(ciphertext)
    except binascii.Error as exc:
        raise ValueError("PEM payload is not valid base64.") from exc

    return cipher_name, iv, ciphertext

# https://docs.openssl.org/1.0.2/man3/EVP_BytesToKey/
def evp_bytes_to_key_md5(
    password: bytes,
    salt: bytes,
    key_len: int,
    iv_len: int,
) -> tuple[bytes, bytes]:
    """
    Reproduce OpenSSL's legacy EVP_BytesToKey derivation with:

        digest = MD5
        iteration count = 1

    For traditional encrypted PEM, OpenSSL historically uses the first
    8 bytes of the DEK-Info IV as the salt.

    Returns:
        key, iv_derived

    For this PEM format, the actual IV used for CBC is the IV from DEK-Info.
    The derived IV is returned for completeness but is not used below.
    """

    needed = key_len + iv_len
    output = b""
    previous = b""

    while len(output) < needed:
        previous = hashlib.md5(previous + password + salt).digest()
        output += previous

    key = output[:key_len]
    iv_derived = output[key_len : key_len + iv_len]

    return key, iv_derived


def remove_pkcs7_padding(data: bytes, block_size: int) -> bytes:
    """
    Remove PKCS#5/PKCS#7-style block padding.
    DES-EDE3-CBC has 8-byte blocks; AES-CBC has 16-byte blocks.
    """

    if not data:
        raise ValueError("Decrypted data is empty.")

    pad_len = data[-1]

    if pad_len < 1 or pad_len > block_size:
        raise ValueError(
            "Invalid padding. The passphrase may be wrong, "
            "or the file may not use standard PEM CBC padding."
        )

    if data[-pad_len:] != bytes([pad_len]) * pad_len:
        raise ValueError(
            "Invalid padding. The passphrase may be wrong, "
            "or the ciphertext may be corrupted."
        )

    return data[:-pad_len]


def decrypt_legacy_pem_to_der(
    pem_path: Path,
    passphrase: str,
) -> tuple[bytes, str]:
    pem_text = pem_path.read_text(encoding="ascii")

    cipher_name, iv, ciphertext = parse_legacy_pem(pem_text)

    key_len, iv_len, cipher_ctor = SUPPORTED_CIPHERS[cipher_name]

    # OpenSSL legacy PEM encryption uses the first 8 bytes of the IV as salt
    # for EVP_BytesToKey, even for AES where the IV is 16 bytes.
    salt = iv[:8]

    key, _derived_iv = evp_bytes_to_key_md5(
        password=passphrase.encode("utf-8"),
        salt=salt,
        key_len=key_len,
        iv_len=iv_len,
    )

    cipher = Cipher(cipher_ctor(key), modes.CBC(iv))
    decryptor = cipher.decryptor()

    padded_plaintext = decryptor.update(ciphertext) + decryptor.finalize()

    block_size = cipher_ctor.block_size // 8
    plaintext_der = remove_pkcs7_padding(padded_plaintext, block_size)

    return plaintext_der, cipher_name


def main() -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Peel a traditional OpenSSL encrypted PEM down to plaintext DER bytes, "
            "without parsing the DER."
        )
    )
    parser.add_argument("pem_file", type=Path, help="Input encrypted PEM file")
    parser.add_argument(
        "-o",
        "--out",
        type=Path,
        default=Path("plaintext.der"),
        help="Output file for plaintext DER bytes",
    )

    args = parser.parse_args()

    passphrase = getpass.getpass("PEM passphrase: ")

    try:
        plaintext_der, cipher_name = decrypt_legacy_pem_to_der(
            args.pem_file,
            passphrase,
        )
    except Exception as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1

    args.out.write_bytes(plaintext_der)

    print(f"Cipher: {cipher_name}")
    print(f"Wrote plaintext DER: {args.out}")
    print(f"Plaintext DER length: {len(plaintext_der)} bytes")

    # Optional sanity check only: ASN.1 DER SEQUENCE usually starts with 0x30.
    # This does not parse the DER.
    if plaintext_der.startswith(b"\x30"):
        print("Sanity check: DER begins with 0x30, likely ASN.1 SEQUENCE.")
    else:
        print("Warning: DER does not begin with 0x30.")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
