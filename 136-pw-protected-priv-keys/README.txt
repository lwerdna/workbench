generate a password-protected private key:
	openssl genrsa -traditional -des3 -out example.pem 2048

used password "MyPassword"

these old legacy PKCS#1 files start with:

	-----BEGIN RSA PRIVATE KEY-----
	Proc-Type: 4,ENCRYPTED
	DEK-Info: DES-EDE3-CBC,CE4F4C616F0A8E0E

modern PKCS#8 start with:

	-----BEGIN ENCRYPTED PRIVATE KEY-----

internal structure:
	text PEM armor
	└── base64 text
	    └── encrypted DER bytes
	        └── ASN.1 DER RSAPrivateKey structure

dump its contents:
	openssl rsa -in rsa-3des.key -noout -text

outermost layer is explained in [1]
you will see the structure from [2]

peel off all but the innermost layer:
	./peel_pem.py example.pem -o plaintext.bin

examine it with:
	openssl pkey -inform DER -in plaintext.bin -noout -text
	openssl asn1parse -inform DER -in ./plaintext.bin -i

crack it:
	build john the ripper from [3]
	the apt installable one did not work

	generate the cracker target:
		./ssh2john.py example.pem > john_target

		has contents:
			example.pem:$sshng$0$8$CE4F4C616F0A8E0E$1200$fbc22022...403c1dcc

			decomposed:
				example.pem was input file
				sshng is variant id, which john uses to determin
				0 is cipher or key type
				8 is salt or iv length
				CE4F4C616F0A8E0E is salt or IV, directly from "DEK-Info:" line in PEM
				1200 is size of ciphertext (see ciphertext.bin, decoded base64 from PEM)
				fbc22022...403c1dcc is ciphertext (see ciphertext.bin)

		so basically it's just reformatted data from the PEM

	~/Downloads/john-bleeding-jumbo/run/john --wordlist=./wordlist.txt john_target
	~/Downloads/john-bleeding-jumbo/run/john --show john_target

	I think john has heuristics on that variant id "sshng" in its target file
	to determine if decryption was successful, looking perhaps that candidate
	plaintexts start with an ASN.1 SEQUENCE, or have sane block padding.

1. https://docs.openssl.org/1.0.2/man3/pem/#notes PEM ENCRYPTION FORMAT
2. RFC 8017, A.1.2. RSA Private Key Syntax
3. https://github.com/openwall/john
