client0.py, server0.py - anonymous client, server auths with self-signed certificate
client1.py, server1.py - client and server both auth with self-signed certificate

Generate keys and certificates with `make`.

On one terminal: `./server0.py`
On another: `./client0.py localhost 31337`

# References
1. https://github.com/tlsfuzzer/tlslite-ng/blob/master/tests/tlstest.py
