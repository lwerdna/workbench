client0.py, server0.py - anonymous client, server uses self-signed certificate

Generate keys and certificates with `make`.

On one terminal: `./server0.py`
On another: `./client_cert.py localhost 31337`

# References
1. https://github.com/tlsfuzzer/tlslite-ng/blob/master/tests/tlstest.py
