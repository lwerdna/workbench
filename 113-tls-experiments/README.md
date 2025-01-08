Run some TLS experiments, view encrypted traffic with Wireshark [1].

![](./assets/diagram.svg)

`./v1.0/*` client and server, tls 1.0, client leaks key material for wireshark
`./v1.2/*` client and server, tls 2.0, client leaks key material for wireshark

1. https://en.wikipedia.org/wiki/Wireshark
2. https://pypi.org/project/tlslite-ng/