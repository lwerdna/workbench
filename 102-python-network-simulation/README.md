![](./diagram.svg)

```
This builds on ../0002...
Instead of just outputting the received packets on stdout (simplex) we can also write back, transmitting packets (duplex).
We make some virtual hosts that can respond to ARP and PING.

Quick start:
$ sudo ip tuntap add dev tap0 mode tap
$ make
$ ./vrouter.py

We now have:
	Alice on 192.168.123.10
	  Bob on 192.168.123.11
  Charlie on 192.168.123.12	

In another terminal, ping Alice
$ sudo ip addr add 192.168.123.1/24 dev tap0
$ sudo ip link set tap0 up
$ ping 192.168.123.10
```
