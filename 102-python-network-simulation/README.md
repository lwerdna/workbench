![](./diagram.svg)

This builds on Project 101.

Instead of just outputting the received packets on stdout (simplex) we can also write back, transmitting packets (duplex).

Now you can gain a deep understanding of networking devices by implementing them, leveraging the #AhaPowerOfProgramming. And since real programs (ping, nmap, etc.) on your host can interact with the virtual network through the [TAP interface](https://en.wikipedia.org/wiki/TUN/TAP), those programs working as expected are good indicators your implemented and understood the hardware correctly.
