https://research.nccgroup.com/2021/01/29/software-verification-and-analysis-using-z3/

There are a couple changes in there, notably this error:

```
(assert (=  pn-hwin 
	     (bvlshr pn-win (_ bv2 64) )))
```

This needs to be `(_ bv1 64)` instead.

A few solutions (the values to the `DecodePacketNumber()` call that can return a value greater than $2^{62}-1$) are:

```C
DecodePacketNumber(0x3fffffffffffffff, 0x10018001, 32); // returns 0x4000000010018001
DecodePacketNumber(0x3fffffffffffffff, 0x8000, 16); // returns 0x4000000000008000
DecodePacketNumber(0x3fffffffffff8028, 0x7fff2052, 32); // 0x400000007fff2052
DecodePacketNumber(0x3fffffffffffc028, 0x2052, 16); // 0x4000000000002052
```

