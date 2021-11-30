## Binja Architecture Flags Part 2: Flag Producer/Consumer

In the last installment, we informed Binja of our architecture's flags by defining a list of flag names, a mapping from flag names to `flag roles`, and groups of flags commonly set together called `flag write types`.

Let's remind ourselves briefly that these are terms within an imagined protocol between architecture author and Binja. The protocol's purpose is to communicate to Binja what flags are present and how they behave. As we accumulate architectures that stretch the protocol's limits (eg: PowerPC with its flag banks), it's possible the protocol gets adjusted to more generally accommodate architectures.

In Part 1, I said Binja tries to reduce the noise in displayed IL by showing only the flags between producer and consumer that are relevant. Consider this simplified flags definition for Z80:

```python
flags = ['c']
flag_roles = { 'c': FlagRole.CarryFlagRole }
flag_write_types = ['none', 'only_carry']
flags_written_by_flag_write_type = { 'none': [], 'only_carry': ['c'], }
```

We have one flag named 'c', we tell Binja that it's the textbook carry flag, and we define a flag group called "only_carry" which sets just this flag.

At lifting time, we mark certain IL instructions as a **producer** using the `flags` keyword. Remember to pass the _group_ or _flag write type_ that contains `c`, **not** `c` itself:

```python
il.add(size, lhs, rhs, flags='only_carry')
```

We mark certain IL instructions as a **consumer** by passing an LLIL flag expression as one of its operands:

```python
il.add_carry(size, lhs, rhs, il.flag("c"))
```

Instructions can be both producers and consumers. This applies to add-with-carry, which both consumes and produces a new `c`. I omitted `, flags='only_carry'` to maximize contrast.

#### Example A

Let's lift a simple C function:

```C
unsigned char add(unsigned char a, unsigned char b)
{
	return a + b;
}
```

Recap: the C function is named `add()` which will produce a Z80 instruction `ADD` (among others) which we lift to LLIL `ADD` that is a **producer** of the `c` flag.

Binja gives this LLIL, after compilation with [SDCC](http://sdcc.sourceforge.net):

```
_add:
   0 @ 0000020e  HL = 3
   1 @ 00000211  HL = HL + SP {arg2}
   2 @ 00000212  IY = 2
   3 @ 00000216  IY = IY + SP {arg1}
   4 @ 00000218  A = [IY {arg1}].b
   5 @ 0000021b  A = A + [HL {arg2}].b   <-- PRODUCER
   6 @ 0000021c  L = A
   7 @ 0000021d  <return> jump(pop)
```

WHERE'S THE CARRY!?

This is the lesson that was non-intuitive to me. Binja knows from the architecture-supplied _lifted IL_ that `ADD` sets `c`, but it doesn't produce any `c` setting _low level_ IL because it failed to detect anyone using `c`.

#### Example B

Let's change the function to use 2-byte integers:

```C
unsigned int add(unsigned int a, unsigned int b)
{
	return a + b;
}
```

Since the Z80 ALU only adds 8-bit ints, multi-byte adds are synthesized with an initial `ADD`, followed by runs of `ADC`. Here's the new IL:

```
_add:
   0 @ 0000020e  HL = 4
   1 @ 00000211  HL = HL + SP {arg3}
   2 @ 00000212  IY = 2
   3 @ 00000216  IY = IY + SP {arg1}
   4 @ 00000218  A = [IY {arg1}].b
   5 @ 0000021b  temp0.b = A
   6 @ 0000021b  temp1.b = [HL {arg3}].b
   7 @ 0000021b  A = A + [HL {arg3}].b                   <-- PRODUCER
   8 @ 0000021b  flag:c = temp0.b + temp1.b u< temp0.b   <--
   9 @ 0000021c  C = A
  10 @ 0000021d  A = [IY + 1 {arg2}].b
  11 @ 00000220  HL = HL + 1 {arg4}
  12 @ 00000221  A = adc.b(A, [HL {arg4}].b, flag:c)     <-- CONSUMER
  13 @ 00000222  B = A
  14 @ 00000223  L = C
  15 @ 00000224  H = B
  16 @ 00000225  <return> jump(pop)
```

With `ADC` present, Binja detects the relationship, and produces the IL `flag:c = temp0.b + temp1.b u< temp0.b`.

This also means that you can mark instructions as producers of a group of many flags, and LLIL will contain the flag calculating code for those flags consumed further along.

### Review

You, the architecture author:

* inform Binja of your architecture's flags by defining:
  * flag names
  * flag "roles" which are just their textbook behavior, if they qualify
  * flag "write types" which groups of flags often set together
* assign instructions as flag **producers** by passing `flag=` keyword parameter during lifting
* assign instructions as flag **consumers** by passing IL flag expressions as operands during lifting

With the defined variables and lifted IL, Binja decides when to generate flag-affecting low level IL.

