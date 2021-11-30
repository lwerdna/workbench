## Binja Architecture Flags Part 3: Flag Roles

The previous articles said that flag roles were the textbook behavior of flags. If you can assign a flag to a role, there's a chance Binja will have that default behavior and you won't have to implement it yourself. For example, the carry flag is so common among architectures and its behavior is (to my knowledge) non-varying during addition, that we have it hardcoded into Binja:

```
   5 @ 0000021b  temp0.b = A
   6 @ 0000021b  temp1.b = [HL {arg3}].b
   7 @ 0000021b  A = A + [HL {arg3}].b
   8 @ 0000021b  flag:c = temp0.b + temp1.b u< temp0.b   <-- HERE
```

The `c` flag was declared to have CarryFlagRole so the `flag:c = ...` was produced by Binja and the architecture author is not responsible.

The hardcoded flag code is in the `get_flag_write_low_level_il()` method of the Architecture class and (at the time of this writing) supports:

|                      | ADD  | ADC  | SUB  | NEG  | FSUB | OTHERS |
| -------------------- | ---- | ---- | ---- | ---- | ---- | ------ |
| CarryFlagRole        | yes  | yes  | yes  | yes  | yes  |        |
| NegativeSignFlagRole | yes  | yes  | yes  | yes  | yes  | yes    |
| OrderedFlagRole      |      |      |      |      | yes  |        |
| OverflowFlagRole     | yes  |      | yes  |      |      |        |
| PositiveSignFlagRole | yes  | yes  | yes  | yes  | yes  | yes    |
| UnorderedFlagRole    |      |      |      |      | yes  |        |
| ZeroFlagRole         | yes  | yes  | yes  | yes  | yes  | yes    |

If a cell has "yes" it means that for the instruction at the column header, there's an built-in **attempt** at producing the flag in the row. It is not a guarantee that the flag semantics match your architecture's.

So for any instructions that are not ADD, ADC, SUB, NEG, or FSUB, you can try and see if Binja's built-in for calculating negative, positive, or zero flags are accurate for your architecture. If you want carry, ordered, overflow, or unordered, you will need to implement it yourself.

What happens when you mark an instruction the producer of a certain flag, but no implementation exists?

```
  12 @ 0000029e  A = sbb.b(temp1.b, D, flag:c)
  13 @ 0000029e  flag:s = sbb.b(temp1.b, D, flag:c) s< 0
  14 @ 0000029e  flag:pv = unimplemented
```

Here, `sbb` is an `s` producer and a `pv` producer.

Flag `s` is mapped to FlagRole.NegativeSignRole which is "yes" in the table, so Binja emits the default LLIL to set it.

Flag `pv` is mapped to FlagRole.OverflowFlagRole which is not "yes", so Binja doesn't have an implementation and emits LLIL_UNIMPLEMENTED.

If you need to define your own flag setting code, set the flag role to SpecialFlagRole and override `get_flag_write_low_level_il()`. There are two contraints you must work around:

* you do not have access to the operation result, which is tempting to use in negative and overflow calculation
* the operands given are not expressions, they're the registers or constants themselves

In C++ land, converting the operands to expressions has a helper function in LowLevelILFunction called `GetExprForRegisterOrConstantOperation()`. In Python land, you can use `expressionify()` from https://github.com/Vector35/Z80/blob/master/Z80IL.py

## Example: 6502

In 6502, the subtraction carry flag (borrow) is inverted from the textbook behavior, otherwise it's as expected:

```python
flag_roles = {
	"c": FlagRole.SpecialFlagRole,  # Not a normal carry flag, subtract result is inverted
	...
```

Then, later in `get_flag_write_low_level_il()` there is:

```python
def get_flag_write_low_level_il(self, op, size, write_type, flag, operands, il):
	if flag == 'c':
		if (op == LowLevelILOperation.LLIL_SUB) or (op == LowLevelILOperation.LLIL_SBB):
			# Subtraction carry flag is inverted from the commom implementation
			return il.not_expr(0, self.get_default_flag_write_low_level_il(op, size, FlagRole.CarryFlagRole, operands, il))
			# Other operations use a normal carry flag
			return self.get_default_flag_write_low_level_il(op, size, FlagRole.CarryFlagRole, operands, il)
	...			
```

This is nice and convenient: the normal behavior is simply wrapped in a `not`. See https://github.com/Vector35/binaryninja-api/blob/dev/python/examples/nes.py for the full code.