# Experiments with Kleene's recursion theorem

The recursion theorem shows that Turing machines (TM) are capable of accessing own description. This capability lets you prove other results about TM's. For example it leads to another contradiction when assuming a machine decides the halting language.

Prior to investing the idea of UTM's, TM's are not software, and aren't thought of as having "code". They're rigid state machines with access to tape memory. So "description" is being used here to mean one possibility in how to describe and store the states and transitions of TM's. This is an easy detail to overlook when programmers frequently access and modify the source code (description) of the machines they make in HLL's like C, python, or java.

## Self printing TM's

A nice intermediate step to the full statement and proof is to show the possibility of a TM that outputs its own description. Let makePrinter(x) be a utility function that returns a TM that outputs description(x). Then we can make the self printer in two parts A and B:

            A:                 B:
    +----------------+-------------------+
    | output of      | invoke            |
    | makePrinter(B) | makePrinter(tape) |
    +----------------+-------------------+

One would construct this machine by first writing B, which contains the implementation of makePrinter(), and the functionality to invoke it with the tape as input. Now run makePrinter(B) externally, to get A. Yes, makePrinter() is run on itself.

During execution, A prints B on the tape, and B accesses the tape to repeat the call makePrinter(B) as done in the construction, prepending this to output, resulting in AB.

## Full statement

The statement and proof of the recursion theorem is a constructive one that shows that the functionality can be added to any machine. See the wikipedia page or Sipser's book for the formal statement:

1. take any TM and add one parameter to its input, so T(x) now takes T(x,y)
2. a new machine R(a) can be constructed that "wraps" T, invoking T(x,description(R))

Any machine can be converted into a new machine that performs equivalently, but can access its own description. R is constructed as in the self printing TM, but B now contains T. Care is required to ensure that the original parameter x is not overwritten by A, and is not accessed by B when it called makePrinter.

            A:                 B:
    +----------------+---------------------+
    | output of      | invoke              |
    | makePrinter(B) | makePrinter(tape)   |
    |                | T(x,description(R)) |
    +----------------+---------------------+

## On computer viruses

I don't see the connection as Sipser and others do. Viruses are "cheating" because they only exist as their description, and they can invoke instructions that get at their code natively (eg: call/pop, pointers, memcpy(), etc.). In x86 assembly language, I'll argue that 99% of instructions deal with descriptions.

The original TM conception didn't have it existing as code, and has an extremely limited set of instructions and defined set of alphabet symbols to load and store on its tape. The idea that every TM can be transferred from the physical realm into an encoding, and that the TM's logic can consider itself in this encoding is exciting.

What if a TM's description on tape is not a mere copy, but a live functioning representation of the TM that is executing? Isn't our own brain modifying its own function when we learn, or store new memories? See [Godel Machine](https://en.wikipedia.org/wiki/G%C3%B6del_machine).


## On quines

A program that does nothing but prints its own description is called a quine. Consider this function:

    def ExecuteProgram(program):
       return exec(program).stdout

Then quines are fixed points, as ExecuteProgram(ExecuteProgram(...ExecuteProgram(quine)...)) returns quine.

## In Turing Machines

TODO: implement quinte in a TM

## In non-TM's

TM's have the convenience that the tape is the implied output; the memory and output are unified. In HLL's the program's memory (eg: setting a variable) is separate from its output (eg: printing on stdout).

## In Python

Python's built in repr() function is the makePrinter() we need. A variable "tape" is used to emulate the TM tape.

To make our python world construction match the TM world construction, start with examinging B.py. It uses the built in repr() as a convenient makePrinter(). A variable "tape" emulates the tape. An external implementation of makePrinter() is in makePrinter.py and is used to produce A:

```
./makePrinter.py B.py > A.py
```

And A and B together are the quine:

```
cat A.py B.py > quine.py
```

Run `python quine.py` for output.

# Must all quine's fit in the recursion theorem's framework?

Does Kleene's construction illustrate just one (of many) ways to make a quine? Or is it unique, required of all programs that access their code?

TODO: analyze some quines, identify Kleene's ideas


