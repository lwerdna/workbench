A practical worked example of an expression parser, trying minimize the use of formal definitions like first and follow sets.

# Stage 1

I want to be able to parse expressions with the normal arithmetic operators +, -, *, /. The multiply and divide should have higher precedence than addition and subtraction, but parenthesis should be able to override this. 

Since Precedence is lowest near the start symbol, and highest near the depths of production rules, we start with add and subtract. An expression can be the addition or subtraction of addends:

    E -> A '+' A
      -> A '-' A

Addends can be the product or quotient of factors:

    A -> F '*' F
      -> F '/' F

The factors can be numbers, or a parenthesized subexpression:

    F -> '(' E ')'
      -> NUMLIT

# Stage 2

The grammar made perfect sense in Stage 1 when we wrote it, simply mirroring our speech as we described it. But it is easy to miss some details, and often those details can be found by subjecting the grammar to some examples. One problematic example is `5*5` which reveals that our production rules *require* an addition sign or subtraction sign.

We make the operators optional by adding rules that allow "fall through" to the next rules.

    E -> A '+' A
      -> A '-' A
      -> A

    A -> F '*' F
      -> F '/' F
      -> F

    F -> '(' E ')'
      -> NUMLIT

# Stage 3

When the parser encounters the first symbol of the input, how will it know which of E's three production rules to use? In its current form, all three start with A, so it may be possible to defer the decision, descend down A's path, and make a decision after A returns by examining the next input symbol.

But a true LL(1) parser should know which production to immediately after looking at the next input symbol, and in its current form, this is not possible.

A single language can be described by many grammars. This language happens to be LL(1), which means at least one grammar in LL(1) form exists to generate it. Indeed, we will arrive at one by applying small fixes to this one. The general problem of deciding whether a given non-LL(1) grammar has an LL(1) form (thus deciding of the language generated is LL(1)) gets into CS difficulty.

We rearrange and augment E's production rules so that the rule can be chosen after looking only at the next input symbol. Every rule starts with A, so we "factor" it out, and create a new nonterminal for the remaining `'+' A`, '`-' A` and `<empty>`:

    E  -> A E_

    E_ -> '+' A
       -> '-' A
       -> <empty>
       
The action of the parser *still* defers the decision until after A is finished, but by splitting E into this two-rule form, the parser's needs only the next input symbol to decide the next rule to use

Similar factoring is required for the remainder of the grammar:

    A  -> F A_
    
    A_ -> '*' F
       -> '/' F
       -> <empty>

    F -> '(' E ')'
      -> NUMLIT

# Example - Pushdown Automata (PDA)

Number the rules to make referring to them more compact:

    E  -> A E_        (1)

    E_ -> '+' A       (2)
       -> '-' A       (3)
       -> <empty>     (4)
       
    A  -> F A_        (5)
    
    A_ -> '*' F       (6)
       -> '/' F       (7)
       -> <empty>     (8)

    F -> '(' E ')'    (9)
      -> NUMLIT       (10)

The stack is initialized with the start nonterminal E. When the top of the stack and the input character are terminals, the PDA checks that they match, and consumes both when they do (parse error otherwise). But when the stack contains a nontermainl, a lookup table decides which production rule to use:

|    | '+' | '-' | '*' | '/' | '(' | ')' | NUMLIT |
|----|-----|-----|-----|-----|-----|-----|--------|
| E  |  1  |  1  |  1  |  1  |  1  |  1  |   1    |
| E_ |  2  |  3  |  4  |  4  |  4  |  4  |   4    |
| A  |  5  |  5  |  5  |  5  |  5  |  5  |   5    |  
| A_ |  8  |  8  |  6  |  7  |  8  |  8  |   8    |
| F  | err | err | err | err |  9  | err |   10   |

An example parse of the expression `(6+4)*8` which has tokens `'(', NUMLIT, '+', NUMLIT, ')', '*', NUMLIT` follows. The leftmost character of the string representing the stack is the top.

| step | stack                  | input       | lookup            |
|------|------------------------|-------------|-------------------|
|1     | E                      | (6+4)*8$    | 1: E -> A E_      |
|2     | A E_                   | (6+4)*8$    | 5: A -> F A_      |
|3     | F A_ E_                | (6+4)*8$    | 9: F -> '(' E ')' |
|4     | '(' E ')' A_ E_        | (6+4)*8$    | match             |
|5     | E ')' A_ E_            | 6+4)*8$     | 1: E -> A E_      |
|6     | A E_ ')' A_ E_         | 6+4)*8$     | 5: A -> F A_      |
|7     | F A_ E_ ')' A_ E_      | 6+4)*8$     | 10: F -> NUMLIT   |
|8     | NUMLIT A_ E_ ')' A_ E_ | 6+4)*8$     | match             |
|9     | A_ E_ ')' A_ E_        | +4)*8$      | 8: A_ -> empty    |
|10    | E_ ')' A_ E_           | +4)*8$      | 4: E_ -> '+' F    |
|11    | '+' F ')' A_ E_        | +4)*8$      | match             |
|12    | F ')' A_ E_            | 4)*8$       | 10: F_ -> NUMLIT  |
|13    | NUMLIT ')' A_ E_       | 4)*8$       | match             |
|14    | ')' A_ E_              | )*8$        | match             |
|15    | A_ E_                  | *8$         | 6: A -> '*' F     |
|16    | '*' F E_               | *8$         | match             |
|17    | F E_                   | 8$          | 9: F -> NUMLIT    |
|18    | NUMLIT E_              | 8$          | match             |
|19    | E_                     | $           | 4: E_ -> empty    |
|20    |                        | $           | match, DONE       |

# Example - Recursive Descent

The call stack of functions per nonterminal is like the PDA's stack if the presense of terminals is ignored. Here is a tree showing the calls taken to parse the same expression `(6+4)*8`.

    E()
    |
    +-----+
    |     |
    A()   E_()
    |     |
    |     empty
    |
    +----------------------------+
    |                            |  
    F()                          A_()
    |                            |
    +--+----------------------+  +--+
    |  |                      |  |  |
    |  E()                    |  |  F()
    |  |                      |  |  |
    |  +---------+            |  |  |
    |  |         |            |  |  |
    |  A()       E_()         |  |  |
    |  |         |            |  |  |
    |  +---+     +--+         |  |  |
    |  |   |     |  |         |  |  |
    |  F() A_()  |  A()       |  |  |
    |  |   |     |  |         |  |  |
    |  |   empty |  +---+     |  |  |
    |  |         |  |   |     |  |  |
    |  |         |  F() A_()  |  |  |
    |  |         |  |   |     |  |  |
    |  |         |  |   empty |  |  |
    |  |         |  |         |  |  |
    (  6         +  4         )  *  8

# Stage 4

If you play with the parser, you'll notice that the binary operators are *required* to be binary when written. We implicitly know that expressions like `3+3+3+3` are are the same as `((3+3)+3)+3` but the parser does not and must be explicitly told.

We can add to this capability by letting nonterminals E_ and A_ recur on themselves:

    E  -> A E_ 

    E_ -> '+' A E_
       -> '-' A E_
       -> <empty>
       
    A  -> F A_ 
    
    A_ -> '*' F A_
       -> '/' F A_
       -> <empty>

    F -> '(' E ')'
      -> NUMLIT   

This associates right, but these operators are associative so it doesn't matter: `(1+2)+3) == 1+(2+3)`.


