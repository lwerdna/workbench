Solve knight's tour in several ways

Some attempts at efficiency: hardcoded coords for knight moves, bitmap for visited squares

sat0.py - SAT solution, relies on picosat (solves 5x5 board fast, 8x8 takes a LONG time)
ktour.c - classic solution, takes forever?!
ktour2.c - classic solution with more checking, still takes forever!?
ktour3.c - classic solution with different search order in moves, solves instantly!?
genit.py - generates the hardcoded move coordinates for the above solutions

example run:

```
a@ubuntu:~/code/ktour$ gcc ktour3.c -o ktour3
a@ubuntu:~/code/ktour$ ./ktour3
failCount: 0
+--+--+--+--+--+--+--+--+
| 0|35|46|49|56|51|60|39|
+--+--+--+--+--+--+--+--+
|45|48|57|36|59|38|55|52|
+--+--+--+--+--+--+--+--+
|34| 1|26|47|50|53|40|61|
+--+--+--+--+--+--+--+--+
|25|44|33|58|37|42|31|54|
+--+--+--+--+--+--+--+--+
| 2|27|24|43|32|29|62|41|
+--+--+--+--+--+--+--+--+
|11|14|17|28|23|20| 7|30|
+--+--+--+--+--+--+--+--+
|16| 3|12| 9|18| 5|22|63|
+--+--+--+--+--+--+--+--+
|13|10|15| 4|21| 8|19| 6|
+--+--+--+--+--+--+--+--+
```

