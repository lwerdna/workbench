#!/usr/bin/env python3

import os, sys

from pprint import pprint

class Solution0:
    def coinChange(self, coins: list[int], amount: int) -> int:
        if not amount: return 0

        table = [0] + [None]*amount
        
        for a in range(1, amount+1):
            vals = [table[a-c]+1 for c in coins if a-c >= 0 and table[a-c] != None]
            table[a] = min(vals) if vals else None

        return table[amount] or -1

# use only a portion of the table
class Solution1:
    def coinChange(self, coins: list[int], amount: int) -> int:
        if not amount: return 0

        # the most we'll have to look back is the largest coin
        table_n = min(max(coins), 10000)

        table = [None]*(table_n-1) + [0]
        
        for a in range(1, amount+1):
            vals = [table[-c]+1 for c in coins if c <= table_n and table[-c] != None]
            table.pop(0)
            table.append(min(vals) if vals else None)

        return table[-1] or -1

# use only a portion of the table, and NO pop/append list changing
class Solution2:
    def coinChange(self, coins: list[int], amount: int) -> int:
        if not amount: return 0

        # the most we'll have to look back is the largest coin
        table_n = min(max(coins), 10000)

        #breakpoint()
        table = [0] + [None]*(table_n-1)
       
        i = 0
        for a in range(1, amount+1):
            i = (i + 1) % table_n
            vals = [table[(i-c) % table_n]+1 for c in coins if c <= table_n and table[(i-c) % table_n] != None]
            table[i] = min(vals) if vals else None

        return table[i] or -1

class Solution3:
    def coinChange(self, coins, amount):
        memo = [0] + [-1] * amount

        for amt in range(1, amount+1):
            subresults = [memo[amt-c]+1 for c in coins if amt-c >= 0 and memo[amt-c] != -1]
            memo[amt] = min(subresults) if subresults else -1

        return memo[amount]

for sol in [Solution0(), Solution1(), Solution2(), Solution3()]:
    assert(sol.coinChange([1,2,5], 11) == 3)
    assert(sol.coinChange([2147483647], 2) == -1)
    assert(sol.coinChange([2], 3) == -1)
    assert(sol.coinChange([1], 0) == 0)

    assert sol.coinChange([1, 10, 17], 30) == 3
    assert sol.coinChange([1, 10, 17], 20) == 2
