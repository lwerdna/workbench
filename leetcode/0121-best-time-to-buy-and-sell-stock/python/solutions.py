#!/usr/bin/env python

# Algorithm:
# Scan right, tracking minimum amount encountered so far (best buy price to the left).
# Treat each current price as a sell price, subtracting the best buy price, tracking the biggest difference.
class Solution0:
    def maxProfit(self, prices):
        max_profit = 0
        min_price = 10000
        for p in prices:
            min_price = min(min_price, p)
            max_profit = max(max_profit, p - min_price)

        return max_profit

# Algorithm:
# Scan left, tracking maximum amount encountered so far (best sell price to the right).
# Treat each current price as a buy price, subtracting it from best sell price, tracking the biggest difference.
class Solution1:
    def maxProfit(self, prices):
        max_profit = 0
        max_price = -1
        for p in prices[::-1]:
            max_price = max(max_price, p)
            max_profit = max(max_profit, max_price - p)

        return max_profit

import itertools

# Algorithm:
# Create lookup table of best sell price.
# Scan right, subtracting current price (buy) from best sell price, recording best difference (profit).
class Solution2:
    def maxProfit(self, prices):
        max_profit = 0

        # [7,1,5,3,6,4] ->
        # [7,6,6,6,6,4]
        lookup = list(reversed(list(itertools.accumulate(reversed(prices), max))))

        for i,p in enumerate(prices):
            max_profit = max(max_profit, lookup[i] - p)

        return max_profit

# Algorithm:
# Create lookup table of best buy price.
# Scan right, subtracting current price (sell) from best buy price, recording best difference (profit).
class Solution3:
    def maxProfit(self, prices):
        max_profit = 0

        # [7,1,5,3,6,4] ->
        # [7,1,1,1,1,1]
        lookup = list(itertools.accumulate(prices, min))

        for i,p in enumerate(prices):
            max_profit = max(max_profit, p - lookup[i])

        return max_profit

if __name__ == '__main__':
    for sol in [Solution0(), Solution1(), Solution2(), Solution3()]:
        assert sol.maxProfit([7,1,5,3,6,4]) == 5
        assert sol.maxProfit([7,6,4,3,1]) == 0
