#!/usr/bin/env python

# Give a list of addends A and a target sum S, find the subset of A so their
# sum is maximized without exceeding S. In other words, the sum is as close
# as possible to S without going over.

# This is a 0-1 knapsack problem with:
# - capacity is the target sum S
# - weights are the addends themselves
# - values are the addends themselves (since this is what we wish to maximize)

from helpers import Table

#    0  1  2  3  4  5  6
A = [8, 6, 7, 5, 3, 0, 9]
S = 19

table = Table(len(A), S+1, 0)

print(table)

for capacity in range(1,S+1):
    for (items_i, weight) in enumerate(A):
        best = None

        # If the weight exceeds the capacity, don't use the weight.
        # Our best is our best from using the previous items.
        if weight > capacity:
            best = table[items_i-1, capacity]
        else:
            best = max(
                # If we don't use this item
                table[items_i-1, capacity],

                # If we do use this item, look back to when we didn't, plus us
                table[items_i-1, capacity-weight] + weight
            )
            
        table[items_i, capacity] = best

        print(f'setting items_i={items_i}, capacity={capacity} best={best}')
        print(table)
        input()
