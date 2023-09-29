---
UNIQUE_ID: AJL23FNR
---
| problem                                                      | complexity | how                                                          | notes                                                        |
| ------------------------------------------------------------ | ---------- | ------------------------------------------------------------ | ------------------------------------------------------------ |
| 0001: [subset sum (limit 2)](https://leetcode.com/problems/two-sum/) | O(n)       | scan, store in dict, lookup `target-cur` in dict             | #blind75                                                     |
| 0003: [longest substring with unique chars](https://leetcode.com/problems/longest-substring-without-repeating-characters/submissions/) | O(n)       | sliding window                                               |                                                              |
| 0005: [longest palindromic substring](https://leetcode.com/problems/longest-palindromic-substring) | O(n^2)     | dynamic: ispal(i,j) = ispal(i+1, j-1) and string[i] == string[j] | surprise: dynamic is not O(n), but special Manacher's algo is |
| 0011: [container with most water](https://leetcode.com/problems/container-with-most-water/) | O(n)       | sliding window                                               | surprise!                                                    |
| 0053: [maximum subarray](https://leetcode.com/problems/maximum-subarray/) | O(n)       | lowering, DP, lifting                                        | Kadane's algorithm<br />#blind75                             |
| 0057: [insert interval](https://leetcode.com/problems/insert-interval/) |            | clever way to merge in the new interval                      | grind75 Week 3 #1                                            |
| 0070: [climbing stairs](https://leetcode.com/problems/climbing-stairs/) | O(n)       | dynamic: 1+memo[stairs-1] plus 2+memo[stairs-2]              | for 2 hop options, this is fibonacci and related problems    |
| 0232: [implement queue using stacks](https://leetcode.com/problems/implement-queue-using-stacks) |            | transferring between stacks reverses the order, so one stack for enqueuing, the other for dequeuing |                                                              |
| 0542: [01 matrix](https://leetcode.com/problems/01-matrix/)  |            | straightforward: workqueue up the 0 locations and "grow" them outward with +1, refill queue, repeat | grind75 Week 3 #2                                            |
| 0560: [count subarray sums equals k](https://leetcode.com/problems/subarray-sum-equals-k) | O(n)       | cumulative sums looked up in dict                            |                                                              |
| 0713: [count subarrays product less than k](https://leetcode.com/problems/subarray-product-less-than-k/) | O(n)       | sliding window                                               | all factors >1 so cumulative product never decreases         |
| 0724: [find pivot](https://leetcode.com/problems/find-pivot-index/) | O(n)       | a summing pass allows the next pass to accumulate and compare `lsum` to `total - lsum` | list elems can be negative                                   |
| 0983: [minimum cost for tickets](https://leetcode.com/problems/minimum-cost-for-tickets/) | O(n)       | dynamic: can reach back 1 day, 1 week, or 1 month into subproblems |                                                              |

## Complexities:

**Quicksort** is O(n^2) worst case, but average O(n log n). Space is O(log n) worst case for in-place.

**Integer Factorization** is sub-exponential (I think that means slower than n log n, but not O(n^x))) - current state of the art is the GNFS (general number field sieve)

## Tips

### Greedy vs. Dynamic

A problem is said to have **optimal substructure** if an optimal solution can be constructed from optimal solutions of its subproblems.
`(optimal_substructure && !overlapping_subproblems) -> greedy`
`(optimal_substructure && overlapping_subproblems) -> dynamic`

### Dynamic

In dynamic programming, you're not limited to looking only 1 back. You can reach back way in the memo. Also, don't think the final memo entry is necessarily the returned solution. Another pass can come and return the minimum, for example. Subsolutions beyond the horizon can be discarded for space savings (eg: Fibonacci requires only two variables, not a list of all Fibonacci numbers)

### Misc.

Look at the input constraints for clues to optimizations. Eg: in [count subarrays product less than k](https://leetcode.com/problems/subarray-product-less-than-k/) all factors are >= 0, so after filtering for zeros, a cumulative product never decreases, allowing the sliding window. In [Find All Duplicates in an Array](https://leetcode.com/problems/find-all-duplicates-in-an-array/) the duplicate count is limited to 2, allowing a simple marker. It also stated all arr[i] < len(arr) which allowed the indexes of the input array to be utilized as marker location.

Look to save space by utilizing the input data structure. In [Find All Duplicates in an array](https://leetcode.com/problems/find-all-duplicates-in-an-array/) the input list could have its elements flipped in sign (x -> -x) to mark if they've been seen before.

There can be savings when you don't need maximum information about an answer. Asking if a list has a 2-sum isn't as difficult as asking for the indices for a 2-sum solution.

