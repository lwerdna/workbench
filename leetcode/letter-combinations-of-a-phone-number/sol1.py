#!/usr/bin/env python3

# 20ms, 11.8mb

class Solution:
    def compute(self, s):
        if s == '': return []

        lookup = {
            '2':list('abc'),
            '3':list('def'),
            '4':list('ghi'),
            '5':list('jkl'),
            '6':list('mno'),
            '7':list('pqrs'),
            '8':list('tuv'),
            '9':list('wxyz')
        }

        sets = []
        bases = []
        for c in s:
            tmp = lookup[c]
            sets.append(lookup[c])
            bases.append(len(tmp))

        digits = [0]*len(bases)

        sets.reverse()
        bases.reverse()

        results = []
        done = False
        while not done:
            # current number -> string
            result = ''
            for (j,set_) in enumerate(sets):
                result = set_[digits[j]] + result
            results.append(result)

            number = ''.join(map(str, digits))
            #print('mapped %s -> %s' % (number,result))

            # increment current number
            for (j,base) in enumerate(bases):
                digits[j] += 1
                # break if no carry needed
                if digits[j]<base:
                    break
                # break if carry needed and this is the last digit
                if j == len(bases)-1:
                    done = True
                    break
                # set to zero, loop will increment next
                digits[j] = 0
        return results

inp = "23"
inp = ''
inp = '222'
inp = '2399'

sol = Solution()
ans = sol.compute(inp)

print(ans)
