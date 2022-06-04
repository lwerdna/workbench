#!/usr/bin/env python3

class Solution0:
    @classmethod
    def isMatch(self, s, p):
    # ~~~~~ snip to leetcode
    
        # replace a*a*a*...a* -> a*
        i = 0
        p2 = ''
        lenp = len(p)
        while i<lenp:
            if i<lenp-1 and p[i+1]=='*':
                save = p[i:i+2]
                #print('save is: %s' % save)
                while i<lenp-1 and p[i:i+2]==save:
                    #print('%d -> %d' % (i, i+2))
                    i += 2
                p2 += save
            else:
                p2 += p[i]
                i += 1
        if p != p2:
            #print('optimized %s -> %s' % (p, p2))
            p = p2
            
        return self.helper(s, 0, p, 0)
        
    @classmethod
    def helper(self, string, i, pattern, j, depth=0):
        #print('%shelper("%s", "%s")' % (' '*depth, string[i:], pattern[j:]))
        
        # both exhausted? MATCH!
        if len(string)==i and len(pattern)==j:
            #print('returning True!')
            return True
        # string remaining, pattern empty -> MISMATCH
        if len(string)>i and len(pattern)==j:
            return False
             
        star = len(pattern)>(j+1) and pattern[j+1]=='*'
             
        # string empty, pattern remaining:
        if len(string)==i:
            return star and self.helper(string, i, pattern, j+2, depth+1)             
              
        isdot = pattern[j]=='.'
        ismatch = isdot or (string[i] == pattern[j])
            
        if ismatch:
            if not star:
                return self.helper(string, i+1, pattern, j+1, depth+1)
            else:
                # star eats 1
                if self.helper(string, i+1, pattern, j+2, depth+1):
                    return True
                # star eats multiple (greedy)
                if self.helper(string, i+1, pattern, j, depth+1):
                    return True
                # * eats 0
                return self.helper(string, i, pattern, j+2, depth+1)
        elif star:
            # * eats 0
            return self.helper(string, i, pattern, j+2, depth+1)
            
        return False

class Table:
    def __init__(self, rows, cols):
        self.rows = rows
        self.cols = cols
        self.cells = [[0]*cols for k in range(rows)]

    def access(self, row, col):
        # empty string matches empty pattern
        if row == self.rows and col == self.cols:
            return 1

        if row < 0 or row >= self.rows:
            return 0
        if col < 0 or col >= self.cols:
            return 0
        return self.cells[row][col]

    def set(self, row, col, val):
        assert row >= 0 and row <= self.rows, breakpoint()
        assert col >= 0 and col <= self.cols
        self.cells[row][col] = val

class Solution1:
    def isMatch(s, p):
        table = Table(len(p), len(s))

        # seed last column
        col = len(s)-1
        for row in reversed(range(len(p))):
            table.set(row, col, p[row]=='*' or p[row]=='.' or p[row]==s[col])

        # seed last row
        row = len(p)-1
        for col in reversed(range(len(s)-1)):
            table.set(row, col, p[row]=='*')

        for col in reversed(range(len(s)-1)):
            for row in reversed(range(len(p)-1)):
                val = None
                if p[row] == '*':
                    val = table.access(row+1, col) or table.access(row, col+1)
                elif p[row] == '.':
                    val = table.access(row+1, col+1)
                else:
                    val = p[row] == s[col] and table.access(row+1, col+1)
                table.set(row, col, int(val))
        return table.access(0, 0)

for sol in [Solution0, Solution1]:
    assert(sol.isMatch('aa', 'a') == False)
    assert(sol.isMatch('aa', 'a*'))
    assert(sol.isMatch('ab', '.*'))
    assert(sol.isMatch('aab', 'c*a*b'))
    assert(sol.isMatch('mississippi', 'mis*is*p*.') == False)
    assert(sol.isMatch('mississippi', 'mis*is*ip*.'))
    assert(sol.isMatch('', ''))
    assert(sol.isMatch('', '.')==False)
    assert(sol.isMatch('', '.*'))
    assert(sol.isMatch('', 'a')==False)
    assert(sol.isMatch('', 'a*'))
    assert(sol.isMatch('aaaaaaaaaaaaab', 'a*a*a*a*a*a*a*a*a*a*c')==False)
    assert(sol.isMatch('aaaaaaaaaaaaab', 'a*a*a*a*a*a*a*a*a*a*b'))
    assert(sol.isMatch('aaaaaaaaacccxyz', 'a*a*a*a*a*a*a*a*a*a*b*b*b*b*b*b*b*c*c*c*c*c*c*xyz'))

print('OK!')
