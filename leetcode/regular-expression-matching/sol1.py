#!/usr/bin/env python3
# https://leetcode.com/problems/container-with-most-water

class Foo:
    @classmethod
    def compute(self, s, p):
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

assert(Foo.compute('aa', 'a') == False)
assert(Foo.compute('aa', 'a*'))
assert(Foo.compute('ab', '.*'))
assert(Foo.compute('aab', 'c*a*b'))
assert(Foo.compute('mississippi', 'mis*is*p*.') == False)
assert(Foo.compute('mississippi', 'mis*is*ip*.'))
assert(Foo.compute('', ''))
assert(Foo.compute('', '.')==False)
assert(Foo.compute('', '.*'))
assert(Foo.compute('', 'a')==False)
assert(Foo.compute('', 'a*'))
assert(Foo.compute('aaaaaaaaaaaaab', 'a*a*a*a*a*a*a*a*a*a*c')==False)
assert(Foo.compute('aaaaaaaaaaaaab', 'a*a*a*a*a*a*a*a*a*a*b'))
assert(Foo.compute('aaaaaaaaacccxyz', 'a*a*a*a*a*a*a*a*a*a*b*b*b*b*b*b*b*c*c*c*c*c*c*xyz'))
print('OK!')
