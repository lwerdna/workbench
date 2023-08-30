#!/usr/bin/env python

#Runtime Details 60ms Beats 16.97%of users with Python
#Memory Details 13.41MB Beats 24.92%of users with Python

# Definition for singly-linked list.
class ListNode(object):
    def __init__(self, val=0, next=None):
        self.val = val
        self.next = next

    def __str__(self):
        result = []
        curr = self
        while curr:
            result.append(str(curr.val))
            curr = curr.next
        return ' -> '.join(result)

class Solution(object):
    def values(self, node):
        if node:
            return [node.val] + self.values(node.next)
        else:
            return []

    def node2num(self, node):
        return sum([v * 10**i for (i,v) in enumerate(self.values(node))])

    def num2node(self, num):
        result = None
        for value in [int(c) for c in str(num)]:
            result = ListNode(value, result)

        if not result:
            result = ListNode(0)

        return result
            
    def addTwoNumbers(self, l1, l2):
        return self.num2node(self.node2num(l1) + self.node2num(l2))

if __name__ == '__main__':
    sol = Solution()

    # l1 = [2,4,3], l2 = [5,6,4]
    l1 = ListNode(2, ListNode(4, ListNode(3)))
    l2 = ListNode(5, ListNode(6, ListNode(4)))
    result = sol.addTwoNumbers(l1, l2)
    assert str(result) == '7 -> 0 -> 8'

    # l1 = [0], l2 = [0]
    l1 = ListNode(0)
    l2 = ListNode(0)
    result = sol.addTwoNumbers(l1, l2)
    assert str(result) == '0'

    # l1 = [9,9,9,9,9,9,9], l2 = [9,9,9,9]
    l1 = ListNode(9, ListNode(9, ListNode(9, ListNode(9, ListNode(9, ListNode(9, ListNode(9)))))))
    l2 = ListNode(9, ListNode(9, ListNode(9, ListNode(9))))
    result = sol.addTwoNumbers(l1, l2)
    assert str(result) == '8 -> 9 -> 9 -> 9 -> 0 -> 0 -> 0 -> 1'
