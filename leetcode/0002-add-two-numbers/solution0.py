#!/usr/bin/env python

#
# Runtime Details 37ms Beats 93.22%of users with Python
# Memory Details 13.20MB Beats 87.48%of users with Python

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
    def append(self, node, value):
        node.next = ListNode(value)
        return node.next

    def addTwoNumbers(self, l1, l2):
        result, current = None, None
        carry = 0

        while l1 or l2:
            a = l1.val if l1 else 0
            b = l2.val if l2 else 0
            sum_ = a + b + carry
            if sum_ >= 10:
                sum_ = sum_ - 10
                carry = 1
            else:
                carry = 0

            if not result:
                result = current = ListNode(sum_)
            else:
                current = self.append(current, sum_)

            if l1: l1 = l1.next
            if l2: l2 = l2.next

        if carry:
            self.append(current, carry)
            
        return result

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
