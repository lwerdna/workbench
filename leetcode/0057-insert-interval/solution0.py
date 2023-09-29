# does the interval contain a given value?
def contains(interv, value):
    return interv[0] <= value <= interv[1]

# do two intervals intersect?
def intersects(a, b):
    return contains(a, b[0]) or contains(a, b[1]) or contains(b, a[0]) or contains(b, a[1])

# compute the union of two intervals
def union(a, b):
    return [min(a[0], b[0]), max(a[1], b[1])]

class Solution:
    def insert(self, intervals, newInterval):
        result = []

        # pass thru all intervals left of ours
        while intervals and intervals[0][1] < newInterval[0]:
            result.append(intervals.pop(0))

        # this is the clever bit! we modify our input to expand to contain
        # passing intervals that intersect
        while intervals and intersects(intervals[0], newInterval):
            newInterval = union(intervals[0], newInterval)
            intervals.pop(0)

        result.append(newInterval)

        # pass remaining intervals
        while intervals:
            result.append(intervals.pop(0))

        return result

if __name__ == '__main__':
    s = Solution()

    print('expect [[0,0],[1,5]]: ', s.insert([[1,5]], [0,0]))
    print('expect [[1,5]]: ', s.insert([[1,5]], [2,3]))
    print('expect [[1,5],[6,9]]: ', s.insert([[1,3],[6,9]], [2,5]))
    print('expect [[1,2],[3,10],[12,16]]: ', s.insert([[1,2],[3,5],[6,7],[8,10],[12,16]], [4,8]))
            
