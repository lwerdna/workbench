class Solution:
    def updateMatrix(self, mat):
        rows = len(mat)
        cols = len(mat[0])
        n = rows*cols

        result = []
        for i in range(rows):
            result.append([None] * cols)

        filled = 0

        # create worklist with all points with 0
        work = []
        for y in range(rows):
            for x in range(cols):
                if mat[y][x] == 0:
                    result[y][x] = 0
                    work.append((y, x))

        # have all 0's "spread" with 1's to adjacent cells
        current = 0
        while work:
            work_new = []

            for (y,x) in work:
                for (y_, x_) in [(y+1,x), (y-1,x), (y,x+1), (y,x-1)]:
                    if y_ >= 0 and y_ < rows and x_ >= 0 and x_ < cols and result[y_][x_] == None:
                        result[y_][x_] = current + 1
                        work_new.append((y_, x_))

            work = work_new
            current += 1

        #
        return result

if __name__ == '__main__':
    s = Solution()

    print(s.updateMatrix([[0,0,0],[0,1,0],[0,0,0]]))
    print(s.updateMatrix([[0,0,0],[0,1,0],[1,1,1]]))
