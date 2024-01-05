import copy

def dot_list(a, b):
    assert len(a) == len(b)
    return sum(a[i]*b[i] for i in range(len(a)))

class Matrix:
    def __init__(self, **kwargs):
        if 'n_rows' in kwargs and 'n_cols' in kwargs:
            self.values = []
        
            for i in range(kwargs['n_rows']):
                self.values.append([None]*kwargs['n_cols'])
        elif 'vals' in kwargs:
            self.load(kwargs['vals'])
        else:
            assert False
            
    def load(self, values):
        self.values = copy.deepcopy(values)

    def n_rows(self):
        return len(self.values)

    def n_cols(self):
        return len(self.values[0])

    def dims(self):
        return n_rows(), n_cols()

    # applies a function to each element in the matrix
    def map(self, func):
        values = copy.deepcopy(self.values)
        for i in range(self.n_rows()):
            for j in range(self.n_cols()):
                values[i][j] = func(self.values[i][j], i, j)

        result = Matrix(self.n_rows(), self.n_cols())
        result.load(values)
        return result

    def transpose(self):
        return Matrix(self.n_cols(), self.n_rows()).map(lambda c,i,j: self.values[j][i])

    def row_vector(self, i):
        return self.values[i]

    def column_vector(self, j):
        return [row[j] for row in self.values]

    def __mul__(self, rhs):
        assert self.n_cols() == rhs.n_rows()

        result = Matrix(n_rows = self.n_rows(), n_cols = rhs.n_cols())

        for i in range(self.n_rows()):
            for j in range(rhs.n_cols()):
                result.values[i][j] = dot_list(self.row_vector(i), rhs.column_vector(j))

        return result

    def __eq__(self, other):
        if type(other) == Matrix:
            return self.values == other.values
        elif type(other) == list:
            return self.values == other

        return False

    def __str__(self):
        lines = []
        for row in self.values:
            lines.append(', '.join(str(k) for k in row))
        return '\n'.join(lines)

if __name__ == '__main__':
    A = Matrix(vals = [ [1, 2, 3],
                        [4, 5, 6]   ])

    B = Matrix(vals = [ [10, 11],
                        [20, 21],
                        [30, 31]    ])

    assert(A * B == [[140, 146], [320, 335]])
