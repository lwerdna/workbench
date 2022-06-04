class Table:
    def __init__(self, rows, cols, default=0):
        self.rows = rows
        self.cols = cols
        self.cells = [[default]*cols for k in range(rows)]
        self.default = default
        self.jamount = 4

    # mytable[3,4]
    def __getitem__(self, coords):
        row,col = coords
        if row < 0 or row >= self.rows:
            return self.default
        if col < 0 or col >= self.cols:
            return self.default
        return self.cells[row][col]

    def __setitem__(self, coords, val):
        row,col = coords
        assert row >= 0 and row <= self.rows, breakpoint()
        assert col >= 0 and col <= self.cols
        self.cells[row][col] = val

    def __str__(self):
        lines = []

        # heading across the top
        words = [' '*self.jamount] + [f'{col}:'.rjust(self.jamount) for col in range(self.cols)]
        lines.append(''.join(words))

        # rows
        for row in range(self.rows):
            words = [f'{row}:'.rjust(self.jamount)]
            for col in range(self.cols):
                words.append(str(self.cells[row][col]).rjust(self.jamount))
            lines.append(''.join(words))
        return '\n'.join(lines)

    def html(self):
        rows = []

        # top heading
        words = ['<th></th>'] + [f'<th>{col}</th>' for col in range(self.cols)]
        rows.append(''.join(words))

        # rows
        for row in range(self.rows):
            words = [f'<th>{row}</th>']
            for col in range(self.cols):
                words.append((f'<td>{self.cells[row][col]}' + '</td>'))
            rows.append(f'<tr>{"".join(words)}</tr>')

        # done
        return f'<table>\n' + '\n'.join(rows) + '\n</table>'

