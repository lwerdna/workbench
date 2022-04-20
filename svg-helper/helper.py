class Line:
    def __init__(self, x1,y1, x2,y2, **kwargs):
        self.x1 = x1
        self.y1 = y1
        self.x2 = x2
        self.y2 = y2

        self.start = kwargs.get('start', None)
        self.end = kwargs.get('end', None)

        self.color = kwargs.get('color', 'black')
        self.width = 1

        self.transform = kwargs.get('transform', lambda x,y: (x,y))

    def svg(self):
        (x1, y1) = self.transform(self.x1, self.y1)
        (x2, y2) = self.transform(self.x2, self.y2)

        attribs = []
        attribs.append(f'x1="{x1}"')
        attribs.append(f'y1="{y1}"')
        attribs.append(f'x2="{x2}"')
        attribs.append(f'y2="{y2}"')
        attribs.append(f'stroke="{self.color}"')
        attribs.append(f'stroke-width="{self.width}"')

        lookup = {  'arrow-forward': 'triangle-forward',
                    'arrow-backward': 'triangle-backward',
                    'dot': 'dot'
                }

        if self.start:
            attribs.append(f'marker-start="url(#{lookup[self.start]})"')
        if self.end:
            attribs.append(f'marker-end="url(#{lookup[self.end]})"')

        return '<line ' + ' '.join(attribs) + ' />'
        
class Drawing:
    def __init__(self, width, height, **kwargs):
        self.width = width
        self.height = height
        self.transform = kwargs.get('transform', lambda x,y: (x,y))

        self.elements = []

        self.guide_visible = False
        self.guide_y_spacing = None
        self.guide_x_spacing = None

    def guide(self, x_spacing, y_spacing, visible=True):
        self.guide_x_spacing = x_spacing
        self.guide_y_spacing = y_spacing
        self.guide_visible = visible

    #
    # line drawing stuff
    #
    def line(self, x1, y1, x2, y2):
        self.elements.append(Line(x1, y1, x2, y2, transform=self.transform))

    def line_segment(self, x1, y1, x2, y2):
        e = Line(x1, y1, x2, y2, start='dot', end='dot', transform=self.transform)
        self.elements.append(e)

    def ray(self, x1, y1, x2, y2):
        e = Line(x1, y1, x2, y2, start='dot', end='arrow-forward', transform=self.transform)
        self.elements.append(e)

    def arrow(self, x1, y1, x2, y2):
        e = Line(x1, y1, x2, y2, end='arrow-forward', transform=self.transform)
        self.elements.append(e)

    def double_arrow(self, x1, y1, x2, y2):
        e = Line(x1, y1, x2, y2, end='arrow-forward', start='arrow-backward', transform=self.transform)
        self.elements.append(e)

    #
    # render
    #
    def export_svg(self, fpath):
        with open(fpath, 'w') as fp:
            fp.write('<svg width="{self.width}" height="{self.height}" viewBox="0 0 {self.width} {self.height}"\n')
            fp.write('    xmlns="http://www.w3.org/2000/svg" version="1.1"\n')
            fp.write('    xmlns:xlink="http://www.w3.org/1999/xlink" >\n')

            # define arrowheads
            fp.write('<defs>\n')
            fp.write('  <marker id="triangle-forward" viewBox="0 0 10 10" refX="10" refY="5" ')
            fp.write('markerUnits="strokeWidth" markerWidth="10" markerHeight="10" ')
            fp.write('orient="auto">\n')
            fp.write('    <path d="M 0 0 L 10 5 L 0 10 z" fill="#000"/>\n')
            fp.write('  </marker>\n')
            fp.write('  <marker id="triangle-backward" viewBox="0 0 10 10" refX="0" refY="5" ')
            fp.write('markerUnits="strokeWidth" markerWidth="10" markerHeight="10" ')
            fp.write('orient="auto">\n')
            fp.write('    <path d="M 0 5 L 10 0 L 10 10 z" fill="#000"/>\n')
            fp.write('  </marker>\n')
            fp.write('  <marker id="dot" viewBox="0 0 10 10" refX="5" refY="5" ')
            fp.write('markerUnits="strokeWidth" markerWidth="10" markerHeight="10" ')
            fp.write('orient="auto">\n')
            fp.write('    <circle cx="5" cy="5" r="4" />\n')
            fp.write('  </marker>\n')
            fp.write('</defs>\n')

            # draw guide?
            guide_elems = []
            if self.guide_visible:
                for x in range(0, self.width, self.guide_x_spacing):
                    guide_elems.append(Line(x, 0, x, self.height, color='grey'))
                for y in range(0, self.height, self.guide_y_spacing):
                    guide_elems.append(Line(0, y, self.width, y, color='grey'))

            fp.write('<!-- guide -->\n')
            for element in guide_elems:
                fp.write(element.svg() + '\n')

            fp.write('<!-- ELEMENTS -->\n')
            for element in self.elements:
                fp.write(element.svg() + '\n')

            fp.write('</svg>')

