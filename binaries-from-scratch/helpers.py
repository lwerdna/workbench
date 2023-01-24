def align_up_to(x, alignment):
    residue = x % alignment
    if residue:
        return x + (alignment - residue)
    return x

def align_down_to(x, alignment):
    residue = x % alignment
    if residue:
        return x - residue
    return x
