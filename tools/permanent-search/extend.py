from collections import defaultdict
from fractions import Fraction
from itertools import combinations, permutations, product

ROWS = 4
COLS = 5
CELLS = ROWS * COLS


def pair(first, second):
    column = [0] * CELLS
    column[first] = 1
    column[second] = -1
    return column


def cross_basis():
    return [pair(j, 0) for j in range(1, COLS)] + [
        pair(i * COLS, COLS) for i in range(2, ROWS)
    ]


def matchings(order):
    for row_indices in combinations(range(ROWS), order):
        for col_indices in permutations(range(COLS), order):
            yield tuple(i * COLS + j for i, j in zip(row_indices, col_indices))


def evaluate_coefficients(basis):
    forms = [tuple((j, v) for j, v in enumerate(row) if v) for row in zip(*basis)]
    for order in range(1, ROWS + 1):
        coefficients = defaultdict(int)
        for matching in matchings(order):
            for terms in product(*(forms[i] for i in matching)):
                monomial = tuple(sorted(j for j, _ in terms))
                value = 1
                for _, coefficient in terms:
                    value *= coefficient
                coefficients[monomial] += value
        yield {term: value for term, value in coefficients.items() if value}


def extension_constraints(basis):
    forms = [tuple((j, v) for j, v in enumerate(row) if v) for row in zip(*basis)]
    equations = []
    for order in range(1, ROWS + 1):
        derivative = defaultdict(lambda: [0] * CELLS)
        for matching in matchings(order):
            for coordinate in matching:
                other_cells = tuple(i for i in matching if i != coordinate)
                for terms in product(*(forms[i] for i in other_cells)):
                    monomial = tuple(sorted(j for j, _ in terms))
                    value = 1
                    for _, coefficient in terms:
                        value *= coefficient
                    derivative[monomial][coordinate] += value
        equations.extend(coefficients for coefficients in derivative.values() if any(coefficients))
    return equations


def nullspace(equations, width, scalar=Fraction):
    pivot_rows = {}
    for source in equations:
        row = [scalar(value) for value in source]
        for pivot, previous in sorted(pivot_rows.items()):
            if row[pivot]:
                row = [a - row[pivot] * b for a, b in zip(row, previous)]
        pivot = next((j for j, value in enumerate(row) if value), None)
        if pivot is None:
            continue
        value = row[pivot]
        row = [x / value for x in row]
        for old_pivot, previous in list(pivot_rows.items()):
            if previous[pivot]:
                pivot_rows[old_pivot] = [a - previous[pivot] * b for a, b in zip(previous, row)]
        pivot_rows[pivot] = row
    basis = []
    for j in range(width):
        if j not in pivot_rows:
            vector = [scalar(0)] * width
            vector[j] = scalar(1)
            for pivot, row in pivot_rows.items():
                vector[pivot] = -row[j]
            basis.append(vector)
    return basis


if __name__ == '__main__':
    cross = cross_basis()
    assert not any(evaluate_coefficients(cross))
    constraints = extension_constraints(cross)
    tangent = nullspace(constraints, CELLS)
    print(f'Cross basis: {len(cross)} independent directions, all four coefficient families vanish')
    print(f'Linear extension constraints: {len(constraints)} equations, rank {CELLS - len(tangent)}')
    print(f'Extension kernel dimension: {len(tangent)}')
    for vector in tangent:
        print(' '.join(str(v) for v in vector))
