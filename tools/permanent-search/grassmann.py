from argparse import ArgumentParser
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from math import lcm
import signal

from extend import CELLS, cross_basis, evaluate_coefficients, extension_constraints, nullspace

CASE_NORMALS = {
    'column-two-entries': (0, 0, 0, 0, 1, 0),
    'column-three-entries': (0, 0, 0, 0, 1, -1),
    'row-one-pair': (1, -1, 0, 0, 0, 0),
    'row-two-pairs': (1, 1, -1, -1, 0, 0),
}


def rank(vectors):
    return CELLS - len(nullspace(vectors, CELLS))


def seed_and_quotient(normal):
    cross = cross_basis()
    pivot = next(i for i, value in enumerate(normal) if value)
    seed = [[x - normal[i] * y for x, y in zip(row, cross[pivot])]
            for i, row in enumerate(cross) if i != pivot]
    current = seed.copy()
    quotient = []
    for vector in nullspace(extension_constraints(seed), CELLS):
        if rank([*current, vector]) > len(current):
            current.append(vector)
            quotient.append(vector)
    assert rank(seed) == 5
    assert not any(evaluate_coefficients(seed))
    return seed, quotient


def chart_equations(seed_count, dimension, coefficients, first, second):
    """Return sparse equations in the free entries of the two identity-normalized vectors."""
    pivots = (first, second)
    variables = [(j, col) for col in range(2) for j in range(dimension) if j not in pivots]
    slots = {coordinate: i for i, coordinate in enumerate(variables)}
    entries = defaultdict(lambda: defaultdict(Fraction))
    for order_coefficients in coefficients:
        for monomial, value in order_coefficients.items():
            seed_vars = tuple(i for i in monomial if i < seed_count)
            quotient_vars = tuple(i - seed_count for i in monomial if i >= seed_count)
            for assignments in product(range(2), repeat=len(quotient_vars)):
                exponents = [0] * len(variables)
                for j, col in zip(quotient_vars, assignments):
                    if j in pivots:
                        if j != pivots[col]:
                            break
                    else:
                        exponents[slots[j, col]] += 1
                else:
                    terms = tuple(sorted(seed_vars + tuple(seed_count + col for col in assignments)))
                    entries[terms][tuple(exponents)] += value
    return variables, {term: {exponents: value for exponents, value in poly.items() if value}
                      for term, poly in entries.items()}


def new_vectors(quotient, pivots, variables, values):
    all_values = dict(zip(variables, values))
    vectors = []
    for col in range(2):
        coefficients = [all_values.get((j, col), int(j == pivots[col])) for j in range(len(quotient))]
        vectors.append([sum(x * a for x, a in zip(coefficients, cell)) for cell in zip(*quotient)])
    return vectors


def verify_expansion(seed, quotient, pivots, variables, entries):
    values = [i % 3 - 1 for i in range(len(variables))]
    actual = dict(item for group in evaluate_coefficients(
        seed + new_vectors(quotient, pivots, variables, values)) for item in group.items())
    predicted = {}
    for term, poly in entries.items():
        total = Fraction(0)
        for exponents, coefficient in poly.items():
            contribution = coefficient
            for value, power in zip(values, exponents):
                contribution *= value**power
            total += contribution
        if total:
            predicted[term] = total
    assert predicted == actual, (predicted, actual)


def rational_ideals(entries, variables):
    from sympy import Poly, QQ

    # Clearing denominators and deduplicating identical polynomials does not change the ideal.
    sparse_polynomials = set()
    for polynomial in entries.values():
        if not polynomial:
            continue
        fractions = [Fraction(value) for value in polynomial.values()]
        denominator = lcm(*(v.denominator for v in fractions))
        converted = tuple(sorted((powers, int(denominator * value)) for powers, value in polynomial.items()))
        if converted[0][1] < 0:
            converted = tuple((powers, -value) for powers, value in converted)
        sparse_polynomials.add(converted)
    return [Poly.from_dict(dict(p), variables, domain=QQ) for p in sorted(sparse_polynomials)]


def timeout(_signum, _frame):
    raise TimeoutError


def solve_chart(seed, quotient, pivots, variables, entries, seconds):
    from sympy import QQ, groebner, solve_poly_system, symbols

    symbols = symbols(f'x:{len(variables)}')
    polynomials = rational_ideals(entries, symbols)
    quadratics = [p for p in polynomials if p.total_degree() <= 2]
    signal.signal(signal.SIGALRM, timeout)
    signal.alarm(seconds)
    try:
        for equations in (quadratics, polynomials):
            basis = groebner(equations, *symbols, order='grevlex', domain=QQ, method='f5b')
            if len(basis.polys) == 1 and basis.polys[0].total_degree() == 0:
                print('excluded over characteristic zero', flush=True)
                return 'excluded'
        print('proper ideal over characteristic zero', flush=True)
        if basis.is_zero_dimensional:
            lex = basis.fglm('lex')
            solutions = solve_poly_system(list(lex), *symbols) or []
            for solution in solutions[:1]:
                witness = seed + new_vectors(quotient, pivots, variables, solution)
                for vector in witness:
                    print('WITNESS ROW:', ' '.join(map(str, vector)), flush=True)
        else:
            print('Leading relations:', [str(p.as_expr()) for p in basis.polys[:14]], flush=True)
        return 'proper'
    except TimeoutError:
        print('timed out', flush=True)
        return 'timeout'
    finally:
        signal.alarm(0)


def main():
    parser = ArgumentParser()
    parser.add_argument('case', choices=CASE_NORMALS)
    parser.add_argument('--validate-only', action='store_true')
    parser.add_argument('--seconds-per-chart', type=int, default=45)
    args = parser.parse_args()
    seed, quotient = seed_and_quotient(CASE_NORMALS[args.case])
    coefficients = list(evaluate_coefficients(seed + quotient))
    print(f'{args.case}: seed dimension {len(seed)}, extension quotient dimension {len(quotient)}', flush=True)
    results = defaultdict(int)
    for first, second in combinations(range(len(quotient)), 2):
        variables, equations = chart_equations(len(seed), len(quotient), coefficients, first, second)
        verify_expansion(seed, quotient, (first, second), variables, equations)
        if not args.validate_only:
            print(f'Chart {(first, second)}: {sum(bool(p) for p in equations.values())} equations', flush=True)
            result = solve_chart(seed, quotient, (first, second), variables, equations, args.seconds_per_chart)
            results[result] += 1
    print('Chart results:', dict(results), flush=True)


if __name__ == '__main__':
    main()
