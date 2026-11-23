from argparse import ArgumentParser
from collections import Counter
from itertools import combinations
from math import lcm
import subprocess

from extend import evaluate_coefficients
from grassmann import CASE_COORDINATES, chart_equations, seed_and_quotient, verify_expansion


def singular_input(equations, width):
    expressions = []
    for polynomial in equations.values():
        if not polynomial:
            continue
        scale = lcm(*(coefficient.denominator for coefficient in polynomial.values()))
        terms = []
        for powers, coefficient in sorted(polynomial.items()):
            term = str(int(coefficient * scale))
            for j, exp in enumerate(powers):
                if exp:
                    term += f'*x{j}' + (f'^{exp}' if exp != 1 else '')
            terms.append(term)
        expressions.append('+'.join(terms).replace('+-', '-'))
    symbols = ','.join(f'x{j}' for j in range(width))
    constraints = ',\n'.join(dict.fromkeys(expressions)) or '0'
    return (f'ring R=0,({symbols}),dp;\nideal I={constraints};\n'
            'ideal G=slimgb(I);\n'
            'if (size(G)==1 && deg(G[1])==0 && G[1]!=0) { print("EXCLUDED"); }\n'
            'else { print("PROPER"); print(dim(G)); if (size(G)<25) { print(G); } }\n'
            'quit;\n')


def solve(equations, width, seconds):
    quadratics = {term: p for term, p in equations.items() if all(sum(exponents) <= 2 for exponents in p)}
    try:
        for expressions in (quadratics, equations):
            result = subprocess.run(['Singular', '-q'], input=singular_input(expressions, width),
                                    timeout=seconds, capture_output=True, text=True, check=True)
            lines = result.stdout.splitlines()
            if 'EXCLUDED' in lines:
                return 'excluded', ''
            if 'PROPER' not in lines or any(line.lstrip().startswith('?') for line in lines):
                raise RuntimeError(result.stdout[-2000:] + result.stderr[-500:])
        return 'proper', result.stdout[-4000:]
    except subprocess.TimeoutExpired:
        return 'timeout', ''


def main():
    parser = ArgumentParser()
    parser.add_argument('case', choices=CASE_COORDINATES)
    parser.add_argument('--batch', type=int, default=0)
    parser.add_argument('--batches', type=int, default=1)
    parser.add_argument('--seconds-per-system', type=int, default=45)
    args = parser.parse_args()
    seed, quotient = seed_and_quotient(args.case)
    coefficients = list(evaluate_coefficients(seed + quotient))
    results = Counter()
    for number, pivots in enumerate(combinations(range(len(quotient)), 7 - len(seed))):
        if number % args.batches != args.batch:
            continue
        variables, equations = chart_equations(len(seed), len(quotient), coefficients, pivots)
        verify_expansion(seed, quotient, pivots, variables, equations)
        outcome, details = solve(equations, len(variables), args.seconds_per_system)
        results[outcome] += 1
        print(f'Chart {pivots}: {outcome}', flush=True)
        if details:
            print(details, flush=True)
    print('Chart results:', dict(results), flush=True)


if __name__ == '__main__':
    main()
