from argparse import ArgumentParser
import signal

import numpy as np
from scipy.linalg import qr
from scipy.optimize import least_squares

from extend import CELLS, cross_basis, matchings

DIMENSION = 7
MATCHINGS = [np.array(list(matchings(order)), dtype=int) for order in (2, 3, 4)]
SELECTORS = [np.eye(CELLS)[indices.flatten()] for indices in MATCHINGS]


def cyclotomic_seed():
    omega = complex(-0.5, np.sqrt(3) / 2)
    left, right = np.zeros((2, 4, 5), dtype=complex)
    for i, phase in enumerate((1, omega, omega**2)):
        left[i, :2] = phase, -phase
    for i, phase in enumerate((1, omega**2, omega)):
        right[i, 2:4] = phase, -phase
    other = np.zeros((4, 4, 5))
    for j in range(4):
        other[j, 3, j] = 1
        other[j, 3, 4] = -1
    return np.vstack((left.reshape(1, -1), right.reshape(1, -1), other.reshape(4, -1)))


def directions(generator, count):
    return (generator.normal(size=(count, DIMENSION)) +
            1j * generator.normal(size=(count, DIMENSION))) / np.sqrt(2 * DIMENSION)


def start_basis(generator, case, attempt):
    noise = generator.normal(size=(DIMENSION, CELLS)) + 1j * generator.normal(size=(DIMENSION, CELLS))
    noise -= noise.mean(axis=1)[:, None]
    if case == 'random':
        return noise
    base = np.array(cross_basis()) if case == 'cross' else cyclotomic_seed()
    hold = np.vstack((base, np.zeros((1, CELLS))))
    amplitude = (0.03, 0.12, 0.35, 0.7)[attempt % 4]
    hold = hold + amplitude * noise
    hold[-1] = noise[-1]
    return hold


class Chart:
    def __init__(self, basis, directions):
        _, _, permutation = qr(basis, pivoting=True, mode='economic')
        self.pivot = permutation[:DIMENSION]
        self.dependent = permutation[DIMENSION]
        self.free = permutation[DIMENSION + 1:]
        self.arity = DIMENSION * len(self.free)
        self.directions = directions
        self.cached_point = None
        shifted = np.linalg.solve(basis[:, self.pivot], basis)
        free = shifted[:, self.free].ravel()
        self.initial = np.r_[free.real, free.imag]

    def basis(self, point):
        free = (point[:self.arity] + 1j * point[self.arity:]).reshape(DIMENSION, -1)
        result = np.zeros((DIMENSION, CELLS), dtype=complex)
        result[:, self.pivot] = np.eye(DIMENSION)
        result[:, self.free] = free
        result[:, self.dependent] = -1 - free.sum(axis=1)
        return result

    def compute(self, point):
        if self.cached_point is not None and np.array_equal(point, self.cached_point):
            return
        self.cached_point = point.copy()
        samples = self.directions @ self.basis(point)
        residuals, derivatives = [], []
        for indices, selector in zip(MATCHINGS, SELECTORS):
            terms = samples[:, indices]
            scale = np.sqrt(indices.shape[0])
            residuals.append(terms.prod(axis=2).sum(axis=1) / scale)
            order = terms.shape[2]
            partial = np.stack([terms[:, :, [j for j in range(order) if j != k]].prod(axis=2)
                                for k in range(order)], axis=2)
            cell_gradient = partial.reshape(samples.shape[0], -1) @ selector
            constrained = cell_gradient[:, self.free] - cell_gradient[:, self.dependent, None]
            gradient = np.einsum('mk,mj->mkj', self.directions, constrained).reshape(len(samples), -1) / scale
            derivatives.append(gradient)
        values = np.concatenate(residuals)
        jacobian = np.vstack(derivatives)
        self.residual = np.r_[values.real, values.imag]
        self.derivative = np.block([[jacobian.real, -jacobian.imag], [jacobian.imag, jacobian.real]])

    def fun(self, point):
        self.compute(point)
        return self.residual

    def jac(self, point):
        self.compute(point)
        return self.derivative


def independent_error(basis, samples):
    matrices = samples @ basis
    return [float(np.max(np.abs(matrices[:, indices].prod(axis=2).sum(axis=1))))
            for indices in MATCHINGS]


def exhausted(_signum, _frame):
    raise TimeoutError


def main():
    parser = ArgumentParser()
    parser.add_argument('case', choices=['cross', 'cyclotomic', 'random'])
    parser.add_argument('--trials', type=int, default=4)
    args = parser.parse_args()
    generator = np.random.default_rng({'cross': 604, 'cyclotomic': 180, 'random': 179}[args.case])
    training, holdout = directions(generator, 240), directions(generator, 240)
    signal.signal(signal.SIGALRM, exhausted)
    for attempt in range(args.trials):
        chart = Chart(start_basis(generator, args.case, attempt), training)
        signal.alarm(120)
        try:
            result = least_squares(chart.fun, chart.initial, jac=chart.jac, method='lm', max_nfev=180,
                                   ftol=1e-11, xtol=1e-11, gtol=1e-11)
        except TimeoutError:
            print(f'Trial {attempt}: timed out', flush=True)
            continue
        finally:
            signal.alarm(0)
        basis = chart.basis(result.x)
        err = independent_error(basis, holdout)
        print(f'Trial {attempt}: {result.nfev} evaluations, independent homogeneous residuals {err}', flush=True)
        if max(err) < 1e-8:
            svals = np.linalg.svd(basis, compute_uv=False)
            print('Candidate only, requires exact reconstruction. Singular values:', svals, flush=True)
            for row in basis:
                print('CANDIDATE:', ' '.join(str(value) for value in row), flush=True)


if __name__ == '__main__':
    main()
