from argparse import ArgumentParser

import numpy as np
from scipy.linalg import null_space, qr
from scipy.optimize import least_squares

from extend import cross_basis
from numeric import MATCHINGS, SELECTORS, directions, independent_error


def centered_basis(size):
    columns = np.column_stack([np.eye(size)[:, i] - np.eye(size)[:, -1] for i in range(size - 1)])
    return qr(columns, mode='economic')[0].T


def coordinate_bases():
    rows, columns = centered_basis(4), centered_basis(5)
    positive = np.array([np.outer(r, c).ravel() for r in rows for c in columns])
    row_uniform = np.array([np.outer(r, np.ones(5) / np.sqrt(5)).ravel() for r in rows])
    column_uniform = np.array([np.outer(np.ones(4) / 2, c).ravel() for c in columns])
    negative = np.vstack((row_uniform / 2, column_uniform / np.sqrt(3)))
    return positive, negative


def complete_cross(rng, positive, negative):
    existing = np.array(cross_basis())
    amplitudes = (existing @ negative.T) * np.array([4] * 3 + [3] * 4)
    right, triangular = qr(amplitudes.T, mode='economic')
    left = np.linalg.solve(triangular.T, existing @ positive.T).T
    assert np.max(abs(left.T @ left - np.eye(6))) < 1e-10
    left_rest = null_space(left.T)
    vector = rng.normal(size=left_rest.shape[1])
    vector = left_rest @ (vector / np.linalg.norm(vector))
    right_full = np.column_stack((right, null_space(right.T)))
    frame = np.column_stack((left, vector)) @ right_full.T
    return np.column_stack((frame, null_space(frame.T)))


class IsotropicChart:
    def __init__(self, positive, negative, rotation, training):
        self.positive = rotation.T @ positive
        self.negative = negative
        self.training = training
        self.rows, self.cols = np.triu_indices(12, 1)
        self.rows, self.cols = self.rows[self.rows < 7], self.cols[self.rows < 7]
        self.variables = len(self.rows)
        self.point = None

    def basis(self, point):
        coefficients = point[:self.variables] + 1j * point[self.variables:]
        transform = np.eye(12, dtype=complex)
        transform[self.rows, self.cols] = coefficients
        transform[self.cols, self.rows] = -coefficients
        inverse = np.linalg.inv(transform)
        frame = 2 * inverse[:, :7] - np.eye(12)[:, :7]
        return self.negative + frame.T @ self.positive, inverse

    def compute(self, point):
        if self.point is not None and np.array_equal(point, self.point):
            return
        self.point = point.copy()
        basis, inv = self.basis(point)
        z = self.training @ basis
        frame_gradient = -2 * (np.einsum('ip,pj->pij', inv[:, self.rows], inv[self.cols, :7]) -
                               np.einsum('ip,pj->pij', inv[:, self.cols], inv[self.rows, :7]))
        basis_gradient = np.einsum('pij,ik->pjk', frame_gradient, self.positive)
        residuals, derivatives = [], []
        for indices, selector in zip(MATCHINGS[1:], SELECTORS[1:]):
            terms = z[:, indices]
            scale = np.sqrt(len(indices))
            residuals.append(terms.prod(axis=2).sum(axis=1) / scale)
            order = terms.shape[2]
            partials = np.stack([terms[:, :, [j for j in range(order) if j != k]].prod(axis=2)
                                 for k in range(order)], axis=2)
            gradient = (partials.reshape(len(z), -1) @ selector) / scale
            all_gradients = np.einsum('mj,mk->mjk', self.training, gradient).reshape(len(z), -1)
            derivatives.append(all_gradients @ basis_gradient.reshape(self.variables, -1).T)
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


def main():
    parser = ArgumentParser()
    parser.add_argument('case', choices=['completing-cross', 'random-isotropic'])
    args = parser.parse_args()
    rng = np.random.default_rng(751 if args.case == 'completing-cross' else 752)
    positive, negative = coordinate_bases()
    training, holdout = directions(rng, 240), directions(rng, 240)
    for attempt in range(8):
        rotation = complete_cross(rng, positive, negative) if args.case == 'completing-cross' else qr(rng.normal(size=(12, 12)))[0]
        chart = IsotropicChart(positive, negative, rotation, training)
        initial = (0.02, 0.08, 0.16, 0.25)[attempt % 4] * rng.normal(size=2 * chart.variables)
        initial_basis, _ = chart.basis(initial)
        assert max(abs(initial_basis.sum(axis=1))) < 1e-10
        assert independent_error(initial_basis, holdout)[0] < 1e-9
        direction = rng.normal(size=len(initial))
        finite_diff = (chart.fun(initial + 1e-6 * direction) - chart.fun(initial - 1e-6 * direction)) / 2e-6
        gradient_error = np.linalg.norm(finite_diff - chart.jac(initial) @ direction) / max(1, np.linalg.norm(finite_diff))
        assert gradient_error < 1e-5, gradient_error
        result = least_squares(chart.fun, initial, jac=chart.jac, method='lm', max_nfev=240,
                               ftol=1e-11, xtol=1e-11, gtol=1e-11)
        basis, _ = chart.basis(result.x)
        err = independent_error(basis, holdout)
        print(f'Trial {attempt}: {result.nfev} evaluations, independent homogeneous residuals {err}', flush=True)
        if max(err) < 1e-8:
            print('Candidate only, requires exact reconstruction. Singular values:',
                  np.linalg.svd(basis, compute_uv=False), flush=True)
            for row in basis:
                print('CANDIDATE:', ' '.join(str(value) for value in row), flush=True)


if __name__ == '__main__':
    main()
