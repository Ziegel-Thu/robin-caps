#!/usr/bin/env python3
"""Robin eigenvalues of thin capsules by P1 finite elements.

The capsule of diameter L and radius R in R^n (n = 2, 3) is the R-neighbourhood of a
segment of length L - 2R.  Its first two Robin eigenfunctions are even in the transverse
variable (n = 2) resp. axisymmetric (n = 3) for small R, so it suffices to solve on the
half section {(x, y) : 0 < x < L, 0 < y < r(x)} with the weight w(y) = 1 (n = 2) or
w(y) = y (n = 3), natural (Neumann) condition on y = 0 and the Robin condition on the
curved boundary y = r(x).  The mesh is a structured grid in (x, t), y = t r(x), split into
triangles; the tips of the capsule are single nodes.

Usage: python3 capsule_gap.py            (prints the tables used in the paper)
"""
import math, sys
import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla
from scipy.optimize import brentq


# ---------- interval reference values -------------------------------------------------
def mu(p, q, ell, j):
    f = lambda k: k * ell - math.atan(p / k) - math.atan(q / k) - (j - 1) * math.pi
    lo, hi = (j - 1) * math.pi / ell + 1e-12, j * math.pi / ell
    k = brentq(f, lo, hi, xtol=1e-14)
    return k * k


def gap(beta, L=1.0):
    return mu(beta, beta, L, 2) - mu(beta, beta, L, 1)


def omega(k):
    return math.pi ** (k / 2) / math.gamma(k / 2 + 1)


def beta0(n, alpha):
    return alpha * omega(n) / (2 * omega(n - 1))


# ---------- mesh ------------------------------------------------------------------------
def profile(x, L, R):
    if x < R:
        return math.sqrt(max(R * R - (x - R) ** 2, 0.0))
    if x > L - R:
        return math.sqrt(max(R * R - (x - (L - R)) ** 2, 0.0))
    return R


def x_nodes(L, R, Ncap, Nbulk):
    phi = np.linspace(0, math.pi / 2, Ncap + 1)
    left = R * (1 - np.cos(phi))            # 0 .. R, clustered at the tip
    bulk = np.linspace(R, L - R, Nbulk + 1)[1:-1]
    right = L - left[::-1]
    return np.concatenate([left, bulk, right])


def build_mesh(L, R, Ncap, Nbulk, Nt):
    xs = x_nodes(L, R, Ncap, Nbulk)
    nodes, cols = [], []
    for x in xs:
        r = profile(x, L, R)
        if r < 1e-14 * R:
            cols.append([len(nodes)]); nodes.append((x, 0.0))
        else:
            ids = list(range(len(nodes), len(nodes) + Nt + 1))
            cols.append(ids)
            for t in np.linspace(0, 1, Nt + 1):
                nodes.append((x, t * r))
    tris, bedges = [], []
    for c0, c1 in zip(cols[:-1], cols[1:]):
        if len(c0) == 1:                      # left tip fan
            for j in range(Nt):
                tris.append((c0[0], c1[j], c1[j + 1]))
            bedges.append((c0[0], c1[-1]))
        elif len(c1) == 1:                    # right tip fan
            for j in range(Nt):
                tris.append((c0[j], c0[j + 1], c1[0]))
            bedges.append((c0[-1], c1[0]))
        else:
            for j in range(Nt):
                a, b, c, d = c0[j], c0[j + 1], c1[j], c1[j + 1]
                tris.append((a, c, d)); tris.append((a, d, b))
            bedges.append((c0[-1], c1[-1]))
    return np.array(nodes), np.array(tris), np.array(bedges)


# ---------- assembly --------------------------------------------------------------------
def assemble(nodes, tris, bedges, alpha, n):
    N = len(nodes)
    P = nodes[tris]                                   # (T,3,2)
    x0, y0 = P[:, 0, 0], P[:, 0, 1]
    x1, y1 = P[:, 1, 0], P[:, 1, 1]
    x2, y2 = P[:, 2, 0], P[:, 2, 1]
    det = (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
    area = 0.5 * np.abs(det)
    yc = (y0 + y1 + y2) / 3
    w = np.ones_like(area) if n == 2 else yc          # weight at the centroid
    # gradients of P1 basis functions
    gx = np.stack([y1 - y2, y2 - y0, y0 - y1], 1) / det[:, None]
    gy = np.stack([x2 - x1, x0 - x2, x1 - x0], 1) / det[:, None]
    rows = np.repeat(tris, 3, axis=1).ravel()
    colsi = np.tile(tris, (1, 3)).ravel()
    Ke = (gx[:, :, None] * gx[:, None, :] + gy[:, :, None] * gy[:, None, :]) * (area * w)[:, None, None]
    Me = (np.ones((3, 3)) + np.eye(3))[None] / 12.0 * (area * w)[:, None, None]
    K = sp.coo_matrix((Ke.ravel(), (rows, colsi)), shape=(N, N)).tocsr()
    M = sp.coo_matrix((Me.ravel(), (rows, colsi)), shape=(N, N)).tocsr()
    # Robin term on the curved boundary
    E = nodes[bedges]
    length = np.hypot(E[:, 1, 0] - E[:, 0, 0], E[:, 1, 1] - E[:, 0, 1])
    ye = (E[:, 0, 1] + E[:, 1, 1]) / 2
    we = np.ones_like(length) if n == 2 else ye
    Be = (np.ones((2, 2)) + np.eye(2))[None] / 6.0 * (alpha * length * we)[:, None, None]
    r2 = np.repeat(bedges, 2, axis=1).ravel(); c2 = np.tile(bedges, (1, 2)).ravel()
    B = sp.coo_matrix((Be.ravel(), (r2, c2)), shape=(N, N)).tocsr()
    return K + B, M


def eigen(L, R, alpha, n, Ncap, Nbulk, Nt, k=2):
    nodes, tris, bedges = build_mesh(L, R, Ncap, Nbulk, Nt)
    A, M = assemble(nodes, tris, bedges, alpha, n)
    vals = spla.eigsh(A, k=k, M=M, sigma=-1.0, which="LM")[0]
    return np.sort(vals), len(nodes)


def gap_capsule(L, R, alpha, n, levels=(1, 2)):
    """Richardson-style check: two meshes, return the finer value and the difference."""
    res = []
    for lev in levels:
        Ncap, Nbulk, Nt = 24 * lev, int(max(200, 12 * L / R)) * lev, 8 * lev
        vals, N = eigen(L, R, alpha, n, Ncap, Nbulk, Nt)
        res.append((vals[1] - vals[0], vals, N))
    return res


if __name__ == "__main__":
    L = 1.0
    print("interval gaps, L = 1:")
    for alpha in (1.0, 4.0, 16.0):
        print(f"  alpha={alpha:5.1f}  G_alpha={gap(alpha):9.4f}  "
              f"G_beta0(n=2)={gap(beta0(2, alpha)):9.4f}  G_beta0(n=3)={gap(beta0(3, alpha)):9.4f}")
    print()
    for n in (2, 3):
        for alpha in (4.0,) if n == 3 else (1.0, 4.0, 16.0):
            Ga, Gb = gap(alpha), gap(beta0(n, alpha))
            print(f"n={n}, alpha={alpha}, L=1:  G_alpha={Ga:.4f}  G_beta0={Gb:.4f}")
            print("   R      gap(fine)   gap(coarse)   (gap-Gb)/R   nodes")
            for R in (0.2, 0.1, 0.05, 0.02, 0.01):
                (g1, v1, N1), (g2, v2, N2) = gap_capsule(L, R, alpha, n)
                print(f"  {R:5.3f}  {g2:10.4f}  {g1:10.4f}  {(g2 - Gb) / R:10.3f}  {N2}")
            print()
