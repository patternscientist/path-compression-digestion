#!/usr/bin/env python3
"""
Finite sanity checks for the path-compression proof packet.

This script does NOT prove the theorem. It only stress-tests small computable
cases for off-by-one and normalization mistakes in the J/R/A definitions used in
the proof note.
"""

from __future__ import annotations

from functools import lru_cache
from math import ceil, log2


MAX_R = 100000


@lru_cache(maxsize=None)
def J(k: int, r: int) -> int:
    """The packet J hierarchy: J_0(r)=ceil((r-1)/2), J_{k+1}=J_k^diamond."""
    if r < 0:
        raise ValueError("r must be nonnegative")
    if k == 0:
        return ceil((r - 1) / 2)
    return diamond(k - 1, r)


@lru_cache(maxsize=None)
def diamond(k: int, r: int) -> int:
    """h = J_k^diamond as in the proof note's recursive definition."""
    g = J(k, r)
    if g <= 1:
        return g
    return 1 + diamond(k, ceil(log2(g)))


def R(k: int, t: int, max_r: int = MAX_R) -> tuple[int, bool]:
    """
    Finite search for R_k(t).

    Returns (best, hit_boundary). If hit_boundary is true, the true R_k(t) is
    at least max_r and this finite routine should not be used as an exact value.
    """
    best = 0
    for r in range(max_r + 1):
        if J(k, r) <= t:
            best = r
        elif r > best:
            # J_k is monotone in all intended cases, so once it exceeds t after
            # the current best, no larger r can return to <=t.
            break
    return best, best == max_r


@lru_cache(maxsize=None)
def A_bounded(i: int, x: int, cap: int = MAX_R) -> int:
    """Packet Ackermann normalization, capped at cap+1."""
    if i == 0:
        return min(2 * x, cap + 1)
    if x == 0:
        return 0
    if x == 1:
        return 2

    y = A_bounded(i, x - 1, cap)
    if y > cap:
        return cap + 1
    return min(A_bounded(i - 1, y, cap), cap + 1)


def check_J_monotonicity() -> None:
    for k in range(4):
        prev = J(k, 0)
        for r in range(1, 500):
            cur = J(k, r)
            assert prev <= cur, (k, r, prev, cur)
            prev = cur


def check_R_monotonicity() -> None:
    for k in range(3):
        prev, prev_boundary = R(k, 0)
        for t in range(1, 3):
            cur, cur_boundary = R(k, t)
            if prev_boundary or cur_boundary:
                continue
            assert prev <= cur, (k, t, prev, cur)
            prev, prev_boundary = cur, cur_boundary


def check_threshold_step_small_cases() -> None:
    # Small exact cases where the finite R search does not hit the boundary.
    cases = [(0, 1), (0, 2)]
    for k, t in cases:
        left, left_boundary = R(k + 1, t + 1)
        inner, inner_boundary = R(k + 1, t)
        if left_boundary or inner_boundary or inner > 20:
            continue
        right, right_boundary = R(k, 2 ** inner)
        if right_boundary:
            continue
        assert left >= right, (k, t, left, right, inner)


def check_main_comparison_small_cases() -> None:
    # The smallest nontrivial published comparison instance:
    # R_{1+1}(1) >= A(1,4).
    z, Q = 1, 1
    target = A_bounded(z, 4 * Q)
    left, boundary = R(z + 1, Q)
    assert not boundary, "finite search unexpectedly hit boundary for z=1,Q=1"
    assert left >= target, (z, Q, left, target)


def main() -> None:
    check_J_monotonicity()
    check_R_monotonicity()
    check_threshold_step_small_cases()
    check_main_comparison_small_cases()
    print("ok: finite J/R/A sanity checks passed")


if __name__ == "__main__":
    main()
