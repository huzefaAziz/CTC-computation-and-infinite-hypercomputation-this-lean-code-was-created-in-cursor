"""
A closed timelike curve as an *untrusted prover* in front of a *trusted checker*.

Python port of CTCProver.lean. Python cannot prove theorems, so each Lean theorem
becomes an executable property that is checked exhaustively: for every candidate-set
size n in a range, and for EVERY possible checker `ok : {0..n-1} -> bool` (2**n of them).

A real CTC would find a witness in one checker pass. On an ordinary computer the
"fixed point" has to be found by brute force, which is what `consistent_histories`
and `ctc_prover` do here. The CTC is simulated, not realized.
"""

from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Callable, Generic, Optional, TypeVar

# --------------------------------------------------------------------------- #
# Part 1: CTC fixed-point search                                              #
# --------------------------------------------------------------------------- #

Checker = Callable[[int], bool]


def step(n: int, ok: Checker, x: int) -> int:
    """One pass around the loop: keep a valid candidate, else pass the next one."""
    return x if ok(x) else (x + 1) % n


def consistent(n: int, ok: Checker, x: int) -> bool:
    """A history is consistent iff what exits the loop equals what entered it."""
    return 0 <= x < n and step(n, ok, x) == x


def consistent_histories(n: int, ok: Checker) -> list[int]:
    """All consistent deterministic histories (brute force stands in for the CTC)."""
    return [x for x in range(n) if consistent(n, ok, x)]


def deutsch_fixed_point(n: int, ok: Checker) -> dict[int, Fraction]:
    """
    Deutsch's probabilistic consistency condition for the classical loop: a
    distribution over candidates that `step` maps to itself. `step` is a
    deterministic map, so the recurrent states are its cycles. Take the uniform
    mixture over all recurrent states:
      * witnesses exist -> the recurrent states are exactly the witnesses;
      * none exist      -> the loop is one n-cycle, so the whole candidate set.
    """
    recurrent = set()
    for start in range(n):
        x = start
        for _ in range(n):  # after n steps we are on a cycle
            x = step(n, ok, x)
        y = x
        while True:  # walk the cycle, collecting its states
            recurrent.add(y)
            y = step(n, ok, y)
            if y == x:
                break
    p = Fraction(1, len(recurrent))
    return {x: p for x in sorted(recurrent)}


def pushforward(n: int, ok: Checker, dist: dict[int, Fraction]) -> dict[int, Fraction]:
    out: dict[int, Fraction] = {}
    for x, p in dist.items():
        y = step(n, ok, x)
        out[y] = out.get(y, Fraction(0)) + p
    return out


# --------------------------------------------------------------------------- #
# Part 2: untrusted prover, trusted checker                                    #
# --------------------------------------------------------------------------- #

S = TypeVar("S")  # statements
P = TypeVar("P")  # proof objects


@dataclass(frozen=True)
class FormalSystem(Generic[S, P]):
    """`check` is the trusted kernel. `sound` is a *claim* about it (Lean proves it)."""
    check: Callable[[P, S], bool]
    holds: Callable[[S], bool]


Prover = Callable[[S], Optional[P]]


def certify(sys_: FormalSystem[S, P], prover: Prover, s: S) -> Optional[P]:
    """Run any prover, but only believe what the kernel accepts."""
    p = prover(s)
    if p is None:
        return None
    return p if sys_.check(p, s) else None


def ctc_prover(sys_: FormalSystem[S, P], n: int, enc: Callable[[int], P]) -> Prover:
    """
    The CTC device as a prover: hand back the contents of *a* consistent history of the
    search loop, if one exists. (Lean: `Classical.choose`. Here: brute force.)
    """
    def prover(s: S) -> Optional[P]:
        ok = lambda i: sys_.check(enc(i), s)
        hist = consistent_histories(n, ok)
        return enc(hist[0]) if hist else None
    return prover


# --------------------------------------------------------------------------- #
# Exhaustive checks of the Lean theorems                                       #
# --------------------------------------------------------------------------- #

def all_checkers(n: int):
    for bits in product([False, True], repeat=n):
        yield (lambda x, b=bits: b[x])


def check_theorems(max_n: int = 8) -> None:
    for n in range(2, max_n + 1):
        for ok in all_checkers(n):
            witnesses = [x for x in range(n) if ok(x)]
            hist = consistent_histories(n, ok)

            # witness_consistent / consistent_is_witness / consistent_exists_iff
            assert set(hist) == set(witnesses)
            assert bool(hist) == bool(witnesses)

            # step_lt: the loop never leaves the candidate set
            assert all(0 <= step(n, ok, x) < n for x in range(n))

            if not witnesses:
                # no_witness_no_history: grandfather paradox
                assert hist == []
                # step_injective_of_no_witness: the loop is a permutation
                images = [step(n, ok, x) for x in range(n)]
                assert len(set(images)) == n
                # ...so the uniform distribution is Deutsch's consistent state
                d = deutsch_fixed_point(n, ok)
                assert d == {x: Fraction(1, n) for x in range(n)}

            # the Deutsch fixed point really is fixed, in every case
            d = deutsch_fixed_point(n, ok)
            assert pushforward(n, ok, d) == d
            assert sum(d.values()) == 1
            # and when proofs exist, it is supported only on valid ones
            if witnesses:
                assert all(ok(x) for x in d)


def check_pipeline_soundness() -> None:
    """certify_sound / ctc_pipeline_sound on a toy system, with deliberately bad provers."""
    toy = FormalSystem[int, int](
        check=lambda r, N: r * r == N,                       # kernel: r is a square root of N
        holds=lambda N: any(r * r == N for r in range(N + 1)),
    )
    provers: list[Prover] = [
        ctc_prover(toy, 64, lambda i: i),                    # the CTC device
        lambda N: 0,                                         # a buggy prover
        lambda N: N + 1,                                     # a lying prover
        lambda N: None,                                      # a silent prover
    ]
    for prv in provers:
        for N in range(0, 200):
            proof = certify(toy, prv, N)
            if proof is not None:
                assert toy.holds(N), (N, proof)              # soundness, whoever the prover is

    # certify_complete / ctcProver_complete: if a proof sits among the first n candidates,
    # the CTC pipeline finds one.
    dev = ctc_prover(toy, 64, lambda i: i)
    for N in range(0, 200):
        has_proof = any(r * r == N for r in range(64))
        assert (certify(toy, dev, N) is not None) == has_proof


# --------------------------------------------------------------------------- #
# Demo                                                                         #
# --------------------------------------------------------------------------- #

def demo() -> None:
    n = 20
    ok49 = lambda x: x * x == 49
    ok50 = lambda x: x * x == 50

    print("Checker: x*x == 49, candidates 0..19")
    print("  step(7)             =", step(n, ok49, 7), "(fixed, so 7 is a consistent history)")
    print("  consistent histories =", consistent_histories(n, ok49))
    print("  Deutsch fixed point  =", {k: str(v) for k, v in deutsch_fixed_point(n, ok49).items()})

    print("\nChecker: x*x == 50 (no solution)")
    print("  step(7)             =", step(n, ok50, 7), "(moves on, so 7 is not consistent)")
    print("  consistent histories =", consistent_histories(n, ok50), "(grandfather paradox)")
    d = deutsch_fixed_point(n, ok50)
    print("  Deutsch fixed point  = uniform over", len(d), "candidates, each", next(iter(d.values())))

    toy = FormalSystem[int, int](check=lambda r, N: r * r == N, holds=lambda N: True)
    dev = ctc_prover(toy, 64, lambda i: i)
    print("\nCTC prover through the kernel:")
    for N in (49, 50, 3481):
        print(f"  is {N} a perfect square? certified proof = {certify(toy, dev, N)}")


if __name__ == "__main__":
    check_theorems()
    check_pipeline_soundness()
    print("All exhaustive checks passed (n = 2..8, every checker function).\n")
    demo()
