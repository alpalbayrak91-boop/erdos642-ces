/-
Copyright 2026 Alp Albayrak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Erdos642CES

@[expose] public section

/-!
# Erdős Problem 642: the Chen–Erdős–Staton bound, proved

The statements are those of `Challenge.lean`; the proofs are in `Erdos642CES`.
-/

open Filter

namespace Erdos642

/-- **Explicit form of the Chen–Erdős–Staton bound.** A graph on `n` vertices in which every
cycle has more vertices than chords has at most $2(\lfloor\sqrt n\rfloor + 1)n$ edges. -/
theorem maxEdges_le_two_mul_sqrt_succ_mul (n : ℕ) : maxEdges n ≤ 2 * (Nat.sqrt n + 1) * n :=
  CES.maxEdges_le n

/-- **Chen, Erdős, and Staton**: $f(n) \ll n^{3/2}$.

This is `Erdos642.erdos_642.variants.upper_bound_n_pow_three_halves` of
`google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/642.lean`), a solved
variant of Erdős Problem 642, which asks whether $f(n) \ll n$. -/
theorem erdos_642.variants.upper_bound_n_pow_three_halves :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) :=
  CES.isBigO_maxEdges

end Erdos642
