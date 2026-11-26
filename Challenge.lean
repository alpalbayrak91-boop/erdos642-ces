/-
Copyright 2026 Alp Albayrak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# Erdős Problem 642: the Chen–Erdős–Staton bound

Let $f(n)$ be the maximal number of edges of a graph on $n$ vertices in which every cycle has
more vertices than chords. A chord of a cycle is an edge of the graph joining two vertices of the
cycle that are not consecutive on it. Hamburger and Szegedy asked whether $f(n) \ll n$
([erdosproblems.com/642](https://www.erdosproblems.com/642)); this is open.

Chen, Erdős, and Staton proved $f(n) \ll n^{3/2}$. This file states that bound, in the form used
by `google-deepmind/formal-conjectures`, together with an explicit version.

The two definitions below are copied verbatim from
`FormalConjectures/ErdosProblems/642.lean`. They use only Mathlib notions: `SimpleGraph.Walk`,
`SimpleGraph.Walk.IsCycle`, and `SimpleGraph.Walk.IsChord`.
-/

open Filter

namespace Erdos642

/-- Every cycle of the graph `G` has more vertices than chords.

A cycle is a closed walk `c` with `c.IsCycle`. It has `c.length` vertices. A chord of `c` is an
edge of `G` between two vertices of `c` that is not an edge of `c`
(`SimpleGraph.Walk.IsChord`). -/
def CyclesHaveMoreVerticesThanChords {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (c : G.Walk v v), c.IsCycle → {e : Sym2 V | c.IsChord e}.ncard < c.length

open scoped Classical in
/-- The maximal number $f(n)$ of edges of a graph on `n` vertices in which every cycle has more
vertices than chords. There are finitely many graphs on `Fin n`, so the supremum is a maximum. -/
noncomputable def maxEdges (n : ℕ) : ℕ :=
  (Finset.univ.filter fun G : SimpleGraph (Fin n) => CyclesHaveMoreVerticesThanChords G).sup
    fun G => G.edgeSet.ncard

/-- **Explicit form of the Chen–Erdős–Staton bound.** A graph on `n` vertices in which every
cycle has more vertices than chords has at most $2(\lfloor\sqrt n\rfloor + 1)n$ edges. -/
theorem maxEdges_le_two_mul_sqrt_succ_mul (n : ℕ) : maxEdges n ≤ 2 * (Nat.sqrt n + 1) * n := by
  sorry

/-- **Chen, Erdős, and Staton**: $f(n) \ll n^{3/2}$.

This is `Erdos642.erdos_642.variants.upper_bound_n_pow_three_halves` of
`google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/642.lean`), a solved
variant of Erdős Problem 642, which asks whether $f(n) \ll n$. -/
theorem erdos_642.variants.upper_bound_n_pow_three_halves :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  sorry

end Erdos642
