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
# Erdős Problem 642: definitions

The definitions are those of `FormalConjectures/ErdosProblems/642.lean` in
`google-deepmind/formal-conjectures`, copied verbatim.
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

end Erdos642
