/-
Copyright 2026 Alp Albayrak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Erdos642CES.LongestPath
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-!
# The Chen–Erdős–Staton bound for Erdős Problem 642
-/

open Filter

namespace Erdos642

namespace CES

/-- $f(n) \le 2(\lfloor\sqrt n\rfloor + 1)n$. -/
theorem maxEdges_le (n : ℕ) : maxEdges n ≤ 2 * (Nat.sqrt n + 1) * n := by
  classical
  unfold maxEdges
  exact Finset.sup_le fun G hG => ncard_edgeSet_le n G (Finset.mem_filter.1 hG).2

/-- $f(n) \ll n^{3/2}$. -/
theorem isBigO_maxEdges :
    (fun n : ℕ => (maxEdges n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ (3 / 2 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 4 (Eventually.of_forall fun n => ?_)
  have h := maxEdges_le n
  have h1 : (Nat.sqrt n : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h3 : (n : ℝ) ^ (3 / 2 : ℝ) = n * Real.sqrt n := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add_of_nonneg hn0 zero_le_one (by norm_num), Real.rpow_one]
  have h4 : (maxEdges n : ℝ) ≤ 2 * ((Nat.sqrt n : ℝ) + 1) * n := by exact_mod_cast h
  rw [Real.norm_natCast, Real.norm_of_nonneg (Real.rpow_nonneg hn0 _), h3]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa using h4
  · have h2 : (1 : ℝ) ≤ Real.sqrt n := by
      rw [Real.one_le_sqrt]
      exact_mod_cast hn
    nlinarith [mul_le_mul_of_nonneg_right h1 hn0, mul_le_mul_of_nonneg_right h2 hn0]

end CES

end Erdos642
