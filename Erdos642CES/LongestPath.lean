/-
Copyright 2026 Alp Albayrak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Erdos642CES.Defs
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

/-!
# The longest path argument

We prove that a graph on `n` vertices in which every cycle has more vertices than chords has at
most `2 (⌊√n⌋ + 1) n` edges (`Erdos642.CES.ncard_edgeSet_le`).

Delete vertices of degree at most `d` one at a time. If this removes every edge, the graph has at
most `d n` edges. Otherwise we reach a graph in which every non-isolated vertex has degree at
least `d`. Take a longest path `x₁ … xₘ` in it and let `xⱼ` be the last neighbour of `x₁`, the pair
being chosen so that `j` is maximal. If `xᵢ` is a neighbour of `x₁`, then
`xᵢ₋₁ … x₁ xᵢ … xₘ` is again a longest path, so by the choice of `j` all neighbours of `xᵢ₋₁` lie
on the cycle `x₁ … xⱼ`. This gives `d` vertices of the cycle all of whose `≥ d` neighbours lie on
the cycle, hence at least `d² / 2` edges among its `j ≤ n` vertices. If `d² ≥ 4n`, at least `j` of
them are chords.
-/

open Finset

namespace Erdos642

namespace CES

variable {V : Type*}

/-- The property is inherited by spanning subgraphs. -/
theorem mono [Finite V] {G H : SimpleGraph V} (h : H ≤ G)
    (hG : CyclesHaveMoreVerticesThanChords G) : CyclesHaveMoreVerticesThanChords H := by
  intro v c hc
  have h1 := hG v (c.mapLe h) (hc.mapLe h)
  have hsub : {e : Sym2 V | c.IsChord e} ⊆ {e | (c.mapLe h).IsChord e} := by
    intro e
    refine Sym2.inductionOn e fun a b he => ?_
    have he' := SimpleGraph.Walk.isChord_sym2Mk.1 he
    change (c.mapLe h).IsChord s(a, b)
    rw [SimpleGraph.Walk.isChord_sym2Mk, SimpleGraph.Walk.edges_mapLe_eq_edges,
      SimpleGraph.Walk.support_mapLe_eq_support]
    exact ⟨h he'.1, he'.2.1, he'.2.2⟩
  have hlen : (c.mapLe h).length = c.length := by
    rw [← SimpleGraph.Walk.length_edges, SimpleGraph.Walk.edges_mapLe_eq_edges,
      SimpleGraph.Walk.length_edges]
  calc {e : Sym2 V | c.IsChord e}.ncard
      ≤ {e | (c.mapLe h).IsChord e}.ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ < (c.mapLe h).length := h1
    _ = c.length := hlen

/-- A list whose consecutive entries are adjacent is the support of a walk. -/
theorem exists_walk_of_isChain (G : SimpleGraph V) :
    ∀ (l : List V) (u : V), (u :: l).IsChain G.Adj →
      ∃ (v : V) (p : G.Walk u v), p.support = u :: l
  | [], u, _ => ⟨u, SimpleGraph.Walk.nil, rfl⟩
  | w :: l, u, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨v, p, hp⟩ := exists_walk_of_isChain G l w h.2
    exact ⟨v, SimpleGraph.Walk.cons h.1 p, by rw [SimpleGraph.Walk.support_cons, hp]⟩

/-- The edge closing a path with at least three vertices is not an edge of the path. -/
theorem closing_edge_notMem_edges {G : SimpleGraph V} {x v : V} (p : G.Walk x v)
    (hnd : p.support.Nodup) (hlen : 3 ≤ p.support.length) : s(v, x) ∉ p.edges := by
  cases p with
  | nil => simp at hlen
  | cons h q =>
    intro hmem
    rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnd
    rw [SimpleGraph.Walk.edges_cons, List.mem_cons] at hmem
    rcases hmem with heq | hq
    · rw [Sym2.eq_iff] at heq
      rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact h.ne h2
      · subst h1
        have hq : q.IsPath := (SimpleGraph.Walk.isPath_def q).2 hnd.2
        have h0 : q.length = 0 :=
          SimpleGraph.Walk.length_eq_zero_iff.2 (SimpleGraph.Walk.isPath_iff_nil.1 hq)
        rw [SimpleGraph.Walk.support_cons, List.length_cons, SimpleGraph.Walk.length_support,
          h0] at hlen
        omega
    · exact hnd.1 (q.snd_mem_support_of_mem_edges hq)

section Lists

variable [Fintype V] (G : SimpleGraph V)

/-- A configuration is a path `a ++ b` (as a list of vertices) together with a nonempty initial
segment `a` which is a single vertex or closes up to a cycle. -/
structure Config (a b : List V) : Prop where
  nodup : (a ++ b).Nodup
  chain : (a ++ b).IsChain G.Adj
  ne_nil : a ≠ []
  close : a.length = 1 ∨ ∀ x ∈ a.getLast?, ∀ y ∈ a.head?, G.Adj x y

/-- Configurations are compared first by the length of the path, then by the length of the
initial segment. -/
def weight (a b : List V) : ℕ := (a ++ b).length * (Fintype.card V + 1) + a.length

variable {G}

/-- The path of a configuration has at most `|V|` vertices. -/
theorem Config.length_le {a b : List V} (h : Config G a b) :
    (a ++ b).length ≤ Fintype.card V :=
  h.nodup.length_le_card

/-- The initial segment of a configuration has at most `|V|` vertices. -/
theorem Config.length_left_le {a b : List V} (h : Config G a b) :
    a.length ≤ Fintype.card V := by
  have := h.length_le
  rw [List.length_append] at this
  omega

/-- A longer path has larger weight. -/
theorem weight_lt_of_length_lt {a b a' b' : List V} (ha : a.length ≤ Fintype.card V)
    (h : (a ++ b).length < (a' ++ b').length) : weight a b < weight a' b' := by
  unfold weight
  have h1 : ((a ++ b).length + 1) * (Fintype.card V + 1) ≤
      (a' ++ b').length * (Fintype.card V + 1) := Nat.mul_le_mul_right _ h
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- Among paths of the same length, a longer initial segment has larger weight. -/
theorem weight_lt_of_length_eq {a b a' b' : List V}
    (h : (a ++ b).length = (a' ++ b').length) (h' : a.length < a'.length) :
    weight a b < weight a' b' := by
  unfold weight
  rw [h]
  omega

/-- There is a configuration of maximal weight. -/
theorem exists_max_config (h0 : ∃ a b, Config G a b) :
    ∃ a b, Config G a b ∧ ∀ a' b', Config G a' b' → weight a' b' ≤ weight a b := by
  classical
  obtain ⟨a0, b0, h0⟩ := h0
  have hb : ∀ a b, Config G a b →
      weight a b ≤ Fintype.card V * (Fintype.card V + 1) + Fintype.card V := by
    intro a b h
    unfold weight
    exact Nat.add_le_add (Nat.mul_le_mul_right _ h.length_le) h.length_left_le
  obtain ⟨a, b, hab, hw⟩ :=
    Nat.findGreatest_spec (P := fun m => ∃ a b, Config G a b ∧ weight a b = m)
      (hb a0 b0 h0) ⟨a0, b0, h0, rfl⟩
  refine ⟨a, b, hab, fun a' b' h' => ?_⟩
  rw [hw]
  exact Nat.le_findGreatest (hb a' b' h') ⟨a', b', h', rfl⟩

/-- In a maximal configuration `(a, b)`, if `a'` is a rearrangement of `a` such that `a' ++ b` is
still a path, then every neighbour of the first vertex of `a'` lies in `a`. -/
theorem mem_of_adj_head {a b : List V} (hab : Config G a b)
    (hmax : ∀ a' b', Config G a' b' → weight a' b' ≤ weight a b)
    {a' : List V} (hperm : a'.Perm a) (hchain : (a' ++ b).IsChain G.Adj)
    {z w : V} (hz : z ∈ a'.head?) (hzw : G.Adj z w) : w ∈ a := by
  have hlen : a'.length = a.length := hperm.length_eq
  have hnd : (a' ++ b).Nodup := (hperm.append_right b).nodup_iff.2 hab.nodup
  obtain ⟨t, rfl⟩ : ∃ t, a' = z :: t := by
    cases a' with
    | nil => simp at hz
    | cons c t => exact ⟨t, by simp at hz; rw [hz]⟩
  have h1 : w ∈ z :: t ++ b := by
    by_contra hw
    have hc : Config G [w] (z :: t ++ b) :=
      { nodup := by
          rw [List.singleton_append, List.nodup_cons]
          exact ⟨hw, hnd⟩
        chain := by
          rw [List.singleton_append, List.cons_append, List.isChain_cons_cons]
          exact ⟨hzw.symm, hchain⟩
        ne_nil := by simp
        close := Or.inl rfl }
    have h2 := hmax _ _ hc
    have h3 : weight a b < weight [w] (z :: t ++ b) := by
      apply weight_lt_of_length_lt hab.length_left_le
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      omega
    omega
  have h2 : w ∉ b := by
    intro hwb
    obtain ⟨b₁, b₂, rfl⟩ := List.append_of_mem hwb
    have hc : Config G (z :: t ++ b₁ ++ [w]) b₂ :=
      { nodup := by simpa [List.append_assoc] using hnd
        chain := by simpa [List.append_assoc] using hchain
        ne_nil := by simp
        close := Or.inr (by
          intro x hx y hy
          have hx' : w = x := by
            rw [List.getLast?_concat] at hx
            exact Option.mem_some_iff.1 hx
          have hy' : z = y := by simpa using hy
          rw [← hx', ← hy']
          exact hzw.symm) }
    have h3 := hmax _ _ hc
    have h4 : weight a (b₁ ++ w :: b₂) < weight (z :: t ++ b₁ ++ [w]) b₂ := by
      apply weight_lt_of_length_eq
      · simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
        omega
      · simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
        omega
    omega
  exact hperm.mem_iff.1 ((List.mem_append.1 h1).resolve_right h2)

end Lists

open scoped Classical in
/-- **Key lemma.** If every non-isolated vertex has degree at least `d ≥ 2` and there is an edge,
then some cycle spans at least `d ^ 2 / 2` edges, counted as chords plus cycle edges. -/
theorem exists_isCycle_many_chords [Fintype V] (G : SimpleGraph V) {d : ℕ} (hd : 2 ≤ d)
    (hdeg : ∀ v w, G.Adj v w → d ≤ G.degree v) (hne : ∃ v w, G.Adj v w) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length ≤ Fintype.card V ∧
      d * d ≤ 2 * ({e : Sym2 V | c.IsChord e}.ncard + c.length) := by
  obtain ⟨u₀, v₀, huv⟩ := hne
  -- a maximal configuration
  have h0 : Config G [u₀] [v₀] :=
    { nodup := by simpa using huv.ne
      chain := by simpa using huv
      ne_nil := by simp
      close := Or.inl rfl }
  obtain ⟨a, b, hab, hmax⟩ := exists_max_config ⟨_, _, h0⟩
  obtain ⟨x, t, rfl⟩ : ∃ x t, a = x :: t := by
    cases a with
    | nil => exact absurd rfl hab.ne_nil
    | cons x t => exact ⟨x, t, rfl⟩
  have hnd : (x :: t).Nodup := hab.nodup.of_append_left
  have hch : (x :: t).IsChain G.Adj := hab.chain.left_of_append
  -- the path has at least two vertices, so `x` is not isolated
  have hx : ∃ y, G.Adj x y := by
    have h2 : (t ++ b) ≠ [] := by
      intro h
      have h3 := hmax _ _ h0
      have h4 : weight (x :: t) b < weight [u₀] [v₀] := by
        apply weight_lt_of_length_lt hab.length_left_le
        have : (x :: t ++ b).length = 1 := by rw [List.cons_append, h]; rfl
        rw [this]; simp
      omega
    obtain ⟨y, r, hyr⟩ : ∃ y r, t ++ b = y :: r := by
      cases hh : t ++ b with
      | nil => exact absurd hh h2
      | cons y r => exact ⟨y, r, rfl⟩
    have := hab.chain
    rw [List.cons_append, hyr, List.isChain_cons_cons] at this
    exact ⟨y, this.1⟩
  -- every neighbour of `x` lies in the initial segment
  have hA : ∀ w, G.Adj x w → w ∈ x :: t := fun w hw =>
    mem_of_adj_head hab hmax (List.Perm.refl _) hab.chain (by simp) hw
  have hdx : d ≤ G.degree x := hdeg x _ hx.choose_spec
  have hlen3 : 3 ≤ (x :: t).length := by
    have hsub : G.neighborFinset x ⊆ (x :: t).toFinset.erase x := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      exact Finset.mem_erase.2 ⟨hw.ne', List.mem_toFinset.2 (hA w hw)⟩
    have h1 := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree,
      Finset.card_erase_of_mem (List.mem_toFinset.2 (by simp))] at h1
    have h2 := List.toFinset_card_le (x :: t)
    omega
  have hclose : ∀ p ∈ (x :: t).getLast?, ∀ q ∈ (x :: t).head?, G.Adj p q := by
    rcases hab.close with h | h
    · omega
    · exact h
  -- the predecessors of the neighbours of `x`
  set a := x :: t with ha
  let I : Finset (Fin a.length) :=
    Finset.univ.filter fun i => 1 ≤ (i : ℕ) ∧ G.Adj x (a.get i)
  let f : Fin a.length → V := fun i =>
    a[(i : ℕ) - 1]'(lt_of_le_of_lt (Nat.sub_le _ _) i.isLt)
  have hIcard : d ≤ #I := by
    have hsub : G.neighborFinset x ⊆ I.image fun i => a.get i := by
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.1 (hA w hw)
      refine Finset.mem_image.2 ⟨⟨i, hi⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩, hiw⟩
      · rcases Nat.eq_zero_or_pos i with h0' | h0'
        · subst h0'
          exact absurd hiw hw.ne
        · exact h0'
      · change G.Adj x a[i]
        rw [hiw]; exact hw
    calc d ≤ G.degree x := hdx
      _ = #(G.neighborFinset x) := (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
      _ ≤ #(I.image fun i => a.get i) := Finset.card_le_card hsub
      _ ≤ #I := Finset.card_image_le
  have hfinj : Set.InjOn f (I : Set (Fin a.length)) := by
    intro i hi j hj hij
    have hi1 : 1 ≤ (i : ℕ) := (Finset.mem_filter.1 hi).2.1
    have hj1 : 1 ≤ (j : ℕ) := (Finset.mem_filter.1 hj).2.1
    have := hnd.getElem_inj_iff.1 hij
    exact Fin.ext (by omega)
  have hU : ∀ i ∈ I, d ≤ G.degree (f i) ∧ ∀ w, G.Adj (f i) w → w ∈ a := by
    intro i hi
    have hi1 : 1 ≤ (i : ℕ) := (Finset.mem_filter.1 hi).2.1
    have hxi : G.Adj x a[(i : ℕ)] := (Finset.mem_filter.1 hi).2.2
    have hil : (i : ℕ) < a.length := i.isLt
    constructor
    · have h1 := (List.isChain_iff_getElem.1 hch) ((i : ℕ) - 1) (by omega)
      exact hdeg _ _ h1
    · intro w hw
      have hperm : ((a.take i).reverse ++ a.drop i).Perm a := by
        have h1 : ((a.take i).reverse ++ a.drop i).Perm (a.take i ++ a.drop i) :=
          (List.reverse_perm _).append_right _
        rwa [List.take_append_drop] at h1
      have hsplit : a.take i ++ (a.drop i ++ b) = a ++ b := by
        rw [← List.append_assoc, List.take_append_drop]
      have hchain : ((a.take i).reverse ++ a.drop i ++ b).IsChain G.Adj := by
        rw [List.append_assoc, List.isChain_append]
        have h1 : (a.take i ++ (a.drop i ++ b)).IsChain G.Adj := by rw [hsplit]; exact hab.chain
        refine ⟨?_, h1.right_of_append, ?_⟩
        · rw [List.isChain_reverse]
          exact h1.left_of_append.imp fun _ _ h => h.symm
        · intro p hp q hq
          have hp' : p = x := by
            rw [List.getLast?_reverse, List.head?_take] at hp
            have : (i : ℕ) ≠ 0 := by omega
            simpa [this, ha] using hp.symm
          have hq' : q = a[(i : ℕ)] := by
            rw [List.head?_append, List.head?_drop] at hq
            simpa [List.getElem?_eq_getElem hil] using hq.symm
          rw [hp', hq']
          exact hxi
      have hz : f i ∈ ((a.take i).reverse ++ a.drop i).head? := by
        rw [List.head?_append, List.head?_reverse, List.getLast?_take]
        have h0 : (i : ℕ) ≠ 0 := by omega
        have hlt : (i : ℕ) - 1 < a.length := by omega
        simp [h0, List.getElem?_eq_getElem hlt, f]
      exact mem_of_adj_head hab hmax hperm hchain hz hw
  -- the cycle
  obtain ⟨v, p, hp⟩ := exists_walk_of_isChain G t x hch
  have hpnd : p.support.Nodup := by rw [hp]; exact hnd
  have hplen : 3 ≤ p.support.length := by rw [hp]; exact hlen3
  have hvx : G.Adj v x := by
    have h1 : a.getLast? = some v := by
      rw [ha, ← hp, List.getLast?_eq_some_getLast (SimpleGraph.Walk.support_ne_nil p),
        p.getLast_support]
    have h2 : a.head? = some x := by rw [ha]; rfl
    exact hclose v (by rw [h1]; exact Option.mem_some_iff.2 rfl) x
      (by rw [h2]; exact Option.mem_some_iff.2 rfl)
  refine ⟨v, SimpleGraph.Walk.cons hvx p, ?_, ?_, ?_⟩
  · exact (SimpleGraph.Walk.cons_isCycle_iff p hvx).2
      ⟨(SimpleGraph.Walk.isPath_def p).2 hpnd, closing_edge_notMem_edges p hpnd hplen⟩
  · have h1 := p.length_support
    rw [hp, ← ha] at h1
    have h2 := hnd.length_le_card
    rw [SimpleGraph.Walk.length_cons]
    omega
  · set c := SimpleGraph.Walk.cons hvx p with hc
    have hsupp : ∀ w ∈ a, w ∈ c.support := by
      intro w hw
      rw [hc, SimpleGraph.Walk.support_cons, hp]
      exact List.mem_cons_of_mem _ hw
    -- the graph `G` restricted to the vertices of the cycle
    obtain ⟨K, hK⟩ : ∃ K : SimpleGraph V, ∀ p q, K.Adj p q ↔ G.Adj p q ∧ p ∈ a ∧ q ∈ a := by
      refine ⟨G ⊓ SimpleGraph.fromRel fun p q => p ∈ a ∧ q ∈ a, fun p q => ?_⟩
      simp only [SimpleGraph.inf_adj, SimpleGraph.fromRel_adj]
      constructor
      · rintro ⟨h1, _, h2 | h2⟩
        · exact ⟨h1, h2⟩
        · exact ⟨h1, h2.2, h2.1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h1.ne, Or.inl h2⟩
    -- degree sum in `K`
    have h1 : d * d ≤ 2 * #K.edgeFinset := by
      rw [← K.sum_degrees_eq_twice_card_edges]
      have hdegK : ∀ z ∈ I.image f, d ≤ K.degree z := by
        intro z hz
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hz
        obtain ⟨hd1, hd2⟩ := hU i hi
        have hfa : f i ∈ a := List.getElem_mem _
        have hsub : G.neighborFinset (f i) ⊆ K.neighborFinset (f i) := by
          intro w hw
          rw [SimpleGraph.mem_neighborFinset] at hw ⊢
          exact (hK _ _).2 ⟨hw, hfa, hd2 w hw⟩
        calc d ≤ G.degree (f i) := hd1
          _ = #(G.neighborFinset (f i)) := (SimpleGraph.card_neighborFinset_eq_degree _ _).symm
          _ ≤ #(K.neighborFinset (f i)) := Finset.card_le_card hsub
          _ = K.degree (f i) := SimpleGraph.card_neighborFinset_eq_degree _ _
      calc d * d ≤ #(I.image f) * d := by
            rw [Finset.card_image_of_injOn hfinj]
            exact Nat.mul_le_mul_right _ hIcard
        _ = #(I.image f) • d := (smul_eq_mul _ _).symm
        _ ≤ ∑ z ∈ I.image f, K.degree z := Finset.card_nsmul_le_sum _ _ _ hdegK
        _ ≤ ∑ z, K.degree z := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    -- every edge of `K` is a chord or an edge of the cycle
    have h2 : #K.edgeFinset ≤ {e : Sym2 V | c.IsChord e}.ncard + c.length := by
      have hsub : (K.edgeFinset : Set (Sym2 V)) ⊆
          {e : Sym2 V | c.IsChord e} ∪ (c.edges.toFinset : Set (Sym2 V)) := by
        intro e
        refine Sym2.inductionOn e fun p q he => ?_
        rw [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hK] at he
        by_cases hmem : s(p, q) ∈ c.edges
        · exact Or.inr (by simpa using hmem)
        · exact Or.inl (SimpleGraph.Walk.isChord_sym2Mk.2
            ⟨he.1, hmem, hsupp p he.2.1, hsupp q he.2.2⟩)
      calc #K.edgeFinset = (K.edgeFinset : Set (Sym2 V)).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ ({e : Sym2 V | c.IsChord e} ∪ (c.edges.toFinset : Set (Sym2 V))).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ {e : Sym2 V | c.IsChord e}.ncard + (c.edges.toFinset : Set (Sym2 V)).ncard :=
            Set.ncard_union_le _ _
        _ = {e : Sym2 V | c.IsChord e}.ncard + #c.edges.toFinset := by
            rw [Set.ncard_coe_finset]
        _ ≤ {e : Sym2 V | c.IsChord e}.ncard + c.length := by
            have := List.toFinset_card_le c.edges
            rw [SimpleGraph.Walk.length_edges] at this
            omega
    omega

open scoped Classical in
/-- A graph in which every cycle has more vertices than chords has at most `d` edges per
non-isolated vertex, as soon as `d ^ 2 ≥ 4 |V|`. -/
theorem ncard_edgeSet_le_mul [Fintype V] {d : ℕ} (hd : 2 ≤ d)
    (hdn : 4 * Fintype.card V ≤ d * d) :
    ∀ (k : ℕ) (G : SimpleGraph V), CyclesHaveMoreVerticesThanChords G →
      {v | ∃ w, G.Adj v w}.ncard ≤ k → G.edgeSet.ncard ≤ d * k := by
  have hnoedge : ∀ G : SimpleGraph V, (¬ ∃ v w, G.Adj v w) → G.edgeSet.ncard = 0 := by
    intro G hG
    have : G.edgeSet = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro e
      refine Sym2.inductionOn e fun p q he => ?_
      exact hG ⟨p, q, he⟩
    rw [this, Set.ncard_empty]
  intro k
  induction k with
  | zero =>
    intro G _ hk
    rw [hnoedge G, Nat.mul_zero]
    rintro ⟨v, w, hvw⟩
    have h0 : {v | ∃ w, G.Adj v w} = ∅ :=
      (Set.ncard_eq_zero (Set.toFinite _)).1 (Nat.le_zero.1 hk)
    have hv : v ∈ {v | ∃ w, G.Adj v w} := ⟨w, hvw⟩
    rw [h0] at hv
    exact hv
  | succ k ih =>
    intro G hG hk
    by_cases hlow : ∃ v, 0 < G.degree v ∧ G.degree v ≤ d
    · obtain ⟨v, hv0, hvd⟩ := hlow
      have hG' : CyclesHaveMoreVerticesThanChords (G.deleteIncidenceSet v) :=
        mono (G.deleteIncidenceSet_le v) hG
      have hvmem : v ∈ {v | ∃ w, G.Adj v w} := (G.degree_pos_iff_exists_adj v).1 hv0
      have hk' : {u | ∃ w, (G.deleteIncidenceSet v).Adj u w}.ncard ≤ k := by
        have hsub : {u | ∃ w, (G.deleteIncidenceSet v).Adj u w} ⊆
            {u | ∃ w, G.Adj u w} \ {v} := by
          rintro u ⟨w, hw⟩
          rw [SimpleGraph.deleteIncidenceSet_adj] at hw
          exact ⟨⟨w, hw.1⟩, hw.2.1⟩
        have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_sdiff_singleton_of_mem hvmem] at h1
        omega
      have h2 := ih _ hG' hk'
      have h3 : (G.deleteIncidenceSet v).edgeSet.ncard = G.edgeSet.ncard - G.degree v := by
        have := G.card_edgeFinset_deleteIncidenceSet v
        simpa only [SimpleGraph.edgeFinset, ← Set.ncard_eq_toFinset_card'] using this
      rw [h3] at h2
      rw [Nat.mul_succ]
      omega
    · by_cases hE : ∃ v w, G.Adj v w
      · have hdeg : ∀ v w, G.Adj v w → d ≤ G.degree v := by
          intro v w hvw
          by_contra hlt
          exact hlow ⟨v, (G.degree_pos_iff_exists_adj v).2 ⟨w, hvw⟩, by omega⟩
        obtain ⟨v, c, hc, hlen, hch⟩ := exists_isCycle_many_chords G hd hdeg hE
        have := hG v c hc
        omega
      · rw [hnoedge G hE]
        exact Nat.zero_le _

/-- A graph on `n` vertices in which every cycle has more vertices than chords has at most
`2 (⌊√n⌋ + 1) n` edges. -/
theorem ncard_edgeSet_le (n : ℕ) (G : SimpleGraph (Fin n))
    (hG : CyclesHaveMoreVerticesThanChords G) :
    G.edgeSet.ncard ≤ 2 * (Nat.sqrt n + 1) * n := by
  have hd : 2 ≤ 2 * (Nat.sqrt n + 1) := by omega
  have hdn : 4 * Fintype.card (Fin n) ≤ 2 * (Nat.sqrt n + 1) * (2 * (Nat.sqrt n + 1)) := by
    have h1 := Nat.lt_succ_sqrt n
    rw [Fintype.card_fin, Nat.mul_mul_mul_comm]
    simp only [Nat.succ_eq_add_one] at h1
    omega
  have hk : {v | ∃ w, G.Adj v w}.ncard ≤ n := by
    have := Set.ncard_le_ncard (Set.subset_univ {v | ∃ w, G.Adj v w}) (Set.toFinite _)
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  exact ncard_edgeSet_le_mul hd hdn n G hG hk

end CES

end Erdos642
