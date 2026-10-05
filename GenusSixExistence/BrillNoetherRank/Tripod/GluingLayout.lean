import GenusSixExistence.BrillNoetherRank.Tripod.GluingInjective

/-!
# Layouts: the stable paths of a member, cut at marks, as oriented chains

The combinatorial input of `GluingPositivity.exists_pieceLabels` and
`GluingWellDefined.placement_forced`: *the glued paths over a row of `ψ` are its segments between
the marks, with prefix-sum lengths.* This module is generic: a gluing datum `E` over a target `S`,
a core `C : Core m q` with a request `y`, and an injective vertex map `V : Fin m → E.SourceVertex`
(the branch vertices of `E` and the marks placed so far).

* `LabelData E C V y`: a labelling of the surviving edges of `E` by the slots of `C`, constant
  through every surviving vertex of valency two outside the range of `V` (`const`), with the
  incidences of `C` at the vertices `V a` (`inc`), and non-negative target lengths `w` along which
  each label has its requested length (`len`).
* `Layout E C V y`: the same, with each label class written as an oriented chain from `V (tail i)`
  to `V (head i)` (`chain`). A layout gives label data (`Layout.toLabelData`).

The three steps of the gluing are one refinement each (`refineDatum E t`, `subdivide C e`), and
section 2 refines chains (`refineChain`). The forward step (`forward`, section 4) places a
mark at its actual position and refines a layout; the analysis of an arbitrary refinement
(`analyze`, section 5) shows that the position, the labels and the lengths are forced when the
slot is not a loop. Prose: `Research/genus-six-brill-noether-rank.md`, §5.2 (Positivity) and §5.5
(The bijection, "Well defined": this uses that no mark lies on a loop).
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open Utilities.Certificate.ExplicitPotential (Core)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion
open GenusSixExistence.Tripod.Gadget

namespace Chains

/-! ## 1. Label data and layouts -/

section Generic

variable {S : CFGraph} {d : ℕ} (E : GluingDatum S d)

/-- An oriented source edge: an edge, the vertex it is entered by, and the one it is left by. -/
abbrev OEdge := E.SourceEdge × E.SourceVertex × E.SourceVertex

/-- The source length of a source edge under target lengths `w`. -/
def srcLen (w : S.edges → ℚ) (x : E.SourceEdge) : ℚ := w x.1.1 / E.sourceEdgeIndex x

/-- An interior vertex of a chain: surviving valency two, and not one of the named vertices. -/
def Inner {m : ℕ} (V : Fin m → E.SourceVertex) (v : E.SourceVertex) : Prop :=
  nonDanglingValency E v = 2 ∧ v ∉ Set.range V

/-- Consecutive oriented edges of a chain meet at an interior vertex. -/
def Link {m : ℕ} (V : Fin m → E.SourceVertex) (c c' : OEdge E) : Prop :=
  c.2.2 = c'.2.1 ∧ Inner E V c.2.2

/-- A well-formed oriented edge: it survives, and joins its two named vertices, which differ. -/
def Good (c : OEdge E) : Prop :=
  ¬ IsDangling E c.1 ∧ Incident E c.1 c.2.1 ∧ Incident E c.1 c.2.2 ∧ c.2.1 ≠ c.2.2

variable {m q : ℕ}

open Classical in
/-- **Label data**: the labels of the surviving edges by the slots of `C`, constant through the
interior vertices, with the incidences of `C` at the named vertices and the requested lengths. -/
structure LabelData (C : Core m q) (V : Fin m → E.SourceVertex) (y : Fin q → ℚ) where
  lab : NonDanglingEdge E → Fin q
  w : S.edges → ℚ
  w_nonneg : ∀ e, 0 ≤ w e
  const : ∀ (x x' : NonDanglingEdge E) (v : E.SourceVertex), Incident E x.1 v →
    Incident E x'.1 v → Inner E V v → lab x = lab x'
  inc : ∀ a i, (Finset.univ.filter fun x : NonDanglingEdge E ↦
    Incident E x.1 (V a) ∧ lab x = i).card = coreIncidence C a i
  len : ∀ i, (∑ x : NonDanglingEdge E, if lab x = i then srcLen E w x.1 else 0) = y i

/-- **A layout**: label data whose classes are oriented chains from `V (tail i)` to
`V (head i)`. -/
structure Layout (C : Core m q) (V : Fin m → E.SourceVertex) (y : Fin q → ℚ) where
  lab : NonDanglingEdge E → Fin q
  w : S.edges → ℚ
  w_nonneg : ∀ e, 0 ≤ w e
  chain : Fin q → List (OEdge E)
  good : ∀ i, ∀ c ∈ chain i, Good E c
  mem : ∀ (x : NonDanglingEdge E) i, x.1 ∈ (chain i).map Prod.fst ↔ lab x = i
  nodup : ∀ i, ((chain i).map Prod.fst).Nodup
  link : ∀ i, (chain i).IsChain (Link E V)
  ne_nil : ∀ i, chain i ≠ []
  head : ∀ i, ((chain i).head (ne_nil i)).2.1 = V (C.tail i)
  last : ∀ i, ((chain i).getLast (ne_nil i)).2.2 = V (C.head i)
  sum : ∀ i, ((chain i).map fun c ↦ srcLen E w c.1).sum = y i

variable {E}

theorem Good.eq_or_eq {c : OEdge E} (h : Good E c) {v : E.SourceVertex}
    (hv : Incident E c.1 v) : v = c.2.1 ∨ v = c.2.2 := by
  obtain ⟨-, h1, h2, hne⟩ := h
  unfold Incident at h1 h2 hv
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases hv with hv | hv
  all_goals first
    | exact Or.inl (hv.symm.trans h1)
    | exact Or.inr (hv.symm.trans h2)
    | exact absurd (h1.symm.trans h2) hne

theorem Good.incident_iff {c : OEdge E} (h : Good E c) (v : E.SourceVertex) :
    Incident E c.1 v ↔ v = c.2.1 ∨ v = c.2.2 := by
  refine ⟨h.eq_or_eq, ?_⟩
  rintro (rfl | rfl)
  · exact h.2.1
  · exact h.2.2.1

variable {C : Core m q} {V : Fin m → E.SourceVertex} {y : Fin q → ℚ}

/-- A sum over a label class is the sum along its chain. -/
theorem Layout.sum_class {M : Type*} [AddCommMonoid M] (L : Layout E C V y) (i : Fin q)
    (f : E.SourceEdge → M) [DecidablePred fun x : NonDanglingEdge E ↦ L.lab x = i] :
    (∑ x : NonDanglingEdge E, if L.lab x = i then f x.1 else 0) =
      ((L.chain i).map fun c ↦ f c.1).sum := by
  classical
  have hmap : ((L.chain i).map fun c ↦ f c.1) = ((L.chain i).map Prod.fst).map f := by
    rw [List.map_map]; rfl
  rw [hmap, ← List.sum_toFinset f (L.nodup i), ← Finset.sum_filter]
  have hnd : ∀ e ∈ ((L.chain i).map Prod.fst).toFinset, ¬ IsDangling E e := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact (L.good i c hc).1
  refine Finset.sum_bij' (fun x _ ↦ x.1) (fun e he ↦ ⟨e, hnd e he⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact List.mem_toFinset.mpr ((L.mem x i).mpr (Finset.mem_filter.mp hx).2)
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (L.mem _ i).mp (List.mem_toFinset.mp he)⟩
  · intro x _
    rfl
  · intro e _
    rfl
  · intro x _
    rfl

/-- **The incidences along a chain** at a named vertex: only the two ends count. -/
theorem sum_incident_chain (l : List (OEdge E)) (hl : l.IsChain (Link E V))
    (hg : ∀ c ∈ l, Good E c) (hne : l ≠ []) {w : E.SourceVertex} (hw : w ∈ Set.range V)
    {u v : E.SourceVertex} (hu : (l.head hne).2.1 = u) (hv : (l.getLast hne).2.2 = v) :
    (l.map fun c ↦ if Incident E c.1 w then (1 : ℕ) else 0).sum =
      (if u = w then 1 else 0) + (if v = w then 1 else 0) := by
  induction l generalizing u with
  | nil => exact absurd rfl hne
  | cons c l ih =>
    have hc := hg c (List.mem_cons_self ..)
    have key : Incident E c.1 w ↔ c.2.1 = w ∨ c.2.2 = w :=
      (hc.incident_iff w).trans (or_congr eq_comm eq_comm)
    simp only [List.head_cons] at hu
    subst hu
    cases l with
    | nil =>
      simp only [List.getLast_singleton] at hv
      subst hv
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      have hne' := hc.2.2.2
      by_cases h1 : c.2.1 = w
      · have h2 : c.2.2 ≠ w := fun h ↦ hne' (h1.trans h.symm)
        rw [if_pos (key.mpr (Or.inl h1)), if_pos h1, if_neg h2]
      · by_cases h2 : c.2.2 = w
        · rw [if_pos (key.mpr (Or.inr h2)), if_neg h1, if_pos h2]
        · rw [if_neg (fun h ↦ (key.mp h).elim h1 h2), if_neg h1, if_neg h2]
    | cons c' l =>
      rw [List.isChain_cons_cons] at hl
      obtain ⟨⟨hlink, hin⟩, hl'⟩ := hl
      have hvw : c.2.2 ≠ w := fun h ↦ hin.2 (h ▸ hw)
      simp only [List.getLast_cons_cons] at hv
      have ih' := ih hl' (fun c'' h ↦ hg c'' (List.mem_cons_of_mem _ h)) (List.cons_ne_nil _ _)
        (u := c'.2.1) rfl hv
      rw [List.map_cons, List.sum_cons, ih']
      rw [if_neg (show c'.2.1 ≠ w from hlink ▸ hvw), zero_add]
      congr 1
      by_cases h1 : c.2.1 = w
      · rw [if_pos (key.mpr (Or.inl h1)), if_pos h1]
      · rw [if_neg (fun h ↦ (key.mp h).elim h1 hvw), if_neg h1]

/-- **The other edge at an interior vertex** of a chain whose ends are named vertices. -/
theorem exists_other (l : List (OEdge E)) (hl : l.IsChain (Link E V)) (hg : ∀ c ∈ l, Good E c)
    (hne : l ≠ []) (hh : (l.head hne).2.1 ∈ Set.range V)
    (hlast : (l.getLast hne).2.2 ∈ Set.range V) {j : ℕ} (hj : j < l.length) {v : E.SourceVertex}
    (hv : Incident E l[j].1 v) (hin : Inner E V v) :
    ∃ k, ∃ hk : k < l.length, k ≠ j ∧ Incident E l[k].1 v := by
  rcases (hg _ (List.getElem_mem hj)).eq_or_eq hv with rfl | rfl
  · by_cases hj0 : j = 0
    · subst hj0
      exfalso
      apply hin.2
      rw [← List.head_eq_getElem hne]
      exact hh
    · have hj1 : j - 1 + 1 < l.length := by omega
      have hlk := (hl.getElem (j - 1) hj1).1
      have he : j - 1 + 1 = j := by omega
      refine ⟨j - 1, by omega, by omega, ?_⟩
      have hgk := hg _ (List.getElem_mem (show j - 1 < l.length by omega))
      have : l[j - 1].2.2 = l[j].2.1 := by
        rw [hlk]
        simp only [he]
      rw [← this]
      exact hgk.2.2.1
  · by_cases hjl : j + 1 < l.length
    · have hlk := (hl.getElem j hjl).1
      refine ⟨j + 1, hjl, by omega, ?_⟩
      rw [hlk]
      exact (hg _ (List.getElem_mem hjl)).2.1
    · exfalso
      apply hin.2
      have hjeq : j = l.length - 1 := by omega
      have : l[j] = l.getLast hne := by
        rw [List.getLast_eq_getElem]
        simp only [hjeq]
      rw [this]
      exact hlast

/-- **A layout gives label data.** -/
theorem Layout.const (L : Layout E C V y) (x x' : NonDanglingEdge E) (v : E.SourceVertex)
    (hx : Incident E x.1 v) (hx' : Incident E x'.1 v) (hin : Inner E V v) :
    L.lab x = L.lab x' := by
  set i := L.lab x with hi
  have hmem := (L.mem x i).mpr rfl
  obtain ⟨c, hc, hcx⟩ := List.mem_map.mp hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  have hvj : Incident E (L.chain i)[j].1 v := hcx ▸ hx
  obtain ⟨k, hk, hkj, hvk⟩ := exists_other (L.chain i) (L.link i) (L.good i) (L.ne_nil i)
    ⟨_, (L.head i).symm⟩ ⟨_, (L.last i).symm⟩ hj hvj hin
  have hkne : (L.chain i)[k].1 ≠ x.1 := by
    intro h
    have hnd := L.nodup i
    have h' : ((L.chain i).map Prod.fst)[k]'(by simpa using hk) =
        ((L.chain i).map Prod.fst)[j]'(by simpa using hj) := by
      simp only [List.getElem_map]
      rw [h, hcx]
    exact hkj ((List.Nodup.getElem_inj_iff hnd).mp h')
  by_cases hxx : x'.1 = x.1
  · rw [show x' = x from Subtype.ext hxx]
  · obtain ⟨o, -, ho⟩ := exists_unique_other_of_nonDanglingValency_eq_two E hin.1 x.2 hx
    have h1 := ho _ ⟨hkne, (L.good i _ (List.getElem_mem hk)).1, hvk⟩
    have h2 := ho _ ⟨hxx, x'.2, hx'⟩
    have hx'mem : x'.1 ∈ (L.chain i).map Prod.fst := by
      rw [h2, ← h1]
      exact List.mem_map_of_mem (List.getElem_mem hk)
    exact ((L.mem x' i).mp hx'mem).symm

theorem Layout.inc (L : Layout E C V y) (hV : Function.Injective V) (a : Fin m) (i : Fin q)
    [DecidablePred fun x : NonDanglingEdge E ↦ Incident E x.1 (V a) ∧ L.lab x = i] :
    (Finset.univ.filter fun x : NonDanglingEdge E ↦ Incident E x.1 (V a) ∧ L.lab x = i).card =
      coreIncidence C a i := by
  classical
  have h2 := L.sum_class i (fun e ↦ if Incident E e (V a) then (1 : ℕ) else 0)
  rw [Finset.card_filter]
  refine Eq.trans ?_ (h2.trans ?_)
  · refine Finset.sum_congr rfl fun x _ ↦ ?_
    by_cases h : L.lab x = i <;> simp [h]
  · rw [sum_incident_chain _ (L.link i) (L.good i) (L.ne_nil i) ⟨a, rfl⟩ (L.head i) (L.last i)]
    unfold coreIncidence
    simp only [hV.eq_iff]

theorem Layout.len (L : Layout E C V y) (i : Fin q) :
    (∑ x : NonDanglingEdge E, if L.lab x = i then srcLen E L.w x.1 else 0) = y i := by
  classical
  rw [L.sum_class i, L.sum i]

/-- **The label data of a layout.** -/
def Layout.toLabelData (L : Layout E C V y) (hV : Function.Injective V) : LabelData E C V y where
  lab := L.lab
  w := L.w
  w_nonneg := L.w_nonneg
  const := L.const
  inc a i := by classical exact L.inc hV a i
  len := L.len

theorem Layout.exists_lab (L : Layout E C V y) (i : Fin q) : ∃ x, L.lab x = i := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (L.ne_nil i)
  exact ⟨⟨c.1, (L.good i c hc).1⟩, (L.mem _ i).mp (List.mem_map_of_mem hc)⟩

end Generic

/-! ## 2. Refining chains at a target edge -/

section RefineChains

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} (t : S.edges)

theorem Good.ends_cases {c : OEdge E} (h : Good E c) :
    (c.2.1 = (E.sourceEnds c.1).1 ∧ c.2.2 = (E.sourceEnds c.1).2) ∨
      (c.2.1 = (E.sourceEnds c.1).2 ∧ c.2.2 = (E.sourceEnds c.1).1) := by
  obtain ⟨-, h1, h2, hne⟩ := h
  unfold Incident at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.symm.trans h2) hne
  · exact Or.inl ⟨h1.symm, h2.symm⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩
  · exact absurd (h1.symm.trans h2) hne

theorem piece_val (u : E.SourceVertex) (f : E.SourceEdge) :
    (Refine.piece E t u f).1 = (pieceT t u.1.1 f.1.1, f.1.2) := rfl

theorem pieceT_of_ne {w : S.V} {e : S.edges} (h : e ≠ t) :
    pieceT t w e = subdivOcc S t (some e) := by
  unfold pieceT
  rw [if_neg (fun h' ↦ h h'.1)]

theorem pieceT_fst : pieceT t (t : S.V × S.V).1 t = subdivOcc S t (some t) := by
  unfold pieceT
  rw [if_neg (fun h' ↦ fst_ne_snd t h'.2.symm)]

theorem pieceT_snd : pieceT t (t : S.V × S.V).2 t = subdivOcc S t none := by
  unfold pieceT
  rw [if_pos ⟨rfl, rfl⟩]

/-- The piece of an edge not over `t` does not depend on the end. -/
theorem piece_eq_of_ne {f : E.SourceEdge} (h : f.1.1 ≠ t) (u v : E.SourceVertex) :
    Refine.piece E t u f = Refine.piece E t v f := by
  apply Subtype.ext
  rw [piece_val, piece_val, pieceT_of_ne t h, pieceT_of_ne t h]

/-- The two pieces of an edge over `t` at its two ends are different. -/
theorem piece_ne_of_good {c : OEdge E} (hc : Good E c) (h : c.1.1.1 = t) :
    Refine.piece E t c.2.1 c.1 ≠ Refine.piece E t c.2.2 c.1 := by
  intro heq
  have h1 := congrArg (fun y : (refineDatum E t).SourceEdge ↦ y.1.1) heq
  simp only [piece_val] at h1
  rw [h] at h1
  rcases hc.ends_cases with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hu, hv] at h1
    change pieceT t (c.1.1.1 : S.V × S.V).1 t = pieceT t (c.1.1.1 : S.V × S.V).2 t at h1
    rw [h, pieceT_fst, pieceT_snd] at h1
    exact absurd ((subdivOcc S t).injective h1) (by simp)
  · rw [hu, hv] at h1
    change pieceT t (c.1.1.1 : S.V × S.V).2 t = pieceT t (c.1.1.1 : S.V × S.V).1 t at h1
    rw [h, pieceT_fst, pieceT_snd] at h1
    exact absurd ((subdivOcc S t).injective h1) (by simp)

/-- **The children of an edge** are its pieces at its two ends. -/
theorem eq_piece_of_parentSE {c : OEdge E} (hc : Good E c) {y : (refineDatum E t).SourceEdge}
    (hy : Refine.parentSE E t y = c.1) :
    y = Refine.piece E t c.2.1 c.1 ∨ y = Refine.piece E t c.2.2 c.1 := by
  have hT : parentT t y.1.1 = c.1.1.1 := congrArg (fun f : E.SourceEdge ↦ f.1.1) hy
  have hS : y.1.2 = c.1.1.2 := congrArg (fun f : E.SourceEdge ↦ f.1.2) hy
  by_cases hct : c.1.1.1 = t
  · rcases (parentT_eq_iff t y.1.1 c.1.1.1).mp hT with h1 | ⟨-, h1⟩
    · -- the `some` half
      rcases hc.ends_cases with ⟨hu, -⟩ | ⟨-, hv⟩
      · left
        apply Subtype.ext
        rw [piece_val, hu]
        refine Prod.ext ?_ hS
        change y.1.1 = pieceT t (c.1.1.1 : S.V × S.V).1 c.1.1.1
        rw [h1]
        rw [show c.1.1.1 = t from hct]
        rw [pieceT_fst]
      · right
        apply Subtype.ext
        rw [piece_val, hv]
        refine Prod.ext ?_ hS
        change y.1.1 = pieceT t (c.1.1.1 : S.V × S.V).1 c.1.1.1
        rw [h1]
        rw [show c.1.1.1 = t from hct]
        rw [pieceT_fst]
    · rcases hc.ends_cases with ⟨-, hv⟩ | ⟨hu, -⟩
      · right
        apply Subtype.ext
        rw [piece_val, hv]
        refine Prod.ext ?_ hS
        change y.1.1 = pieceT t (c.1.1.1 : S.V × S.V).2 c.1.1.1
        rw [h1, show c.1.1.1 = t from hct, pieceT_snd]
      · left
        apply Subtype.ext
        rw [piece_val, hu]
        refine Prod.ext ?_ hS
        change y.1.1 = pieceT t (c.1.1.1 : S.V × S.V).2 c.1.1.1
        rw [h1, show c.1.1.1 = t from hct, pieceT_snd]
  · left
    rcases (parentT_eq_iff t y.1.1 c.1.1.1).mp hT with h1 | ⟨h2, -⟩
    · apply Subtype.ext
      rw [piece_val, pieceT_of_ne t hct]
      exact Prod.ext h1 hS
    · exact absurd h2 hct

open Classical in
/-- **The children of an oriented edge** in the refinement at `t`, in order: its piece at the
entry vertex, then (if it lies over `t`) the fresh vertex and its piece at the exit vertex. -/
def refineOE (c : OEdge E) : List (OEdge (refineDatum E t)) :=
  if h : c.1.1.1 = t then
    [(Refine.piece E t c.2.1 c.1, Refine.oldSV E t c.2.1, Refine.freshOf E t c.1 h),
      (Refine.piece E t c.2.2 c.1, Refine.freshOf E t c.1 h, Refine.oldSV E t c.2.2)]
  else [(Refine.piece E t c.2.1 c.1, Refine.oldSV E t c.2.1, Refine.oldSV E t c.2.2)]

/-- The refinement of a chain at `t`. -/
def refineChain (l : List (OEdge E)) : List (OEdge (refineDatum E t)) := l.flatMap (refineOE t)

theorem refineOE_of {c : OEdge E} (h : c.1.1.1 = t) :
    refineOE t c =
      [(Refine.piece E t c.2.1 c.1, Refine.oldSV E t c.2.1, Refine.freshOf E t c.1 h),
        (Refine.piece E t c.2.2 c.1, Refine.freshOf E t c.1 h, Refine.oldSV E t c.2.2)] := by
  unfold refineOE
  rw [dif_pos h]

theorem refineOE_of_ne {c : OEdge E} (h : c.1.1.1 ≠ t) :
    refineOE t c = [(Refine.piece E t c.2.1 c.1, Refine.oldSV E t c.2.1, Refine.oldSV E t c.2.2)] := by
  unfold refineOE
  rw [dif_neg h]

theorem refineOE_ne_nil (c : OEdge E) : refineOE t c ≠ [] := by
  by_cases h : c.1.1.1 = t
  · rw [refineOE_of t h]; simp
  · rw [refineOE_of_ne t h]; simp

theorem head_refineOE (c : OEdge E) : ∀ c' ∈ (refineOE t c).head?, c'.2.1 = Refine.oldSV E t c.2.1 := by
  intro c' hc'
  by_cases h : c.1.1.1 = t
  · rw [refineOE_of t h] at hc'
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
    rw [← hc']
  · rw [refineOE_of_ne t h] at hc'
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hc'
    rw [← hc']

theorem last_refineOE (c : OEdge E) :
    ∀ c' ∈ (refineOE t c).getLast?, c'.2.2 = Refine.oldSV E t c.2.2 := by
  intro c' hc'
  by_cases h : c.1.1.1 = t
  · rw [refineOE_of t h] at hc'
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_def,
      Option.some.injEq] at hc'
    rw [← hc']
  · rw [refineOE_of_ne t h] at hc'
    simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq] at hc'
    rw [← hc']

theorem parentSE_of_mem_refineOE {c : OEdge E} {c' : OEdge (refineDatum E t)}
    (h : c' ∈ refineOE t c) : Refine.parentSE E t c'.1 = c.1 := by
  by_cases hct : c.1.1.1 = t
  · rw [refineOE_of t hct] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> exact Refine.parentSE_piece E t _ _
  · rw [refineOE_of_ne t hct] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    exact Refine.parentSE_piece E t _ _

theorem mem_refineOE_of_parentSE {c : OEdge E} (hc : Good E c)
    {y : (refineDatum E t).SourceEdge} (hy : Refine.parentSE E t y = c.1) :
    y ∈ (refineOE t c).map Prod.fst := by
  rcases eq_piece_of_parentSE t hc hy with rfl | rfl
  · by_cases hct : c.1.1.1 = t
    · rw [refineOE_of t hct]; simp
    · rw [refineOE_of_ne t hct]; simp
  · by_cases hct : c.1.1.1 = t
    · rw [refineOE_of t hct]; simp
    · rw [refineOE_of_ne t hct, piece_eq_of_ne t hct c.2.2 c.2.1]; simp

theorem nodup_refineOE {c : OEdge E} (hc : Good E c) : ((refineOE t c).map Prod.fst).Nodup := by
  by_cases hct : c.1.1.1 = t
  · rw [refineOE_of t hct]
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, List.nodup_nil, and_true, not_false_eq_true]
    exact piece_ne_of_good t hc hct
  · rw [refineOE_of_ne t hct]
    simp

variable (hE : E.Connected)
include hE

theorem good_refineOE {c : OEdge E} (hc : Good E c) :
    ∀ c' ∈ refineOE t c, Good (refineDatum E t) c' := by
  intro c' hc'
  obtain ⟨hnd, hu, hv, huv⟩ := hc
  have hnd' : ∀ w, ¬ IsDangling (refineDatum E t) (Refine.piece E t w c.1) := fun w ↦
    (Refine.isDangling_iff E t hE _).not.mpr (by rw [Refine.parentSE_piece]; exact hnd)
  by_cases hct : c.1.1.1 = t
  · have hhalf : ∀ w, Incident (refineDatum E t) (Refine.piece E t w c.1)
        (Refine.freshOf E t c.1 hct) := by
      intro w
      rw [Refine.freshOf, Refine.incident_freshSV_iff]
      by_cases hw : (t : S.V × S.V).2 = w.1.1
      · left
        apply Subtype.ext
        rw [piece_val, hct]
        unfold pieceT
        rw [if_pos ⟨rfl, hw⟩]
        rfl
      · right
        apply Subtype.ext
        rw [piece_val, hct]
        unfold pieceT
        rw [if_neg (fun h ↦ hw h.2)]
        rfl
    rw [refineOE_of t hct] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact ⟨hnd' _, Refine.incident_piece E t hu, hhalf _,
        Refine.oldSV_ne_freshSV E t _ _ _⟩
    · exact ⟨hnd' _, hhalf _, Refine.incident_piece E t hv,
        (Refine.oldSV_ne_freshSV E t _ _ _).symm⟩
  · rw [refineOE_of_ne t hct] at hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    subst hc'
    refine ⟨hnd' _, Refine.incident_piece E t hu, ?_, fun h ↦ huv (Refine.oldSV_injective E t h)⟩
    rw [piece_eq_of_ne t hct c.2.1 c.2.2]
    exact Refine.incident_piece E t hv

omit hE in
theorem srcLen_piece (w' : (subdivTarget S t).edges → ℚ) (u : E.SourceVertex) (f : E.SourceEdge) :
    srcLen (refineDatum E t) w' (Refine.piece E t u f) =
      w' (pieceT t u.1.1 f.1.1) / E.sourceEdgeIndex f := by
  unfold srcLen
  rw [Refine.sourceEdgeIndex_eq, Refine.parentSE_piece]
  rfl

omit hE in
theorem sum_refineOE {w : S.edges → ℚ} {w' : (subdivTarget S t).edges → ℚ}
    (hw₁ : ∀ e₀, e₀ ≠ t → w' (subdivOcc S t (some e₀)) = w e₀)
    (hw₂ : w' (subdivOcc S t (some t)) + w' (subdivOcc S t none) = w t)
    {c : OEdge E} (hc : Good E c) :
    ((refineOE t c).map fun c' ↦ srcLen _ w' c'.1).sum = srcLen E w c.1 := by
  by_cases hct : c.1.1.1 = t
  · rw [refineOE_of t hct]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [srcLen_piece, srcLen_piece, ← add_div, hct]
    have h := hw₂
    unfold srcLen
    rw [hct]
    congr 1
    rcases hc.ends_cases with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [hu, hv]
      change w' (pieceT t (c.1.1.1 : S.V × S.V).1 t) + w' (pieceT t (c.1.1.1 : S.V × S.V).2 t) = _
      rw [hct, pieceT_fst, pieceT_snd, h]
    · rw [hu, hv]
      change w' (pieceT t (c.1.1.1 : S.V × S.V).2 t) + w' (pieceT t (c.1.1.1 : S.V × S.V).1 t) = _
      rw [hct, pieceT_fst, pieceT_snd, add_comm, h]
  · rw [refineOE_of_ne t hct]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [srcLen_piece, pieceT_of_ne t hct]
    have h := hw₁ c.1.1.1 hct
    unfold srcLen
    rw [h]

end RefineChains

section RefineChainLists

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} (t : S.edges)

@[simp] theorem refineChain_nil : refineChain t ([] : List (OEdge E)) = [] := rfl

theorem refineChain_cons (c : OEdge E) (l : List (OEdge E)) :
    refineChain t (c :: l) = refineOE t c ++ refineChain t l := by
  unfold refineChain
  rw [List.flatMap_cons]

theorem refineChain_append (l l' : List (OEdge E)) :
    refineChain t (l ++ l') = refineChain t l ++ refineChain t l' := by
  unfold refineChain
  rw [List.flatMap_append]

theorem refineChain_ne_nil {l : List (OEdge E)} (h : l ≠ []) : refineChain t l ≠ [] := by
  obtain ⟨c, l', rfl⟩ := List.exists_cons_of_ne_nil h
  rw [refineChain_cons]
  exact List.append_ne_nil_of_left_ne_nil (refineOE_ne_nil t c) _

theorem head_refineChain {l : List (OEdge E)} (h : l ≠ []) :
    ((refineChain t l).head (refineChain_ne_nil t h)).2.1 = Refine.oldSV E t (l.head h).2.1 := by
  obtain ⟨c, l', rfl⟩ := List.exists_cons_of_ne_nil h
  have e1 : (refineChain t (c :: l')).head (refineChain_ne_nil t h) =
      (refineOE t c).head (refineOE_ne_nil t c) := by
    simp only [refineChain_cons]
    exact List.head_append_of_ne_nil _
  rw [e1]
  exact head_refineOE t c _ (List.head_mem_head? _)

theorem last_refineChain {l : List (OEdge E)} (h : l ≠ []) :
    ((refineChain t l).getLast (refineChain_ne_nil t h)).2.2 =
      Refine.oldSV E t (l.getLast h).2.2 := by
  induction l with
  | nil => exact absurd rfl h
  | cons c l ih =>
    cases l with
    | nil =>
      have e1 : (refineChain t [c]).getLast (refineChain_ne_nil t h) =
          (refineOE t c).getLast (refineOE_ne_nil t c) := by
        simp only [refineChain_cons, refineChain_nil, List.append_nil]
      rw [e1]
      exact last_refineOE t c _ (List.getLast_mem_getLast? _)
    | cons c' l =>
      have ih' := ih (List.cons_ne_nil _ _)
      have e1 : (refineChain t (c :: c' :: l)).getLast (refineChain_ne_nil t h) =
          (refineChain t (c' :: l)).getLast (refineChain_ne_nil t (List.cons_ne_nil _ _)) := by
        simp only [refineChain_cons]
        rw [List.getLast_append_of_ne_nil]
      rw [e1, ih']
      simp only [List.getLast_cons_cons]

theorem parentSE_of_mem_refineChain {l : List (OEdge E)} {y : (refineDatum E t).SourceEdge}
    (h : y ∈ (refineChain t l).map Prod.fst) : Refine.parentSE E t y ∈ l.map Prod.fst := by
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp h
  obtain ⟨c, hc, hcc⟩ := List.mem_flatMap.mp hc'
  rw [parentSE_of_mem_refineOE t hcc]
  exact List.mem_map_of_mem hc

theorem mem_refineChain_iff {l : List (OEdge E)} (hg : ∀ c ∈ l, Good E c)
    (y : (refineDatum E t).SourceEdge) :
    y ∈ (refineChain t l).map Prod.fst ↔ Refine.parentSE E t y ∈ l.map Prod.fst := by
  refine ⟨parentSE_of_mem_refineChain t, fun h ↦ ?_⟩
  obtain ⟨c, hc, hcy⟩ := List.mem_map.mp h
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (mem_refineOE_of_parentSE t (hg c hc) hcy.symm)
  exact List.mem_map_of_mem (List.mem_flatMap.mpr ⟨c, hc, hc'⟩)

theorem nodup_refineChain {l : List (OEdge E)} (hg : ∀ c ∈ l, Good E c)
    (hl : (l.map Prod.fst).Nodup) : ((refineChain t l).map Prod.fst).Nodup := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [refineChain_cons, List.map_append, List.nodup_append]
    rw [List.map_cons, List.nodup_cons] at hl
    refine ⟨nodup_refineOE t (hg c (List.mem_cons_self ..)),
      ih (fun c' h ↦ hg c' (List.mem_cons_of_mem _ h)) hl.2, ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨c₁, hc₁, rfl⟩ := List.mem_map.mp ha
    apply hl.1
    rw [← parentSE_of_mem_refineOE t hc₁]
    exact parentSE_of_mem_refineChain t hb

theorem good_refineChain (hE : E.Connected) {l : List (OEdge E)} (hg : ∀ c ∈ l, Good E c) :
    ∀ c' ∈ refineChain t l, Good (refineDatum E t) c' := by
  intro c' hc'
  obtain ⟨c, hc, hcc⟩ := List.mem_flatMap.mp hc'
  exact good_refineOE t hE (hg c hc) c' hcc

theorem sum_refineChain {w : S.edges → ℚ} {w' : (subdivTarget S t).edges → ℚ}
    (hw₁ : ∀ e₀, e₀ ≠ t → w' (subdivOcc S t (some e₀)) = w e₀)
    (hw₂ : w' (subdivOcc S t (some t)) + w' (subdivOcc S t none) = w t)
    {l : List (OEdge E)} (hg : ∀ c ∈ l, Good E c) :
    ((refineChain t l).map fun c' ↦ srcLen _ w' c'.1).sum = (l.map fun c ↦ srcLen E w c.1).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [refineChain_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons,
      sum_refineOE t hw₁ hw₂ (hg c (List.mem_cons_self ..)),
      ih (fun c' h ↦ hg c' (List.mem_cons_of_mem _ h))]

theorem isChain_refineChain (hE : E.Connected) {m m' : ℕ} {V : Fin m → E.SourceVertex}
    {V' : Fin m' → (refineDatum E t).SourceVertex}
    (hold : ∀ v, v ∉ Set.range V → Refine.oldSV E t v ∉ Set.range V')
    {l : List (OEdge E)} (hl : l.IsChain (Link E V)) (hg : ∀ c ∈ l, Good E c)
    (hfresh : ∀ c ∈ l, ∀ h : c.1.1.1 = t, Refine.freshOf E t c.1 h ∉ Set.range V') :
    (refineChain t l).IsChain (Link (refineDatum E t) V') := by
  induction l with
  | nil => exact List.IsChain.nil
  | cons c l ih =>
    rw [refineChain_cons]
    have hc := hg c (List.mem_cons_self ..)
    refine List.IsChain.append ?_ (ih hl.tail (fun c' h ↦ hg c' (List.mem_cons_of_mem _ h))
      (fun c' h ↦ hfresh c' (List.mem_cons_of_mem _ h))) ?_
    · by_cases hct : c.1.1.1 = t
      · rw [refineOE_of t hct, List.isChain_pair]
        refine ⟨rfl, ?_, hfresh c (List.mem_cons_self ..) hct⟩
        exact Refine.nonDanglingValency_freshOf E t hE ⟨c.1, hc.1⟩ hct
      · rw [refineOE_of_ne t hct]
        exact List.isChain_singleton _
    · intro a ha b hb
      cases l with
      | nil => simp [refineChain] at hb
      | cons c' l =>
        rw [List.isChain_cons_cons] at hl
        obtain ⟨⟨hlink, hin⟩, -⟩ := hl
        rw [refineChain_cons, List.head?_append_of_ne_nil _ (refineOE_ne_nil t c')] at hb
        have ha' := last_refineOE t c a ha
        have hb' := head_refineOE t c' b hb
        refine ⟨by rw [ha', hb', hlink], ?_⟩
        rw [ha']
        refine ⟨?_, hold _ hin.2⟩
        rw [Refine.nonDanglingValency_oldSV E t hE]
        exact hin.1

end RefineChainLists

/-! ## 3. Splitting a chain at a mark -/

section Split

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} {m : ℕ}

/-- **The named vertices after a mark** on the surviving edge `x`: the old ones, then the fresh
vertex of `x`. -/
def newV (V : Fin m → E.SourceVertex) (x : NonDanglingEdge E) :
    Fin (m + 1) → (refineDatum E x.1.1.1).SourceVertex :=
  Fin.lastCases (Refine.freshOf E x.1.1.1 x.1 rfl) fun a ↦ Refine.oldSV E x.1.1.1 (V a)

@[simp] theorem newV_last (V : Fin m → E.SourceVertex) (x : NonDanglingEdge E) :
    newV V x (Fin.last m) = Refine.freshOf E x.1.1.1 x.1 rfl := by
  unfold newV; rw [Fin.lastCases_last]

@[simp] theorem newV_castSucc (V : Fin m → E.SourceVertex) (x : NonDanglingEdge E) (a : Fin m) :
    newV V x a.castSucc = Refine.oldSV E x.1.1.1 (V a) := by
  unfold newV; rw [Fin.lastCases_castSucc]

theorem newV_injective {V : Fin m → E.SourceVertex} (hV : Function.Injective V)
    (x : NonDanglingEdge E) : Function.Injective (newV V x) := by
  intro a b h
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rfl
    | cast b =>
      rw [newV_last, newV_castSucc] at h
      exact absurd h.symm (Refine.oldSV_ne_freshSV _ _ _ _ _)
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      rw [newV_last, newV_castSucc] at h
      exact absurd h (Refine.oldSV_ne_freshSV _ _ _ _ _)
    | cast b =>
      rw [newV_castSucc, newV_castSucc] at h
      rw [hV (Refine.oldSV_injective _ _ h)]

theorem oldSV_notMem_newV {V : Fin m → E.SourceVertex} {x : NonDanglingEdge E}
    {v : E.SourceVertex} (hv : v ∉ Set.range V) :
    Refine.oldSV E x.1.1.1 v ∉ Set.range (newV V x) := by
  rintro ⟨a, ha⟩
  induction a using Fin.lastCases with
  | last =>
    rw [newV_last] at ha
    exact Refine.oldSV_ne_freshSV _ _ _ _ _ ha.symm
  | cast a =>
    rw [newV_castSucc] at ha
    exact hv ⟨a, Refine.oldSV_injective _ _ ha⟩

theorem freshOf_notMem_newV {V : Fin m → E.SourceVertex} {x : NonDanglingEdge E}
    {f : E.SourceEdge} (hf : f.1.1 = x.1.1.1) (hne : f ≠ x.1) :
    Refine.freshOf E x.1.1.1 f hf ∉ Set.range (newV V x) := by
  rintro ⟨a, ha⟩
  induction a using Fin.lastCases with
  | last =>
    rw [newV_last] at ha
    exact hne (Refine.freshOf_inj _ _ hf rfl ha.symm)
  | cast a =>
    rw [newV_castSucc] at ha
    exact Refine.oldSV_ne_freshSV _ _ _ _ _ ha

variable (t : S.edges)

/-- The half of an edge over `t` at its entry vertex, ending at the fresh vertex. -/
def nearOE (c : OEdge E) (h : c.1.1.1 = t) : OEdge (refineDatum E t) :=
  (Refine.piece E t c.2.1 c.1, Refine.oldSV E t c.2.1, Refine.freshOf E t c.1 h)

/-- The half of an edge over `t` at its exit vertex, starting at the fresh vertex. -/
def farOE (c : OEdge E) (h : c.1.1.1 = t) : OEdge (refineDatum E t) :=
  (Refine.piece E t c.2.2 c.1, Refine.freshOf E t c.1 h, Refine.oldSV E t c.2.2)

/-- The refined chain up to the mark, which lies on the `j`-th edge. -/
def leftPart (l : List (OEdge E)) (j : ℕ) (hj : j < l.length) (h : l[j].1.1.1 = t) :
    List (OEdge (refineDatum E t)) :=
  refineChain t (l.take j) ++ [nearOE t l[j] h]

/-- The refined chain from the mark on. -/
def rightPart (l : List (OEdge E)) (j : ℕ) (hj : j < l.length) (h : l[j].1.1.1 = t) :
    List (OEdge (refineDatum E t)) :=
  farOE t l[j] h :: refineChain t (l.drop (j + 1))

variable {l : List (OEdge E)} {j : ℕ} (hj : j < l.length) (h : l[j].1.1.1 = t)

theorem refineChain_split : refineChain t l = leftPart t l j hj h ++ rightPart t l j hj h := by
  conv_lhs => rw [← List.take_append_drop j l, List.drop_eq_getElem_cons hj]
  rw [refineChain_append, refineChain_cons, refineOE_of t h]
  simp [leftPart, rightPart, nearOE, farOE]

theorem leftPart_ne_nil : leftPart t l j hj h ≠ [] := by simp [leftPart]

theorem head_leftPart (hne : l ≠ []) :
    ((leftPart t l j hj h).head (leftPart_ne_nil t hj h)).2.1 =
      Refine.oldSV E t (l.head hne).2.1 := by
  rw [← head_refineChain t hne]
  have e1 : (refineChain t l).head (refineChain_ne_nil t hne) =
      (leftPart t l j hj h).head (leftPart_ne_nil t hj h) := by
    simp only [refineChain_split t hj h]
    exact List.head_append_of_ne_nil _
  rw [e1]

theorem last_leftPart :
    (leftPart t l j hj h).getLast (leftPart_ne_nil t hj h) = nearOE t l[j] h := by
  unfold leftPart
  exact List.getLast_concat

theorem last_rightPart (hne : l ≠ []) :
    ((rightPart t l j hj h).getLast (List.cons_ne_nil _ _)).2.2 =
      Refine.oldSV E t (l.getLast hne).2.2 := by
  rw [← last_refineChain t hne]
  have e1 : (refineChain t l).getLast (refineChain_ne_nil t hne) =
      (rightPart t l j hj h).getLast (List.cons_ne_nil _ _) := by
    simp only [refineChain_split t hj h]
    exact List.getLast_append_of_ne_nil _ (List.cons_ne_nil _ _)
  rw [e1]

theorem mem_getLast?_refineChain {l' : List (OEdge E)} {a : OEdge (refineDatum E t)}
    (ha : a ∈ (refineChain t l').getLast?) :
    ∃ hne : l' ≠ [], a.2.2 = Refine.oldSV E t (l'.getLast hne).2.2 := by
  have hne : l' ≠ [] := by
    rintro rfl
    simp at ha
  refine ⟨hne, ?_⟩
  rw [List.getLast?_eq_some_getLast (refineChain_ne_nil t hne), Option.mem_def,
    Option.some.injEq] at ha
  rw [← ha]
  exact last_refineChain t hne

theorem mem_head?_refineChain {l' : List (OEdge E)} {a : OEdge (refineDatum E t)}
    (ha : a ∈ (refineChain t l').head?) :
    ∃ hne : l' ≠ [], a.2.1 = Refine.oldSV E t (l'.head hne).2.1 := by
  have hne : l' ≠ [] := by
    rintro rfl
    simp at ha
  refine ⟨hne, ?_⟩
  rw [List.head?_eq_some_head (refineChain_ne_nil t hne), Option.mem_def,
    Option.some.injEq] at ha
  rw [← ha]
  exact head_refineChain t hne

variable (hE : E.Connected) {m' : ℕ} {V : Fin m → E.SourceVertex}
  {V' : Fin m' → (refineDatum E t).SourceVertex}
  (hold : ∀ v, v ∉ Set.range V → Refine.oldSV E t v ∉ Set.range V')
  (hl : l.IsChain (Link E V)) (hg : ∀ c ∈ l, Good E c)

include hE hold hl hg in
theorem isChain_leftPart
    (hfresh : ∀ c ∈ l.take j, ∀ h : c.1.1.1 = t, Refine.freshOf E t c.1 h ∉ Set.range V') :
    (leftPart t l j hj h).IsChain (Link (refineDatum E t) V') := by
  refine List.IsChain.append (isChain_refineChain t hE hold (hl.take j)
    (fun c hc ↦ hg c (List.mem_of_mem_take hc)) hfresh) (List.isChain_singleton _) ?_
  intro a ha b hb
  obtain ⟨hne, ha'⟩ := mem_getLast?_refineChain t ha
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
  subst hb
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | h0
    · simp at hne
    · exact h0
  have hlast : (l.take j).getLast hne = l[j - 1] := by
    rw [List.getLast_eq_getElem]
    simp only [List.getElem_take, List.length_take]
    congr 1
    omega
  have hlink := hl.getElem (j - 1) (by omega)
  have hidx : j - 1 + 1 = j := by omega
  simp only [hidx] at hlink
  rw [hlast] at ha'
  refine ⟨?_, ?_⟩
  · rw [ha', hlink.1]
    rfl
  · rw [ha']
    refine ⟨?_, hold _ hlink.2.2⟩
    rw [Refine.nonDanglingValency_oldSV E t hE]
    exact hlink.2.1

include hE hold hl hg in
theorem isChain_rightPart
    (hfresh : ∀ c ∈ l.drop (j + 1), ∀ h : c.1.1.1 = t, Refine.freshOf E t c.1 h ∉ Set.range V') :
    (rightPart t l j hj h).IsChain (Link (refineDatum E t) V') := by
  unfold rightPart
  rw [List.isChain_cons]
  refine ⟨fun b hb ↦ ?_, isChain_refineChain t hE hold (hl.drop (j + 1))
    (fun c hc ↦ hg c (List.mem_of_mem_drop hc)) hfresh⟩
  obtain ⟨hne, hb'⟩ := mem_head?_refineChain t hb
  have hj1 : j + 1 < l.length := by
    by_contra hc
    exact hne (List.drop_eq_nil_of_le (by omega))
  have hhead : (l.drop (j + 1)).head hne = l[j + 1] := by
    rw [List.head_eq_getElem]
    simp only [List.getElem_drop, Nat.add_zero]
  have hlink := hl.getElem j hj1
  rw [hhead] at hb'
  refine ⟨?_, ?_⟩
  · show Refine.oldSV E t l[j].2.2 = b.2.1
    rw [hb', hlink.1]
  · refine ⟨?_, hold _ hlink.2.2⟩
    show nonDanglingValency _ (Refine.oldSV E t l[j].2.2) = 2
    rw [Refine.nonDanglingValency_oldSV E t hE]
    exact hlink.2.1

omit hj in
theorem sum_leftPart {w : S.edges → ℚ} {w' : (subdivTarget S t).edges → ℚ}
    (hw₁ : ∀ e₀, e₀ ≠ t → w' (subdivOcc S t (some e₀)) = w e₀)
    (hw₂ : w' (subdivOcc S t (some t)) + w' (subdivOcc S t none) = w t)
    (hg : ∀ c ∈ l, Good E c) (hj : j < l.length) (h : l[j].1.1.1 = t) :
    ((leftPart t l j hj h).map fun c' ↦ srcLen _ w' c'.1).sum =
      ((l.take j).map fun c ↦ srcLen E w c.1).sum + srcLen _ w' (nearOE t l[j] h).1 := by
  unfold leftPart
  rw [List.map_append, List.sum_append, sum_refineChain t hw₁ hw₂
    (fun c hc ↦ hg c (List.mem_of_mem_take hc))]
  simp

omit hj in
theorem sum_rightPart {w : S.edges → ℚ} {w' : (subdivTarget S t).edges → ℚ}
    (hw₁ : ∀ e₀, e₀ ≠ t → w' (subdivOcc S t (some e₀)) = w e₀)
    (hw₂ : w' (subdivOcc S t (some t)) + w' (subdivOcc S t none) = w t)
    (hg : ∀ c ∈ l, Good E c) (hj : j < l.length) (h : l[j].1.1.1 = t) :
    ((rightPart t l j hj h).map fun c' ↦ srcLen _ w' c'.1).sum =
      srcLen _ w' (farOE t l[j] h).1 + ((l.drop (j + 1)).map fun c ↦ srcLen E w c.1).sum := by
  unfold rightPart
  rw [List.map_cons, List.sum_cons, sum_refineChain t hw₁ hw₂
    (fun c hc ↦ hg c (List.mem_of_mem_drop hc))]

omit hj in
theorem srcLen_near_add_far {w : S.edges → ℚ} {w' : (subdivTarget S t).edges → ℚ}
    (hw₁ : ∀ e₀, e₀ ≠ t → w' (subdivOcc S t (some e₀)) = w e₀)
    (hw₂ : w' (subdivOcc S t (some t)) + w' (subdivOcc S t none) = w t)
    {c : OEdge E} (hc : Good E c) (h : c.1.1.1 = t) :
    srcLen _ w' (nearOE t c h).1 + srcLen _ w' (farOE t c h).1 = srcLen E w c.1 := by
  have := sum_refineOE t hw₁ hw₂ hc
  rw [refineOE_of t h] at this
  simpa [nearOE, farOE] using this

end Split

/-! ## 4. The forward step: a mark at its actual position -/

section Forward

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} {m q : ℕ} {C : Core m q}
  {V : Fin m → E.SourceVertex} {y : Fin q → ℚ}

/-- **The position on a list of non-negative lengths**: a point strictly after the start and at
most at the end lies on some entry, strictly after its start. -/
theorem exists_split_index (l : List ℚ) (hnn : ∀ a ∈ l, 0 ≤ a) {pos : ℚ} (h0 : 0 < pos)
    (hle : pos ≤ l.sum) :
    ∃ j, ∃ hj : j < l.length, (l.take j).sum < pos ∧ pos ≤ (l.take j).sum + l[j] := by
  induction l generalizing pos with
  | nil => simp at hle; linarith
  | cons a l ih =>
    by_cases hpa : pos ≤ a
    · exact ⟨0, by simp, by simpa using h0, by simpa using hpa⟩
    · push Not at hpa
      obtain ⟨j, hj, h1, h2⟩ := ih (fun b hb ↦ hnn b (List.mem_cons_of_mem _ hb))
        (pos := pos - a) (by linarith) (by simp at hle; linarith)
      refine ⟨j + 1, by simpa using hj, ?_, ?_⟩
      · simp only [List.take_succ_cons, List.sum_cons]; linarith
      · simp only [List.take_succ_cons, List.sum_cons, List.getElem_cons_succ]; linarith

theorem srcLen_nonneg {w : S.edges → ℚ} (hw : ∀ e, 0 ≤ w e) (x : E.SourceEdge) :
    0 ≤ srcLen E w x :=
  div_nonneg (hw _) (Nat.cast_nonneg _)

theorem sourceEdgeIndex_pos' (x : E.SourceEdge) : (0 : ℚ) < E.sourceEdgeIndex x := by
  exact_mod_cast (E.edgePartition x.1.1).blockCard_pos x.1.2

theorem head_congr' {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    l₁.head h₁ = l₂.head h₂ := by subst h; rfl

theorem getLast_congr' {α : Type*} {l₁ l₂ : List α} (h : l₁ = l₂) (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) :
    l₁.getLast h₁ = l₂.getLast h₂ := by subst h; rfl

/-- The edge at index `j` of a duplicate-free chain is not an earlier or a later one. -/
theorem fst_ne_of_mem_take {l : List (OEdge E)} (hl : (l.map Prod.fst).Nodup) {j : ℕ}
    (hj : j < l.length) {c : OEdge E} (hc : c ∈ l.take j) : c.1 ≠ l[j].1 := by
  intro h
  have hd : ((l.take j).map Prod.fst ++ (l.drop j).map Prod.fst).Nodup := by
    rw [← List.map_append, List.take_append_drop]; exact hl
  have h1 : l[j].1 ∈ (l.drop j).map Prod.fst := List.mem_map_of_mem (by
    rw [List.drop_eq_getElem_cons hj]; exact List.mem_cons_self ..)
  exact List.disjoint_of_nodup_append hd (h ▸ List.mem_map_of_mem hc) h1

theorem fst_ne_of_mem_drop {l : List (OEdge E)} (hl : (l.map Prod.fst).Nodup) {j : ℕ}
    (hj : j < l.length) {c : OEdge E} (hc : c ∈ l.drop (j + 1)) : c.1 ≠ l[j].1 := by
  intro h
  have hd : ((l.take (j + 1)).map Prod.fst ++ (l.drop (j + 1)).map Prod.fst).Nodup := by
    rw [← List.map_append, List.take_append_drop]; exact hl
  have h1 : l[j].1 ∈ (l.take (j + 1)).map Prod.fst := List.mem_map_of_mem (by
    rw [List.take_succ_eq_append_getElem hj]; exact List.mem_append_right _ (List.mem_singleton_self _))
  exact List.disjoint_of_nodup_append hd h1 (h ▸ List.mem_map_of_mem hc)

/-- **The forward step** (§5.2, the marks at their actual positions): a layout with the mark placed
at its actual position on its slot `e`, at distance `y' (castSucc e)` from `V (tail e)`. The mark
lies on the surviving edge `x`, the target edge of `x` is subdivided there, and the refined chains
are a layout of the subdivided core, merging back to the old one. -/
theorem forward (hE : E.Connected) (L : Layout E C V y) (e : Fin q) {y' : Fin (q + 1) → ℚ}
    (hy : y = mergeRequest e y') (h1 : 0 < y' e.castSucc) (h2 : 0 ≤ y' (Fin.last q)) :
    ∃ x : NonDanglingEdge E, L.lab x = e ∧
      ∃ L' : Layout (refineDatum E x.1.1.1) (subdivide C e) (newV V x) y',
        (∀ z, mergeOne e (L'.lab z) = L.lab (Refine.parentND E x.1.1.1 hE z)) ∧
        (∀ e₀, e₀ ≠ x.1.1.1 → L'.w (subdivOcc S x.1.1.1 (some e₀)) = L.w e₀) ∧
        L'.w (subdivOcc S x.1.1.1 (some x.1.1.1)) + L'.w (subdivOcc S x.1.1.1 none) =
          L.w x.1.1.1 := by
  classical
  set l := L.chain e with hl
  have hg := L.good e
  set f : OEdge E → ℚ := fun c ↦ srcLen E L.w c.1 with hf
  have htot : (l.map f).sum = y' e.castSucc + y' (Fin.last q) := by
    rw [hf, L.sum e, hy]; unfold mergeRequest; rw [if_pos rfl]
  obtain ⟨j, hjm, hlt, hle⟩ := exists_split_index (l.map f)
    (fun a ha ↦ by
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
      exact srcLen_nonneg L.w_nonneg _) h1 (by rw [htot]; linarith)
  have hj : j < l.length := by simpa using hjm
  rw [← List.map_take] at hlt hle
  simp only [List.getElem_map] at hle
  set c := l[j] with hc
  have hcg := hg c (List.getElem_mem hj)
  set x : NonDanglingEdge E := ⟨c.1, hcg.1⟩ with hx
  set t := x.1.1.1 with ht
  have htc : l[j].1.1.1 = t := rfl
  have hlx : L.lab x = e := (L.mem x e).mp (List.mem_map_of_mem (List.getElem_mem hj))
  refine ⟨x, hlx, ?_⟩
  -- the offset of the mark on `x`, and the lengths of the two halves of `t`
  set pre := ((l.take j).map f).sum with hpre
  set o := y' e.castSucc - pre with ho
  have ho0 : 0 < o := by rw [ho]; linarith
  have hoS : o ≤ f c := by rw [ho]; linarith
  have hidx := sourceEdgeIndex_pos' (E := E) c.1
  set a := o * E.sourceEdgeIndex c.1 with ha
  have ha0 : 0 ≤ a := by positivity
  have haw : a ≤ L.w t := by
    have : f c = L.w t / E.sourceEdgeIndex c.1 := rfl
    rw [this, le_div_iff₀ hidx] at hoS
    exact hoS
  set N : Prop := (t : S.V × S.V).2 = c.2.1.1.1 with hN
  set w' : (subdivTarget S t).edges → ℚ := fun ε ↦ Option.elim ((subdivOcc S t).symm ε)
    (if N then a else L.w t - a) (fun e₀ ↦ if e₀ = t then (if N then L.w t - a else a)
      else L.w e₀) with hw'
  have hw'none : w' (subdivOcc S t none) = if N then a else L.w t - a := by
    simp only [hw', Equiv.symm_apply_apply, Option.elim_none]
  have hw'some : ∀ e₀, w' (subdivOcc S t (some e₀)) =
      if e₀ = t then (if N then L.w t - a else a) else L.w e₀ := by
    intro e₀
    simp only [hw', Equiv.symm_apply_apply, Option.elim_some]
  have hw₁ : ∀ e₀, e₀ ≠ t → w' (subdivOcc S t (some e₀)) = L.w e₀ := fun e₀ he ↦ by
    rw [hw'some, if_neg he]
  have hw₂ : w' (subdivOcc S t (some t)) + w' (subdivOcc S t none) = L.w t := by
    rw [hw'some, if_pos rfl, hw'none]
    split_ifs <;> ring
  have hw'nn : ∀ ε, 0 ≤ w' ε := by
    intro ε
    obtain ⟨oε, rfl⟩ := (subdivOcc S t).surjective ε
    cases oε with
    | none => rw [hw'none]; split_ifs <;> linarith
    | some e₀ =>
      rw [hw'some]
      split_ifs
      · linarith
      · exact ha0
      · exact L.w_nonneg e₀
  have hnear : srcLen _ w' (nearOE t l[j] htc).1 = o := by
    show srcLen _ w' (Refine.piece E t c.2.1 c.1) = o
    rw [srcLen_piece]
    have hpt : w' (pieceT t c.2.1.1.1 c.1.1.1) = a := by
      change w' (pieceT t c.2.1.1.1 t) = a
      unfold pieceT
      by_cases hn : N
      · rw [if_pos ⟨rfl, hn⟩, hw'none, if_pos hn]
      · rw [if_neg (fun h ↦ hn h.2), hw'some, if_pos rfl, if_neg hn]
    rw [hpt, ha]
    field_simp
  have hfar : srcLen _ w' (farOE t l[j] htc).1 = f c - o := by
    have := srcLen_near_add_far t hw₁ hw₂ hcg htc
    rw [hnear] at this
    show _ = srcLen E L.w c.1 - o
    linarith
  -- the parts, and their membership
  set Lf := leftPart t l j hj htc with hLf
  set Rt := rightPart t l j hj htc with hRt
  have hsplit : refineChain t l = Lf ++ Rt := refineChain_split t hj htc
  have hnodup : (Lf.map Prod.fst ++ Rt.map Prod.fst).Nodup := by
    rw [← List.map_append, ← hsplit]
    exact nodup_refineChain t hg (L.nodup e)
  have hK1 : ∀ z : NonDanglingEdge (refineDatum E t),
      z.1 ∈ (refineChain t l).map Prod.fst ↔ L.lab (Refine.parentND E t hE z) = e := by
    intro z
    rw [mem_refineChain_iff t hg, ← L.mem]
    rfl
  have hK3 : ∀ i (z : NonDanglingEdge (refineDatum E t)),
      z.1 ∈ (refineChain t (L.chain i)).map Prod.fst ↔ L.lab (Refine.parentND E t hE z) = i := by
    intro i z
    rw [mem_refineChain_iff t (L.good i), ← L.mem]
    rfl
  -- the labels and the chains
  set lab' : NonDanglingEdge (refineDatum E t) → Fin (q + 1) := fun z ↦
    if L.lab (Refine.parentND E t hE z) = e then
      (if z.1 ∈ Lf.map Prod.fst then e.castSucc else Fin.last q)
    else (L.lab (Refine.parentND E t hE z)).castSucc with hlab'
  set ch : Fin (q + 1) → List (OEdge (refineDatum E t)) := fun i' ↦
    Fin.lastCases Rt (fun i ↦ if i = e then Lf else refineChain t (L.chain i)) i' with hch
  have hch_last : ch (Fin.last q) = Rt := by simp only [hch, Fin.lastCases_last]
  have hch_e : ch e.castSucc = Lf := by simp only [hch, Fin.lastCases_castSucc, if_true]
  have hch_ne : ∀ i, i ≠ e → ch i.castSucc = refineChain t (L.chain i) := fun i hi ↦ by
    simp only [hch, Fin.lastCases_castSucc, if_neg hi]
  have hRt_ne : Rt ≠ [] := List.cons_ne_nil _ _
  have hLf_ne : Lf ≠ [] := leftPart_ne_nil t hj htc
  have hne : ∀ i', ch i' ≠ [] := by
    intro i'
    induction i' using Fin.lastCases with
    | last => rw [hch_last]; exact hRt_ne
    | cast i =>
      by_cases hie : i = e
      · subst hie; rw [hch_e]; exact hLf_ne
      · rw [hch_ne i hie]; exact refineChain_ne_nil t (L.ne_nil i)
  have hgood : ∀ i', ∀ c' ∈ ch i', Good (refineDatum E t) c' := by
    have hgl := good_refineChain t hE hg
    rw [hsplit] at hgl
    intro i' c' hc'
    induction i' using Fin.lastCases with
    | last => rw [hch_last] at hc'; exact hgl c' (List.mem_append_right _ hc')
    | cast i =>
      by_cases hie : i = e
      · subst hie; rw [hch_e] at hc'; exact hgl c' (List.mem_append_left _ hc')
      · rw [hch_ne i hie] at hc'; exact good_refineChain t hE (L.good i) c' hc'
  have hlx' : ∀ i, i ≠ e → ∀ c' ∈ L.chain i, c'.1 ≠ x.1 := by
    intro i hie c' hc' heq
    have hxm : x.1 ∈ (L.chain i).map Prod.fst := by
      rw [← heq]; exact List.mem_map_of_mem hc'
    exact hie (((L.mem x i).mp hxm).symm.trans hlx)
  have hold : ∀ v, v ∉ Set.range V → Refine.oldSV E t v ∉ Set.range (newV V x) :=
    fun v hv ↦ oldSV_notMem_newV hv
  refine ⟨{
    lab := lab'
    w := w'
    w_nonneg := hw'nn
    chain := ch
    good := hgood
    mem := ?_
    nodup := ?_
    link := ?_
    ne_nil := hne
    head := ?_
    last := ?_
    sum := ?_ }, ?_, hw₁, hw₂⟩
  · -- membership
    intro z i'
    induction i' using Fin.lastCases with
    | last =>
      rw [hch_last]
      constructor
      · intro hz
        have hz' : z.1 ∈ (refineChain t l).map Prod.fst := by
          rw [hsplit, List.map_append]; exact List.mem_append_right _ hz
        have hzl := (hK1 z).mp hz'
        have hnot : z.1 ∉ Lf.map Prod.fst := fun h ↦ List.disjoint_of_nodup_append hnodup h hz
        simp only [hlab', if_pos hzl, if_neg hnot]
      · intro hz
        have hzl : L.lab (Refine.parentND E t hE z) = e := by
          by_contra hne'
          simp only [hlab', if_neg hne'] at hz
          exact absurd hz (Fin.castSucc_lt_last _).ne
        have hnot : z.1 ∉ Lf.map Prod.fst := by
          intro hin
          simp only [hlab', if_pos hzl, if_pos hin] at hz
          exact absurd hz (Fin.castSucc_lt_last _).ne
        have hz' := (hK1 z).mpr hzl
        rw [hsplit, List.map_append] at hz'
        exact (List.mem_append.mp hz').resolve_left hnot
    | cast i =>
      by_cases hie : i = e
      · rw [hie, hch_e]
        constructor
        · intro hz
          have hz' : z.1 ∈ (refineChain t l).map Prod.fst := by
            rw [hsplit, List.map_append]; exact List.mem_append_left _ hz
          simp only [hlab', if_pos ((hK1 z).mp hz')]
          split_ifs with h'
          · rfl
          · exact absurd hz h'
        · intro hz
          by_cases hzl : L.lab (Refine.parentND E t hE z) = e
          · by_contra hnot
            simp only [hlab', if_pos hzl] at hz
            split_ifs at hz with h'
            · exact hnot h'
            · exact absurd hz.symm (Fin.castSucc_lt_last _).ne
          · simp only [hlab', if_neg hzl] at hz
            exact absurd (Fin.castSucc_injective _ hz) hzl
      · rw [hch_ne i hie, hK3]
        constructor
        · intro hz
          simp only [hlab', if_neg (hz ▸ hie : L.lab (Refine.parentND E t hE z) ≠ e), hz]
        · intro hz
          by_cases hzl : L.lab (Refine.parentND E t hE z) = e
          · exfalso
            simp only [hlab', if_pos hzl] at hz
            split_ifs at hz with h'
            · exact hie (Fin.castSucc_injective _ hz).symm
            · exact absurd hz.symm (Fin.castSucc_lt_last _).ne
          · simp only [hlab', if_neg hzl] at hz
            exact Fin.castSucc_injective _ hz
  · -- nodup
    intro i'
    induction i' using Fin.lastCases with
    | last => rw [hch_last]; exact hnodup.of_append_right
    | cast i =>
      by_cases hie : i = e
      · rw [hie, hch_e]; exact hnodup.of_append_left
      · rw [hch_ne i hie]; exact nodup_refineChain t (L.good i) (L.nodup i)
  · -- the links
    intro i'
    induction i' using Fin.lastCases with
    | last =>
      rw [hch_last]
      exact isChain_rightPart t hj htc hE hold (L.link e) hg fun c' hc' _ ↦
        freshOf_notMem_newV _ (fst_ne_of_mem_drop (L.nodup e) hj hc')
    | cast i =>
      by_cases hie : i = e
      · rw [hie, hch_e]
        exact isChain_leftPart t hj htc hE hold (L.link e) hg fun c' hc' _ ↦
          freshOf_notMem_newV _ (fst_ne_of_mem_take (L.nodup e) hj hc')
      · rw [hch_ne i hie]
        exact isChain_refineChain t hE hold (L.link i) (L.good i) fun c' hc' _ ↦
          freshOf_notMem_newV _ (hlx' i hie c' hc')
  · -- the first vertices
    intro i'
    induction i' using Fin.lastCases with
    | last =>
      rw [head_congr' hch_last _ hRt_ne, subdivide_tail_last, newV_last]
      rfl
    | cast i =>
      by_cases hie : i = e
      · subst hie
        rw [head_congr' hch_e _ hLf_ne, head_leftPart t hj htc (L.ne_nil i), L.head i,
          subdivide_tail_castSucc, newV_castSucc]
      · rw [head_congr' (hch_ne i hie) _ (refineChain_ne_nil t (L.ne_nil i)),
          head_refineChain t (L.ne_nil i), L.head i, subdivide_tail_castSucc, newV_castSucc]
  · -- the last vertices
    intro i'
    induction i' using Fin.lastCases with
    | last =>
      rw [getLast_congr' hch_last _ hRt_ne, last_rightPart t hj htc (L.ne_nil e), L.last e,
        subdivide_head_last, newV_castSucc]
    | cast i =>
      by_cases hie : i = e
      · subst hie
        rw [getLast_congr' hch_e _ hLf_ne, last_leftPart t hj htc, subdivide_head_castSucc,
          if_pos rfl, newV_last]
        rfl
      · rw [getLast_congr' (hch_ne i hie) _ (refineChain_ne_nil t (L.ne_nil i)),
          last_refineChain t (L.ne_nil i), L.last i, subdivide_head_castSucc, if_neg hie,
          newV_castSucc]
  · -- the lengths
    intro i'
    induction i' using Fin.lastCases with
    | last =>
      rw [hch_last, sum_rightPart t hw₁ hw₂ hg hj htc, hfar]
      have hl3 : (l.map f).sum = pre + f c + ((l.drop (j + 1)).map f).sum := by
        conv_lhs => rw [← List.take_append_drop j l, List.drop_eq_getElem_cons hj]
        simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, hpre]
        ring
      have : ((l.drop (j + 1)).map fun c ↦ srcLen E L.w c.1) = (l.drop (j + 1)).map f := rfl
      rw [this]
      rw [htot] at hl3
      rw [ho]
      linarith
    | cast i =>
      by_cases hie : i = e
      · subst hie
        rw [hch_e, sum_leftPart t hw₁ hw₂ hg hj htc, hnear, ho]
        have : ((l.take j).map fun c ↦ srcLen E L.w c.1) = (l.take j).map f := rfl
        rw [this, ← hpre]
        ring
      · rw [hch_ne i hie, sum_refineChain t hw₁ hw₂ (L.good i), L.sum i, hy]
        unfold mergeRequest
        rw [if_neg hie]
  · -- the merge
    intro z
    simp only [hlab']
    split_ifs with h₁ h₂
    · rw [mergeOne_castSucc, h₁]
    · rw [mergeOne_last, h₁]
    · rw [mergeOne_castSucc]

end Forward

/-! ## 5. Any refinement is the forward one -/

section Analyze

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} {m q : ℕ} {C : Core m q}
  {V : Fin m → E.SourceVertex} {y : Fin q → ℚ}

theorem mergeOne_eq_self_iff {q : ℕ} (e : Fin q) (i' : Fin (q + 1)) :
    mergeOne e i' = e ↔ i' = e.castSucc ∨ i' = Fin.last q := by
  induction i' using Fin.lastCases with
  | last => simp [mergeOne_last]
  | cast i =>
    rw [mergeOne_castSucc]
    constructor
    · rintro rfl; exact Or.inl rfl
    · rintro (h | h)
      · exact Fin.castSucc_injective _ h
      · exact absurd h (Fin.castSucc_lt_last _).ne

theorem eq_castSucc_of_mergeOne {q : ℕ} {e i : Fin q} {i' : Fin (q + 1)} (h : mergeOne e i' = i)
    (hi : i ≠ e) : i' = i.castSucc := by
  induction i' using Fin.lastCases with
  | last => rw [mergeOne_last] at h; exact absurd h.symm hi
  | cast i'' => rw [mergeOne_castSucc] at h; rw [h]

/-- A sum over the surviving edges listed by a duplicate-free list of good oriented edges. -/
theorem sum_mem_list {M : Type*} [AddCommMonoid M] (l : List (OEdge E))
    (hg : ∀ c ∈ l, Good E c) (hl : (l.map Prod.fst).Nodup) (f : E.SourceEdge → M)
    [DecidablePred fun z : NonDanglingEdge E ↦ z.1 ∈ l.map Prod.fst] :
    (∑ z : NonDanglingEdge E, if z.1 ∈ l.map Prod.fst then f z.1 else 0) =
      (l.map fun c ↦ f c.1).sum := by
  classical
  have hmap : (l.map fun c ↦ f c.1) = (l.map Prod.fst).map f := by rw [List.map_map]; rfl
  rw [hmap, ← List.sum_toFinset f hl, ← Finset.sum_filter]
  have hnd : ∀ e ∈ (l.map Prod.fst).toFinset, ¬ IsDangling E e := by
    intro e he
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    exact (hg c hc).1
  refine Finset.sum_bij' (fun x _ ↦ x.1) (fun e he ↦ ⟨e, hnd e he⟩) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact List.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
  · intro e he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, List.mem_toFinset.mp he⟩
  · intro x _; rfl
  · intro e _; rfl
  · intro x _; rfl

/-- **Label data are constant along a chain.** -/
theorem LabelData.lab_chain (R : LabelData E C V y) {l : List (OEdge E)}
    (hl : l.IsChain (Link E V)) (hg : ∀ c ∈ l, Good E c) (hne : l ≠ []) :
    ∀ c (hc : c ∈ l), R.lab ⟨c.1, (hg c hc).1⟩ =
      R.lab ⟨(l.head hne).1, (hg _ (List.head_mem hne)).1⟩ := by
  induction l with
  | nil => exact absurd rfl hne
  | cons c₀ l ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · rfl
    · have hne' : l ≠ [] := List.ne_nil_of_mem hc'
      have ih' := ih hl.tail (fun c'' h ↦ hg c'' (List.mem_cons_of_mem _ h)) hne' c hc'
      rw [ih']
      obtain ⟨c₁, l', rfl⟩ := List.exists_cons_of_ne_nil hne'
      rw [List.isChain_cons_cons] at hl
      obtain ⟨⟨hlink, hin⟩, -⟩ := hl
      have hg₀ := hg c₀ (List.mem_cons_self ..)
      have hg₁ := hg c₁ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have hi₁ : Incident E c₁.1 c₀.2.2 := by rw [hlink]; exact hg₁.2.1
      exact (R.const ⟨c₀.1, hg₀.1⟩ ⟨c₁.1, hg₁.1⟩ c₀.2.2 hg₀.2.2.1 hi₁ hin).symm

variable (hE : E.Connected) (L : Layout E C V y) (e : Fin q) (hloop : C.tail e ≠ C.head e)
  {y' : Fin (q + 1) → ℚ} (h2 : 0 < y' (Fin.last q))
  (x : NonDanglingEdge E)
  (R : LabelData (refineDatum E x.1.1.1) (subdivide C e) (newV V x) y')
  (hmerge : ∀ z, mergeOne e (R.lab z) = L.lab (Refine.parentND E x.1.1.1 hE z))
  (hw₁ : ∀ e₀, e₀ ≠ x.1.1.1 → R.w (subdivOcc S x.1.1.1 (some e₀)) = L.w e₀)
  (hw₂ : R.w (subdivOcc S x.1.1.1 (some x.1.1.1)) + R.w (subdivOcc S x.1.1.1 none) =
    L.w x.1.1.1)

include hmerge in
/-- The mark edge lies on the slot of the mark. -/
theorem lab_markEdge : L.lab x = e := by
  classical
  have hinc := R.inc (Fin.last m) e.castSucc
  have hci : coreIncidence (subdivide C e) (Fin.last m) e.castSucc = 1 := by
    unfold coreIncidence
    rw [subdivide_tail_castSucc, subdivide_head_castSucc, if_pos rfl,
      if_neg (Fin.castSucc_lt_last _).ne, if_pos rfl]
  rw [hci] at hinc
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [hinc]; norm_num)
  obtain ⟨hzi, hzl⟩ := (Finset.mem_filter.mp hz).2
  rw [newV_last, Refine.freshOf, Refine.incident_freshSV_iff] at hzi
  have hp : Refine.parentND E x.1.1.1 hE z = x := by
    apply Subtype.ext
    show Refine.parentSE E x.1.1.1 z.1 = x.1
    rcases hzi with h | h <;> rw [h]
    · rw [Refine.parentSE_halfNone]; rfl
    · rw [Refine.parentSE_halfSome]; rfl
  rw [← hp, ← hmerge, hzl, mergeOne_castSucc]

include hmerge in
theorem exists_index :
    ∃ j, ∃ hj : j < (L.chain e).length, (L.chain e)[j].1 = x.1 := by
  have hmem := (L.mem x e).mpr (lab_markEdge hE L e x R hmerge)
  obtain ⟨c, hc, hcx⟩ := List.mem_map.mp hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
  exact ⟨j, hj, hcx⟩

include hloop h2 hmerge hw₁ hw₂ in
/-- **The analysis of a refinement**: the classes of the two pieces of the slot of the mark are
the two parts of its refined chain, and the piece from the tail to the mark has its requested
length. -/
theorem analyze {j : ℕ} (hj : j < (L.chain e).length)
    (hjx : (L.chain e)[j].1 = x.1) :
    (∀ z, z.1 ∈ (leftPart x.1.1.1 (L.chain e) j hj (by rw [hjx])).map Prod.fst →
      R.lab z = e.castSucc) ∧
    (∀ z, z.1 ∈ (rightPart x.1.1.1 (L.chain e) j hj (by rw [hjx])).map Prod.fst →
      R.lab z = Fin.last q) ∧
    srcLen _ R.w (nearOE x.1.1.1 (L.chain e)[j] (by rw [hjx])).1 =
      y' e.castSucc - (((L.chain e).take j).map fun c ↦ srcLen E L.w c.1).sum := by
  classical
  set t := x.1.1.1 with ht
  set l := L.chain e with hl
  have hg := L.good e
  have htc : l[j].1.1.1 = t := by rw [hjx]
  set Lf := leftPart t l j hj htc with hLf
  set Rt := rightPart t l j hj htc with hRt
  have hsplit : refineChain t l = Lf ++ Rt := refineChain_split t hj htc
  have hold : ∀ v, v ∉ Set.range V → Refine.oldSV E t v ∉ Set.range (newV V x) :=
    fun v hv ↦ oldSV_notMem_newV hv
  have hLfc := isChain_leftPart t hj htc hE hold (L.link e) hg fun c' hc' _ ↦
    freshOf_notMem_newV _ (hjx ▸ fst_ne_of_mem_take (L.nodup e) hj hc')
  have hRtc := isChain_rightPart t hj htc hE hold (L.link e) hg fun c' hc' _ ↦
    freshOf_notMem_newV _ (hjx ▸ fst_ne_of_mem_drop (L.nodup e) hj hc')
  have hgl := good_refineChain t hE hg
  rw [hsplit] at hgl
  have hgLf : ∀ c ∈ Lf, Good _ c := fun c hc ↦ hgl c (List.mem_append_left _ hc)
  have hgRt : ∀ c ∈ Rt, Good _ c := fun c hc ↦ hgl c (List.mem_append_right _ hc)
  have hnodup : (Lf.map Prod.fst ++ Rt.map Prod.fst).Nodup := by
    rw [← List.map_append, ← hsplit]
    exact nodup_refineChain t hg (L.nodup e)
  have hK1 : ∀ z : NonDanglingEdge (refineDatum E t),
      z.1 ∈ (refineChain t l).map Prod.fst ↔ L.lab (Refine.parentND E t hE z) = e := by
    intro z
    rw [mem_refineChain_iff t hg, ← L.mem]
    rfl
  -- labels on the parts lie over `e`
  have hover : ∀ z : NonDanglingEdge (refineDatum E t), z.1 ∈ (refineChain t l).map Prod.fst →
      R.lab z = e.castSucc ∨ R.lab z = Fin.last q := by
    intro z hz
    rw [← mergeOne_eq_self_iff, hmerge]
    exact (hK1 z).mp hz
  -- a list element as a surviving edge
  have hmemL : ∀ c (hc : c ∈ Lf), (⟨c.1, (hgLf c hc).1⟩ : NonDanglingEdge _).1 ∈
      (refineChain t l).map Prod.fst := fun c hc ↦ by
    rw [hsplit, List.map_append]; exact List.mem_append_left _ (List.mem_map_of_mem hc)
  have hmemR : ∀ c (hc : c ∈ Rt), (⟨c.1, (hgRt c hc).1⟩ : NonDanglingEdge _).1 ∈
      (refineChain t l).map Prod.fst := fun c hc ↦ by
    rw [hsplit, List.map_append]; exact List.mem_append_right _ (List.mem_map_of_mem hc)
  -- the left part carries `castSucc e`: its first edge meets `V (tail e)`, where `last` does not
  have hLf_ne : Lf ≠ [] := leftPart_ne_nil t hj htc
  have hc₀ := hgLf _ (List.head_mem hLf_ne)
  have hlabL₀ : R.lab ⟨(Lf.head hLf_ne).1, hc₀.1⟩ = e.castSucc := by
    rcases hover _ (hmemL _ (List.head_mem hLf_ne)) with h | h
    · exact h
    · exfalso
      have hinc := R.inc (C.tail e).castSucc (Fin.last q)
      have hci : coreIncidence (subdivide C e) (C.tail e).castSucc (Fin.last q) = 0 := by
        unfold coreIncidence
        rw [subdivide_tail_last, subdivide_head_last, if_neg (Fin.castSucc_lt_last _).ne',
          if_neg (fun h ↦ hloop (Fin.castSucc_injective _ h).symm)]
      rw [hci, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hinc
      refine hinc (Finset.mem_univ ⟨(Lf.head hLf_ne).1, hc₀.1⟩) ⟨?_, h⟩
      rw [newV_castSucc, ← L.head e]
      have := head_leftPart t hj htc (L.ne_nil e)
      rw [← this]
      exact hc₀.2.1
  have hlabL : ∀ c (hc : c ∈ Lf), R.lab ⟨c.1, (hgLf c hc).1⟩ = e.castSucc := by
    intro c hc
    rw [R.lab_chain hLfc hgLf hLf_ne c hc, hlabL₀]
  have hlabL' : ∀ z : NonDanglingEdge (refineDatum E t), z.1 ∈ Lf.map Prod.fst →
      R.lab z = e.castSucc := by
    intro z hz
    obtain ⟨c, hc, hcz⟩ := List.mem_map.mp hz
    have := hlabL c hc
    rwa [show (⟨c.1, (hgLf c hc).1⟩ : NonDanglingEdge _) = z from Subtype.ext hcz] at this
  -- the right part carries `last`, or the class of `last` would be empty
  have hRt_ne : Rt ≠ [] := List.cons_ne_nil _ _
  have hlabR' : ∀ z : NonDanglingEdge (refineDatum E t), z.1 ∈ Rt.map Prod.fst →
      R.lab z = Fin.last q := by
    have hd₀ := hgRt _ (List.head_mem hRt_ne)
    have hR₀ : R.lab ⟨(Rt.head hRt_ne).1, hd₀.1⟩ = Fin.last q := by
      rcases hover _ (hmemR _ (List.head_mem hRt_ne)) with h | h
      · exfalso
        have hall : ∀ c (hc : c ∈ Rt), R.lab ⟨c.1, (hgRt c hc).1⟩ = e.castSucc := by
          intro c hc
          rw [R.lab_chain hRtc hgRt hRt_ne c hc, h]
        have hempty : ∀ z : NonDanglingEdge (refineDatum E t), R.lab z ≠ Fin.last q := by
          intro z hz
          have hz' : z.1 ∈ (refineChain t l).map Prod.fst := by
            rw [hK1, ← hmerge, hz, mergeOne_last]
          rw [hsplit, List.map_append] at hz'
          rcases List.mem_append.mp hz' with hz'' | hz''
          · exact absurd (hz.symm.trans (hlabL' z hz'')) (Fin.castSucc_lt_last _).ne'
          · obtain ⟨c, hc, hcz⟩ := List.mem_map.mp hz''
            have := hall c hc
            rw [show (⟨c.1, (hgRt c hc).1⟩ : NonDanglingEdge _) = z from Subtype.ext hcz] at this
            exact absurd (hz.symm.trans this) (Fin.castSucc_lt_last _).ne'
        have hlen := R.len (Fin.last q)
        rw [Finset.sum_eq_zero fun z _ ↦ if_neg (hempty z)] at hlen
        linarith
      · exact h
    intro z hz
    obtain ⟨c, hc, hcz⟩ := List.mem_map.mp hz
    have := R.lab_chain hRtc hgRt hRt_ne c hc
    rw [hR₀, show (⟨c.1, (hgRt c hc).1⟩ : NonDanglingEdge _) = z from Subtype.ext hcz] at this
    exact this
  refine ⟨hlabL', hlabR', ?_⟩
  -- the length of the piece from the tail to the mark
  have hclass : ∀ z : NonDanglingEdge (refineDatum E t),
      R.lab z = e.castSucc ↔ z.1 ∈ Lf.map Prod.fst := by
    intro z
    refine ⟨fun hz ↦ ?_, hlabL' z⟩
    have hz' : z.1 ∈ (refineChain t l).map Prod.fst := by
      rw [hK1, ← hmerge, hz, mergeOne_castSucc]
    rw [hsplit, List.map_append] at hz'
    rcases List.mem_append.mp hz' with h | h
    · exact h
    · exact absurd (hz.symm.trans (hlabR' z h)) (Fin.castSucc_lt_last _).ne
  have hlen := R.len e.castSucc
  have hsum : (∑ z : NonDanglingEdge (refineDatum E t),
      if R.lab z = e.castSucc then srcLen _ R.w z.1 else 0) =
      (Lf.map fun c ↦ srcLen _ R.w c.1).sum := by
    rw [← sum_mem_list Lf hgLf hnodup.of_append_left]
    exact Finset.sum_congr rfl fun z _ ↦ by
      by_cases hz : R.lab z = e.castSucc
      · rw [if_pos hz, if_pos ((hclass z).mp hz)]
      · rw [if_neg hz, if_neg (fun h ↦ hz ((hclass z).mpr h))]
  rw [hsum, sum_leftPart t hw₁ hw₂ hg hj htc] at hlen
  linarith

end Analyze

/-! ## 6. Uniqueness of the refinement -/

section Unique

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} {m q : ℕ} {C : Core m q}
  {V : Fin m → E.SourceVertex} {y : Fin q → ℚ}

theorem prefix_le (l : List ℚ) (hnn : ∀ a ∈ l, 0 ≤ a) {i k : ℕ} (h : i ≤ k) :
    (l.take i).sum ≤ (l.take k).sum := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.sum_append]
  have : 0 ≤ ((l.drop i).take r).sum :=
    List.sum_nonneg fun a ha ↦ hnn a (List.mem_of_mem_drop (List.mem_of_mem_take ha))
  linarith

theorem srcLen_pos {S' : CFGraph} {E' : GluingDatum S' d} {w : S'.edges → ℚ}
    (hw : ∀ ε, 0 < w ε) (x : E'.SourceEdge) : 0 < srcLen E' w x :=
  div_pos (hw _) (sourceEdgeIndex_pos' x)

variable (hE : E.Connected) (L : Layout E C V y) (e : Fin q) (hloop : C.tail e ≠ C.head e)
  {y' : Fin (q + 1) → ℚ} (h2 : 0 < y' (Fin.last q))

include hloop h2 in
/-- **The mark edge is forced** when one of the two refinements has positive lengths. -/
theorem unique_markEdge (x₁ x₂ : NonDanglingEdge E)
    (R₁ : LabelData (refineDatum E x₁.1.1.1) (subdivide C e) (newV V x₁) y')
    (hm₁ : ∀ z, mergeOne e (R₁.lab z) = L.lab (Refine.parentND E x₁.1.1.1 hE z))
    (hw₁₁ : ∀ e₀, e₀ ≠ x₁.1.1.1 → R₁.w (subdivOcc S x₁.1.1.1 (some e₀)) = L.w e₀)
    (hw₁₂ : R₁.w (subdivOcc S x₁.1.1.1 (some x₁.1.1.1)) + R₁.w (subdivOcc S x₁.1.1.1 none) =
      L.w x₁.1.1.1)
    (hpos : ∀ ε, 0 < R₁.w ε)
    (R₂ : LabelData (refineDatum E x₂.1.1.1) (subdivide C e) (newV V x₂) y')
    (hm₂ : ∀ z, mergeOne e (R₂.lab z) = L.lab (Refine.parentND E x₂.1.1.1 hE z))
    (hw₂₁ : ∀ e₀, e₀ ≠ x₂.1.1.1 → R₂.w (subdivOcc S x₂.1.1.1 (some e₀)) = L.w e₀)
    (hw₂₂ : R₂.w (subdivOcc S x₂.1.1.1 (some x₂.1.1.1)) + R₂.w (subdivOcc S x₂.1.1.1 none) =
      L.w x₂.1.1.1) : x₁ = x₂ := by
  set l := L.chain e with hl
  have hnn : ∀ a ∈ l.map (fun c : OEdge E ↦ srcLen E L.w c.1), 0 ≤ a := fun a ha ↦ by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ha
    exact srcLen_nonneg L.w_nonneg _
  obtain ⟨j₁, hj₁, hjx₁⟩ := exists_index hE L e x₁ R₁ hm₁
  obtain ⟨j₂, hj₂, hjx₂⟩ := exists_index hE L e x₂ R₂ hm₂
  obtain ⟨-, -, hn₁⟩ := analyze hE L e hloop h2 x₁ R₁ hm₁ hw₁₁ hw₁₂ hj₁ hjx₁
  obtain ⟨-, -, hn₂⟩ := analyze hE L e hloop h2 x₂ R₂ hm₂ hw₂₁ hw₂₂ hj₂ hjx₂
  have hc₁ := L.good e _ (List.getElem_mem hj₁)
  have hc₂ := L.good e _ (List.getElem_mem hj₂)
  have hs₁ := srcLen_near_add_far x₁.1.1.1 hw₁₁ hw₁₂ hc₁ (by rw [hjx₁])
  have hs₂ := srcLen_near_add_far x₂.1.1.1 hw₂₁ hw₂₂ hc₂ (by rw [hjx₂])
  have hp₁ := srcLen_pos hpos (nearOE x₁.1.1.1 l[j₁] (by rw [hjx₁])).1
  have hq₁ := srcLen_pos hpos (farOE x₁.1.1.1 l[j₁] (by rw [hjx₁])).1
  have hp₂ := srcLen_nonneg R₂.w_nonneg (nearOE x₂.1.1.1 l[j₂] (by rw [hjx₂])).1
  have hq₂ := srcLen_nonneg R₂.w_nonneg (farOE x₂.1.1.1 l[j₂] (by rw [hjx₂])).1
  have hP : ∀ k (hk : k < l.length),
      ((l.take (k + 1)).map fun c : OEdge E ↦ srcLen E L.w c.1).sum =
        ((l.take k).map fun c : OEdge E ↦ srcLen E L.w c.1).sum + srcLen E L.w l[k].1 := by
    intro k hk
    rw [List.map_take, List.map_take, List.sum_take_succ _ _ (by simpa using hk),
      List.getElem_map]
  have hP₁ := hP j₁ hj₁
  have hP₂ := hP j₂ hj₂
  have hmono : ∀ {i k : ℕ}, i ≤ k →
      ((l.take i).map fun c : OEdge E ↦ srcLen E L.w c.1).sum ≤
        ((l.take k).map fun c : OEdge E ↦ srcLen E L.w c.1).sum := by
    intro i k hik
    have := prefix_le _ hnn hik
    rwa [← List.map_take, ← List.map_take] at this
  have hj : j₁ = j₂ := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hmono (show j₁ + 1 ≤ j₂ by omega)
      linarith
    · have := hmono (show j₂ + 1 ≤ j₁ by omega)
      linarith
  subst hj
  exact Subtype.ext (hjx₁.symm.trans hjx₂)

include hloop h2 in
/-- **The labels and lengths of a refinement are forced** by the mark edge. -/
theorem unique_data (x : NonDanglingEdge E)
    (R₁ R₂ : LabelData (refineDatum E x.1.1.1) (subdivide C e) (newV V x) y')
    (hm₁ : ∀ z, mergeOne e (R₁.lab z) = L.lab (Refine.parentND E x.1.1.1 hE z))
    (hw₁₁ : ∀ e₀, e₀ ≠ x.1.1.1 → R₁.w (subdivOcc S x.1.1.1 (some e₀)) = L.w e₀)
    (hw₁₂ : R₁.w (subdivOcc S x.1.1.1 (some x.1.1.1)) + R₁.w (subdivOcc S x.1.1.1 none) =
      L.w x.1.1.1)
    (hm₂ : ∀ z, mergeOne e (R₂.lab z) = L.lab (Refine.parentND E x.1.1.1 hE z))
    (hw₂₁ : ∀ e₀, e₀ ≠ x.1.1.1 → R₂.w (subdivOcc S x.1.1.1 (some e₀)) = L.w e₀)
    (hw₂₂ : R₂.w (subdivOcc S x.1.1.1 (some x.1.1.1)) + R₂.w (subdivOcc S x.1.1.1 none) =
      L.w x.1.1.1) :
    R₁.lab = R₂.lab ∧ R₁.w = R₂.w := by
  classical
  set t := x.1.1.1 with ht
  set l := L.chain e with hl
  obtain ⟨j, hj, hjx⟩ := exists_index hE L e x R₁ hm₁
  obtain ⟨hL₁, hR₁, hn₁⟩ := analyze hE L e hloop h2 x R₁ hm₁ hw₁₁ hw₁₂ hj hjx
  obtain ⟨hL₂, hR₂, hn₂⟩ := analyze hE L e hloop h2 x R₂ hm₂ hw₂₁ hw₂₂ hj hjx
  have htc : l[j].1.1.1 = t := by rw [hjx]
  have hsplit := refineChain_split t hj htc
  have hg := L.good e
  refine ⟨funext fun z ↦ ?_, funext fun ε ↦ ?_⟩
  · by_cases hz : L.lab (Refine.parentND E t hE z) = e
    · have hz' : z.1 ∈ (refineChain t l).map Prod.fst := by
        rw [mem_refineChain_iff t hg]
        exact (L.mem (Refine.parentND E t hE z) e).mpr hz
      rw [hsplit, List.map_append] at hz'
      rcases List.mem_append.mp hz' with h | h
      · rw [hL₁ z h, hL₂ z h]
      · rw [hR₁ z h, hR₂ z h]
    · rw [eq_castSucc_of_mergeOne (hm₁ z) hz, eq_castSucc_of_mergeOne (hm₂ z) hz]
  · -- the lengths: off `t` they are those of `L`; on the halves of `t`, the near half is forced
    have hidx := sourceEdgeIndex_pos' (E := E) l[j].1
    have hnear : R₁.w (pieceT t l[j].2.1.1.1 t) = R₂.w (pieceT t l[j].2.1.1.1 t) := by
      have e₁ := hn₁
      have e₂ := hn₂
      rw [← e₂] at e₁
      simp only [nearOE, srcLen_piece] at e₁
      rw [div_left_inj' (ne_of_gt hidx)] at e₁
      rw [htc] at e₁
      exact e₁
    obtain ⟨o, rfl⟩ := (subdivOcc S t).surjective ε
    have hcase : ∀ R : LabelData (refineDatum E t) (subdivide C e) (newV V x) y',
        R.w (subdivOcc S t (some t)) + R.w (subdivOcc S t none) = L.w t →
        (R.w (subdivOcc S t (some t)) = if pieceT t l[j].2.1.1.1 t = subdivOcc S t (some t)
          then R.w (pieceT t l[j].2.1.1.1 t) else L.w t - R.w (pieceT t l[j].2.1.1.1 t)) ∧
        (R.w (subdivOcc S t none) = if pieceT t l[j].2.1.1.1 t = subdivOcc S t none
          then R.w (pieceT t l[j].2.1.1.1 t) else L.w t - R.w (pieceT t l[j].2.1.1.1 t)) := by
      intro R hR
      have hu : l[j].2.1.1.1 = (t : S.V × S.V).1 ∨ l[j].2.1.1.1 = (t : S.V × S.V).2 := by
        rcases (hg _ (List.getElem_mem hj)).ends_cases with ⟨hu, -⟩ | ⟨hu, -⟩
        · left; rw [hu]; show (l[j].1.1.1 : S.V × S.V).1 = _; rw [htc]
        · right; rw [hu]; show (l[j].1.1.1 : S.V × S.V).2 = _; rw [htc]
      have hsn : subdivOcc S t (some t) ≠ subdivOcc S t none := fun h ↦
        absurd ((subdivOcc S t).injective h) (by simp)
      rcases hu with hu | hu
      · rw [hu, pieceT_fst, if_pos rfl, if_neg hsn]
        exact ⟨rfl, by linarith⟩
      · rw [hu, pieceT_snd, if_neg hsn.symm, if_pos rfl]
        exact ⟨by linarith, rfl⟩
    cases o with
    | none =>
      rw [(hcase R₁ hw₁₂).2, (hcase R₂ hw₂₂).2, hnear]
    | some e₀ =>
      by_cases he : e₀ = t
      · subst he
        rw [(hcase R₁ hw₁₂).1, (hcase R₂ hw₂₂).1, hnear]
      · rw [hw₁₁ e₀ he, hw₂₁ e₀ he]

end Unique

/-! ## 7. Merging label data back at a mark -/

section Merge

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} {m q : ℕ} {C : Core m q}
  {V : Fin m → E.SourceVertex}

theorem sum_ite_fibre {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α] [AddCommMonoid M]
    (g : β → α) (P : α → Prop) [DecidablePred P] (G : β → M) :
    (∑ a, if P a then ∑ b, (if g b = a then G b else 0) else 0) =
      ∑ b, if P (g b) then G b else 0 := by
  have h1 : ∀ a, (if P a then ∑ b, (if g b = a then G b else 0) else 0) =
      ∑ b, if g b = a then (if P a then G b else 0) else 0 := by
    intro a
    split_ifs with ha
    · exact Finset.sum_congr rfl fun b _ ↦ by split_ifs <;> rfl
    · exact (Finset.sum_eq_zero fun b _ ↦ by split_ifs <;> rfl).symm
  rw [Finset.sum_congr rfl fun a _ ↦ h1 a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.sum_ite_eq]
  simp

/-- The incidences of a subdivided core, merged back. -/
theorem sum_coreIncidence_subdivide (C : Core m q) (e : Fin q) (a : Fin m) (i : Fin q) :
    (∑ i' : Fin (q + 1), if mergeOne e i' = i then
      coreIncidence (subdivide C e) a.castSucc i' else 0) = coreIncidence C a i := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [mergeOne_castSucc, mergeOne_last]
  rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
  unfold coreIncidence
  simp only [subdivide_tail_castSucc, subdivide_head_castSucc, subdivide_tail_last,
    subdivide_head_last, Fin.castSucc_inj, if_neg (Fin.castSucc_lt_last a).ne']
  by_cases hie : i = e
  · subst hie
    simp only [if_true, if_neg (Fin.castSucc_lt_last a).ne']
    ring
  · rw [if_neg hie, if_neg (Ne.symm hie)]
    simp

theorem coreIncidence_subdivide_last (C : Core m q) (e : Fin q) (i : Fin q) (hi : i ≠ e) :
    coreIncidence (subdivide C e) (Fin.last m) i.castSucc = 0 := by
  unfold coreIncidence
  rw [subdivide_tail_castSucc, subdivide_head_castSucc, if_neg hi,
    if_neg (Fin.castSucc_lt_last _).ne, if_neg (Fin.castSucc_lt_last _).ne]

variable (hE : E.Connected) (e : Fin q) (x : NonDanglingEdge E) {y' : Fin (q + 1) → ℚ}

include hE in
open Classical in
/-- The fibre of the parent map. -/
theorem fibre_parentND (x' : NonDanglingEdge E) :
    (Finset.univ.filter fun z ↦ Refine.parentND E x.1.1.1 hE z = x') =
      if x'.1.1.1 = x.1.1.1 then
        {Refine.someHalfND E x.1.1.1 hE x', Refine.noneHalfND E x.1.1.1 hE x'}
      else {Refine.someHalfND E x.1.1.1 hE x'} := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl
    rcases Refine.eq_someHalfND_or_noneHalfND E x.1.1.1 hE z with h | ⟨ht, h⟩
    · split_ifs <;> simp [← h]
    · rw [if_pos ht]; simp [← h]
  · intro hz
    split_ifs at hz with ht
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Refine.parentND_someHalfND E _ hE x'
      · exact Refine.parentND_noneHalfND E _ hE ht
    · simp only [Finset.mem_singleton] at hz
      rw [hz]
      exact Refine.parentND_someHalfND E _ hE x'

include hE in
/-- **Merging label data back at a mark**: label data of the refinement at the mark edge give label
data of `E` at the merged request, with the merged labels and the summed lengths. -/
theorem merge (R : LabelData (refineDatum E x.1.1.1) (subdivide C e) (newV V x) y') :
    ∃ R₀ : LabelData E C V (mergeRequest e y'),
      (∀ z, mergeOne e (R.lab z) = R₀.lab (Refine.parentND E x.1.1.1 hE z)) ∧
      (∀ e₀, e₀ ≠ x.1.1.1 → R.w (subdivOcc S x.1.1.1 (some e₀)) = R₀.w e₀) ∧
      R.w (subdivOcc S x.1.1.1 (some x.1.1.1)) + R.w (subdivOcc S x.1.1.1 none) =
        R₀.w x.1.1.1 := by
  classical
  set lab₀ : NonDanglingEdge E → Fin q := fun x' ↦ mergeOne e (R.lab (Refine.someHalfND E x.1.1.1 hE x'))
    with hlab₀
  set w₀ : S.edges → ℚ := fun e₀ ↦
    R.w (subdivOcc S x.1.1.1 (some e₀)) + (if e₀ = x.1.1.1 then R.w (subdivOcc S x.1.1.1 none) else 0) with hw₀
  -- the two halves have one merged label
  have hhalves : ∀ x' : NonDanglingEdge E, x'.1.1.1 = x.1.1.1 →
      mergeOne e (R.lab (Refine.noneHalfND E x.1.1.1 hE x')) =
        mergeOne e (R.lab (Refine.someHalfND E x.1.1.1 hE x')) := by
    intro x' hx'
    obtain ⟨hs, hn⟩ := Refine.incident_halves E x.1.1.1 hE hx'
    by_cases hxx : x' = x
    · have hfx : Refine.freshOf E x.1.1.1 x'.1 hx' = Refine.freshOf E x.1.1.1 x.1 rfl := by
        subst hxx; rfl
      rw [hfx] at hs hn
      have hover : ∀ z : NonDanglingEdge (refineDatum E x.1.1.1),
          Incident _ z.1 (Refine.freshOf E x.1.1.1 x.1 rfl) → mergeOne e (R.lab z) = e := by
        intro z hz
        rw [mergeOne_eq_self_iff]
        by_contra hne
        push Not at hne
        induction h : R.lab z using Fin.lastCases with
        | last => exact hne.2 h
        | cast i =>
          have hie : i ≠ e := fun h' ↦ hne.1 (by rw [h, h'])
          have hinc := R.inc (Fin.last m) i.castSucc
          rw [coreIncidence_subdivide_last C e i hie, Finset.card_eq_zero,
            Finset.filter_eq_empty_iff] at hinc
          exact hinc (Finset.mem_univ z) ⟨by rw [newV_last]; exact hz, h⟩
      rw [hover _ hn, hover _ hs]
    · have hin : Inner (refineDatum E x.1.1.1) (newV V x) (Refine.freshOf E x.1.1.1 x'.1 hx') :=
        ⟨Refine.nonDanglingValency_freshOf E x.1.1.1 hE x' hx',
          freshOf_notMem_newV hx' (fun h ↦ hxx (Subtype.ext h))⟩
      rw [R.const _ _ _ hn hs hin]
  have hK : ∀ z, mergeOne e (R.lab z) = lab₀ (Refine.parentND E x.1.1.1 hE z) := by
    intro z
    rcases Refine.eq_someHalfND_or_noneHalfND E x.1.1.1 hE z with h | ⟨hp, h⟩
    · conv_lhs => rw [h]
    · conv_lhs => rw [h]
      exact hhalves _ hp
  refine ⟨{
    lab := lab₀
    w := w₀
    w_nonneg := ?_
    const := ?_
    inc := ?_
    len := ?_ }, hK, fun e₀ he ↦ ?_, ?_⟩
  · intro e₀
    simp only [hw₀]
    have h1 := R.w_nonneg (subdivOcc S x.1.1.1 (some e₀))
    have h2 := R.w_nonneg (subdivOcc S x.1.1.1 none)
    split_ifs <;> linarith
  · intro x₁ x₂ v hx₁ hx₂ hin
    have hin' : Inner (refineDatum E x.1.1.1) (newV V x) (Refine.oldSV E x.1.1.1 v) := by
      refine ⟨?_, oldSV_notMem_newV hin.2⟩
      rw [Refine.nonDanglingValency_oldSV E x.1.1.1 hE]
      exact hin.1
    have h := R.const (Refine.pieceND E x.1.1.1 hE v x₁) (Refine.pieceND E x.1.1.1 hE v x₂) _
      (Refine.incident_piece E x.1.1.1 hx₁) (Refine.incident_piece E x.1.1.1 hx₂) hin'
    have e₁ := hK (Refine.pieceND E x.1.1.1 hE v x₁)
    have e₂ := hK (Refine.pieceND E x.1.1.1 hE v x₂)
    rw [Refine.parentND_pieceND] at e₁ e₂
    rw [← e₁, ← e₂, h]
  · intro a i
    -- the edges at an old vertex are the pieces of those of `E`
    have hbij : (Finset.univ.filter fun x' : NonDanglingEdge E ↦
        Incident E x'.1 (V a) ∧ lab₀ x' = i).card =
        (Finset.univ.filter fun z : NonDanglingEdge (refineDatum E x.1.1.1) ↦
          Incident _ z.1 (Refine.oldSV E x.1.1.1 (V a)) ∧ mergeOne e (R.lab z) = i).card := by
      refine Finset.card_bij (fun x' _ ↦ Refine.pieceND E x.1.1.1 hE (V a) x') ?_ ?_ ?_
      · intro x' hx'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' ⊢
        refine ⟨Refine.incident_piece E x.1.1.1 hx'.1, ?_⟩
        rw [hK, Refine.parentND_pieceND]
        exact hx'.2
      · intro x₁ _ x₂ _ h
        rw [← Refine.parentND_pieceND E x.1.1.1 hE (V a) x₁, h, Refine.parentND_pieceND]
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨hzi, hzl⟩ := hz
        obtain ⟨hpi, hpt⟩ := (Refine.incident_oldSV_iff E x.1.1.1 z.1 (V a)).mp hzi
        refine ⟨Refine.parentND E x.1.1.1 hE z, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hpi, by rw [← hK]; exact hzl⟩
        · apply Subtype.ext
          apply Subtype.ext
          show (pieceT x.1.1.1 (V a).1.1 (Refine.parentSE E x.1.1.1 z.1).1.1, (Refine.parentSE E x.1.1.1 z.1).1.2) =
            z.1.1
          exact Prod.ext hpt.symm rfl
    rw [hbij, Finset.card_filter]
    have hsplit := sum_ite_fibre R.lab (fun i' ↦ mergeOne e i' = i)
      (fun z ↦ if Incident _ z.1 (Refine.oldSV E x.1.1.1 (V a)) then (1 : ℕ) else 0)
    have hl : (∑ z : NonDanglingEdge (refineDatum E x.1.1.1),
        if Incident _ z.1 (Refine.oldSV E x.1.1.1 (V a)) ∧ mergeOne e (R.lab z) = i then 1 else 0) =
        ∑ z : NonDanglingEdge (refineDatum E x.1.1.1), if mergeOne e (R.lab z) = i then
          (if Incident _ z.1 (Refine.oldSV E x.1.1.1 (V a)) then (1 : ℕ) else 0) else 0 :=
      Finset.sum_congr rfl fun z _ ↦ by by_cases h1 : mergeOne e (R.lab z) = i <;> simp [h1]
    rw [hl, ← hsplit, ← sum_coreIncidence_subdivide C e a i]
    refine Finset.sum_congr rfl fun i' _ ↦ ?_
    split_ifs with h1
    · rw [← R.inc a.castSucc i', Finset.card_filter, newV_castSucc]
      exact Finset.sum_congr rfl fun z _ ↦ by by_cases h2 : R.lab z = i' <;> simp [h2]
    · rfl
  · intro i
    -- the length of an edge of `E` is the sum over its pieces
    have hpieces : ∀ x' : NonDanglingEdge E, srcLen E w₀ x'.1 =
        ∑ z : NonDanglingEdge (refineDatum E x.1.1.1),
          if Refine.parentND E x.1.1.1 hE z = x' then srcLen _ R.w z.1 else 0 := by
      intro x'
      rw [← Finset.sum_filter, fibre_parentND hE x x']
      have hidx := sourceEdgeIndex_pos' (E := E) x'.1
      by_cases hx' : x'.1.1.1 = x.1.1.1
      · rw [if_pos hx', Finset.sum_pair (Refine.someHalfND_ne_noneHalfND E x.1.1.1 hE hx')]
        unfold srcLen
        rw [Refine.sourceEdgeIndex_someHalfND, Refine.sourceEdgeIndex_noneHalfND E x.1.1.1 hE hx',
          Refine.noneHalfND_val E x.1.1.1 hE hx', ← add_div]
        congr 1
        show w₀ x'.1.1.1 = R.w (subdivOcc S x.1.1.1 (some x'.1.1.1)) + R.w (subdivOcc S x.1.1.1 none)
        simp only [hw₀, if_pos hx']
      · rw [if_neg hx', Finset.sum_singleton]
        unfold srcLen
        rw [Refine.sourceEdgeIndex_someHalfND]
        congr 1
        show w₀ x'.1.1.1 = R.w (subdivOcc S x.1.1.1 (some x'.1.1.1))
        simp only [hw₀, if_neg hx', add_zero]
    have h1 : (∑ x' : NonDanglingEdge E, if lab₀ x' = i then srcLen E w₀ x'.1 else 0) =
        ∑ z : NonDanglingEdge (refineDatum E x.1.1.1),
          if mergeOne e (R.lab z) = i then srcLen _ R.w z.1 else 0 := by
      rw [Finset.sum_congr rfl fun x' _ ↦ by rw [hpieces x'],
        sum_ite_fibre (Refine.parentND E x.1.1.1 hE) (fun x' ↦ lab₀ x' = i)]
      exact Finset.sum_congr rfl fun z _ ↦ by rw [hK]
    rw [h1, ← sum_ite_fibre R.lab (fun i' ↦ mergeOne e i' = i)]
    have h2 : ∀ i', (∑ z : NonDanglingEdge (refineDatum E x.1.1.1),
        if R.lab z = i' then srcLen _ R.w z.1 else 0) = y' i' := R.len
    simp only [h2]
    rw [Fin.sum_univ_castSucc]
    simp only [mergeOne_castSucc, mergeOne_last]
    rw [Finset.sum_ite_eq' Finset.univ i, if_pos (Finset.mem_univ _)]
    unfold mergeRequest
    by_cases hie : i = e
    · rw [if_pos hie, if_pos hie.symm]
    · rw [if_neg hie, if_neg (Ne.symm hie), add_zero]
  · simp only [hw₀, if_neg he, add_zero]
  · simp [hw₀]

end Merge

/-! ## 8. Reversing a chain -/

section Reverse

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} {m : ℕ} {V : Fin m → E.SourceVertex}

/-- An oriented edge, traversed backwards. -/
def swapOE (c : OEdge E) : OEdge E := (c.1, c.2.2, c.2.1)

/-- A chain, traversed backwards. -/
def revChain (l : List (OEdge E)) : List (OEdge E) := (l.map swapOE).reverse

theorem good_swapOE {c : OEdge E} (h : Good E c) : Good E (swapOE c) :=
  ⟨h.1, h.2.2.1, h.2.1, h.2.2.2.symm⟩

theorem good_revChain {l : List (OEdge E)} (h : ∀ c ∈ l, Good E c) :
    ∀ c ∈ revChain l, Good E c := by
  intro c hc
  unfold revChain at hc
  obtain ⟨c', hc', rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
  exact good_swapOE (h c' hc')

theorem map_fst_revChain (l : List (OEdge E)) :
    (revChain l).map Prod.fst = (l.map Prod.fst).reverse := by
  unfold revChain
  rw [List.map_reverse, List.map_map]
  rfl

theorem isChain_revChain {l : List (OEdge E)} (h : l.IsChain (Link E V)) :
    (revChain l).IsChain (Link E V) := by
  unfold revChain
  rw [List.isChain_reverse, List.isChain_map]
  refine h.imp fun a b hab ↦ ⟨hab.1.symm, ?_⟩
  show Inner E V b.2.1
  rw [← hab.1]
  exact hab.2

theorem revChain_ne_nil {l : List (OEdge E)} (h : l ≠ []) : revChain l ≠ [] := by
  unfold revChain; simpa using h

theorem head_revChain {l : List (OEdge E)} (h : l ≠ []) :
    ((revChain l).head (revChain_ne_nil h)).2.1 = (l.getLast h).2.2 := by
  simp [revChain, swapOE, List.head_reverse, List.getLast_map]

theorem last_revChain {l : List (OEdge E)} (h : l ≠ []) :
    ((revChain l).getLast (revChain_ne_nil h)).2.2 = (l.head h).2.1 := by
  simp [revChain, swapOE, List.getLast_reverse, List.head_map]

theorem sum_revChain {S' : CFGraph} {E' : GluingDatum S' d} (l : List (OEdge E'))
    (f : E'.SourceEdge → ℚ) :
    ((revChain l).map fun c ↦ f c.1).sum = (l.map fun c ↦ f c.1).sum := by
  unfold revChain
  rw [List.map_reverse, List.sum_reverse, List.map_map]
  rfl

end Reverse

/-! ## 9. Three marks -/

section Three

variable {S : CFGraph} {d m : ℕ} {E : GluingDatum S d} (V : Fin m → E.SourceVertex)
  (x₀ : NonDanglingEdge E) (x₁ : NonDanglingEdge (refineDatum E x₀.1.1.1))
  (x₂ : NonDanglingEdge (refineDatum (refineDatum E x₀.1.1.1) x₁.1.1.1))

theorem newV₃_old (v : Fin m) :
    newV (newV (newV V x₀) x₁) x₂ v.castSucc.castSucc.castSucc =
      Refine.oldSV _ x₂.1.1.1 (Refine.oldSV _ x₁.1.1.1 (Refine.oldSV E x₀.1.1.1 (V v))) := by
  rw [newV_castSucc, newV_castSucc, newV_castSucc]

theorem newV₃_mark₀ :
    newV (newV (newV V x₀) x₁) x₂ (Fin.last m).castSucc.castSucc =
      Refine.oldSV _ x₂.1.1.1 (Refine.oldSV _ x₁.1.1.1 (Refine.freshOf E x₀.1.1.1 x₀.1 rfl)) := by
  rw [newV_castSucc, newV_castSucc, newV_last]

theorem newV₃_mark₁ :
    newV (newV (newV V x₀) x₁) x₂ (Fin.last (m + 1)).castSucc =
      Refine.oldSV _ x₂.1.1.1 (Refine.freshOf _ x₁.1.1.1 x₁.1 rfl) := by
  rw [newV_castSucc, newV_last]

theorem newV₃_mark₂ :
    newV (newV (newV V x₀) x₁) x₂ (Fin.last (m + 1 + 1)) =
      Refine.freshOf _ x₂.1.1.1 x₂.1 rfl := by
  rw [newV_last]

end Three

/-! ## 10. Three marks are forced -/

section Down

variable {S : CFGraph} {d : ℕ} {E : GluingDatum S d} {m q : ℕ} {C : Core m q}
  {V : Fin m → E.SourceVertex} (hE : E.Connected) (e : Fin q) (x : NonDanglingEdge E)
  {y' : Fin (q + 1) → ℚ}

/-- **The label data merged back at a mark** (`merge`, as a definition). -/
noncomputable def LabelData.down
    (R : LabelData (refineDatum E x.1.1.1) (subdivide C e) (newV V x) y') :
    LabelData E C V (mergeRequest e y') :=
  (merge hE e x R).choose

variable (R : LabelData (refineDatum E x.1.1.1) (subdivide C e) (newV V x) y')

theorem LabelData.down_lab (z : NonDanglingEdge (refineDatum E x.1.1.1)) :
    (R.down hE e x).lab (Refine.parentND E x.1.1.1 hE z) = mergeOne e (R.lab z) :=
  ((merge hE e x R).choose_spec.1 z).symm

theorem LabelData.down_w₁ (e₀ : S.edges) (he : e₀ ≠ x.1.1.1) :
    R.w (subdivOcc S x.1.1.1 (some e₀)) = (R.down hE e x).w e₀ :=
  (merge hE e x R).choose_spec.2.1 e₀ he

theorem LabelData.down_w₂ :
    R.w (subdivOcc S x.1.1.1 (some x.1.1.1)) + R.w (subdivOcc S x.1.1.1 none) =
      (R.down hE e x).w x.1.1.1 :=
  (merge hE e x R).choose_spec.2.2

theorem LabelData.down_pos (hpos : ∀ ε, 0 < R.w ε) : ∀ e₀, 0 < (R.down hE e x).w e₀ := by
  intro e₀
  by_cases he : e₀ = x.1.1.1
  · subst he
    rw [← R.down_w₂ hE e x]
    have := hpos (subdivOcc S x.1.1.1 none)
    have := hpos (subdivOcc S x.1.1.1 (some x.1.1.1))
    linarith
  · rw [← R.down_w₁ hE e x e₀ he]
    exact hpos _

end Down

section Forced

variable {S : CFGraph} {d : ℕ} {E₀ : GluingDatum S d} {m q : ℕ} {C₀ : Core m q}
  {V₀ : Fin m → E₀.SourceVertex}

/-- **One refinement is forced**: a refinement of a layout with positive lengths has the mark
edge of the forward step, and its label data are those of a layout of the refinement. -/
theorem step_forced (hE : E₀.Connected) (hV : Function.Injective V₀) {y : Fin q → ℚ}
    (L : Layout E₀ C₀ V₀ y) (e : Fin q) (hloop : C₀.tail e ≠ C₀.head e) {y' : Fin (q + 1) → ℚ}
    (hy : y = mergeRequest e y') (hy' : ∀ i, 0 < y' i) (x : NonDanglingEdge E₀)
    (R : LabelData (refineDatum E₀ x.1.1.1) (subdivide C₀ e) (newV V₀ x) y')
    (hpos : ∀ ε, 0 < R.w ε)
    (hlab : (R.down hE e x).lab = L.lab) (hw : (R.down hE e x).w = L.w) :
    ∃ L' : Layout (refineDatum E₀ x.1.1.1) (subdivide C₀ e) (newV V₀ x) y',
      L'.lab = R.lab ∧ L'.w = R.w := by
  have hm : ∀ z, mergeOne e (R.lab z) = L.lab (Refine.parentND E₀ x.1.1.1 hE z) := fun z ↦ by
    rw [← hlab, R.down_lab hE e x z]
  have hw₁ : ∀ e₀, e₀ ≠ x.1.1.1 → R.w (subdivOcc S x.1.1.1 (some e₀)) = L.w e₀ := fun e₀ he ↦ by
    rw [← hw, R.down_w₁ hE e x e₀ he]
  have hw₂ : R.w (subdivOcc S x.1.1.1 (some x.1.1.1)) + R.w (subdivOcc S x.1.1.1 none) =
      L.w x.1.1.1 := by
    rw [← hw, R.down_w₂ hE e x]
  obtain ⟨X, -, L', hm', hw₁', hw₂'⟩ := forward hE L e hy (hy' _) (hy' _).le
  have hX := unique_markEdge hE L e hloop (hy' _) x X R hm hw₁ hw₂ hpos (L'.toLabelData
    (newV_injective hV X)) hm' hw₁' hw₂'
  subst hX
  obtain ⟨h1, h2⟩ := unique_data hE L e hloop (hy' _) x R (L'.toLabelData (newV_injective hV x))
    hm hw₁ hw₂ hm' hw₁' hw₂'
  exact ⟨L', h1.symm, h2.symm⟩

/-- **The mark edge is forced** between two refinements, one with positive lengths. -/
theorem step_same (hE : E₀.Connected) {y : Fin q → ℚ}
    (L : Layout E₀ C₀ V₀ y) (e : Fin q) (hloop : C₀.tail e ≠ C₀.head e) {y' : Fin (q + 1) → ℚ}
    (hy' : ∀ i, 0 < y' i) (x x' : NonDanglingEdge E₀)
    (R : LabelData (refineDatum E₀ x.1.1.1) (subdivide C₀ e) (newV V₀ x) y')
    (hpos : ∀ ε, 0 < R.w ε)
    (hlab : (R.down hE e x).lab = L.lab) (hw : (R.down hE e x).w = L.w)
    (R' : LabelData (refineDatum E₀ x'.1.1.1) (subdivide C₀ e) (newV V₀ x') y')
    (hlab' : (R'.down hE e x').lab = L.lab) (hw' : (R'.down hE e x').w = L.w) : x = x' := by
  refine unique_markEdge hE L e hloop (hy' _) x x' R (fun z ↦ by rw [← hlab, R.down_lab hE e x z])
    (fun e₀ he ↦ by rw [← hw, R.down_w₁ hE e x e₀ he]) (by rw [← hw, R.down_w₂ hE e x]) hpos R'
    (fun z ↦ by rw [← hlab', R'.down_lab hE e x' z])
    (fun e₀ he ↦ by rw [← hw', R'.down_w₁ hE e x' e₀ he]) (by rw [← hw', R'.down_w₂ hE e x'])

/-- **Three marks are forced**: two candidates for the three mark edges over a layout, each with
label data of positive lengths at the third stage merging back to the layout, have the same
mark edges. -/
theorem three_forced (hE₀ : E₀.Connected) (hV₀ : Function.Injective V₀)
    (e₀ : Fin q) (e₁ : Fin (q + 1)) (e₂ : Fin (q + 1 + 1))
    (hl₀ : C₀.tail e₀ ≠ C₀.head e₀) (hl₁ : (subdivide C₀ e₀).tail e₁ ≠ (subdivide C₀ e₀).head e₁)
    (hl₂ : (subdivide (subdivide C₀ e₀) e₁).tail e₂ ≠ (subdivide (subdivide C₀ e₀) e₁).head e₂)
    {y₃ : Fin (q + 1 + 1 + 1) → ℚ} (hy₃ : ∀ i, 0 < y₃ i)
    (L₀ : Layout E₀ C₀ V₀ (mergeRequest e₀ (mergeRequest e₁ (mergeRequest e₂ y₃))))
    (x₀ : NonDanglingEdge E₀) (x₁ : NonDanglingEdge (refineDatum E₀ x₀.1.1.1))
    (x₂ : NonDanglingEdge (refineDatum (refineDatum E₀ x₀.1.1.1) x₁.1.1.1))
    (R₃ : LabelData (refineDatum (refineDatum (refineDatum E₀ x₀.1.1.1) x₁.1.1.1) x₂.1.1.1)
      (subdivide (subdivide (subdivide C₀ e₀) e₁) e₂) (newV (newV (newV V₀ x₀) x₁) x₂) y₃)
    (hpos : ∀ ε, 0 < R₃.w ε)
    (hlab : ((R₃.down (refineDatum_connected _ _ (refineDatum_connected _ _ hE₀)) e₂ x₂).down
      (refineDatum_connected _ _ hE₀) e₁ x₁ |>.down hE₀ e₀ x₀).lab = L₀.lab)
    (hw : ((R₃.down (refineDatum_connected _ _ (refineDatum_connected _ _ hE₀)) e₂ x₂).down
      (refineDatum_connected _ _ hE₀) e₁ x₁ |>.down hE₀ e₀ x₀).w = L₀.w)
    (x₀' : NonDanglingEdge E₀) (x₁' : NonDanglingEdge (refineDatum E₀ x₀'.1.1.1))
    (x₂' : NonDanglingEdge (refineDatum (refineDatum E₀ x₀'.1.1.1) x₁'.1.1.1))
    (R₃' : LabelData (refineDatum (refineDatum (refineDatum E₀ x₀'.1.1.1) x₁'.1.1.1) x₂'.1.1.1)
      (subdivide (subdivide (subdivide C₀ e₀) e₁) e₂) (newV (newV (newV V₀ x₀') x₁') x₂') y₃)
    (hlab' : ((R₃'.down (refineDatum_connected _ _ (refineDatum_connected _ _ hE₀)) e₂ x₂').down
      (refineDatum_connected _ _ hE₀) e₁ x₁' |>.down hE₀ e₀ x₀').lab = L₀.lab)
    (hw' : ((R₃'.down (refineDatum_connected _ _ (refineDatum_connected _ _ hE₀)) e₂ x₂').down
      (refineDatum_connected _ _ hE₀) e₁ x₁' |>.down hE₀ e₀ x₀').w = L₀.w) :
    x₀ = x₀' ∧ HEq x₁ x₁' ∧ HEq x₂ x₂' := by
  have hy₂ := mergeRequest_pos e₂ hy₃
  have hy₁ := mergeRequest_pos e₁ hy₂
  -- stage one
  have hE₁ := refineDatum_connected _ x₀.1.1.1 hE₀
  have h₀ := step_same hE₀ L₀ e₀ hl₀ hy₁ x₀ x₀' _
    (LabelData.down_pos _ _ _ _ (LabelData.down_pos _ _ _ _ hpos)) hlab hw _ hlab' hw'
  subst h₀
  obtain ⟨L₁, hL₁lab, hL₁w⟩ := step_forced hE₀ hV₀ L₀ e₀ hl₀ rfl hy₁ x₀ _
    (LabelData.down_pos _ _ _ _ (LabelData.down_pos _ _ _ _ hpos)) hlab hw
  have hV₁ := newV_injective hV₀ x₀
  -- the primed candidate has the same stage-one data
  obtain ⟨-, hd₁⟩ := unique_data hE₀ L₀ e₀ hl₀ (hy₁ _) x₀
    ((R₃.down (refineDatum_connected _ _ hE₁) e₂ x₂).down hE₁ e₁ x₁)
    ((R₃'.down (refineDatum_connected _ _ hE₁) e₂ x₂').down hE₁ e₁ x₁')
    (fun z ↦ by rw [← hlab, LabelData.down_lab]) (fun e₀' he ↦ by rw [← hw, LabelData.down_w₁ _ _ _ _ _ he])
    (by rw [← hw, LabelData.down_w₂]) (fun z ↦ by rw [← hlab', LabelData.down_lab])
    (fun e₀' he ↦ by rw [← hw', LabelData.down_w₁ _ _ _ _ _ he]) (by rw [← hw', LabelData.down_w₂])
  obtain ⟨hd₁lab, -⟩ := unique_data hE₀ L₀ e₀ hl₀ (hy₁ _) x₀
    ((R₃.down (refineDatum_connected _ _ hE₁) e₂ x₂).down hE₁ e₁ x₁)
    ((R₃'.down (refineDatum_connected _ _ hE₁) e₂ x₂').down hE₁ e₁ x₁')
    (fun z ↦ by rw [← hlab, LabelData.down_lab]) (fun e₀' he ↦ by rw [← hw, LabelData.down_w₁ _ _ _ _ _ he])
    (by rw [← hw, LabelData.down_w₂]) (fun z ↦ by rw [← hlab', LabelData.down_lab])
    (fun e₀' he ↦ by rw [← hw', LabelData.down_w₁ _ _ _ _ _ he]) (by rw [← hw', LabelData.down_w₂])
  -- stage two
  have hE₂ := refineDatum_connected _ x₁.1.1.1 hE₁
  have h₁ := step_same hE₁ L₁ e₁ hl₁ hy₂ x₁ x₁' _ (LabelData.down_pos _ _ _ _ hpos) hL₁lab.symm
    hL₁w.symm _ (hd₁lab.symm.trans hL₁lab.symm) (hd₁.symm.trans hL₁w.symm)
  subst h₁
  obtain ⟨L₂, hL₂lab, hL₂w⟩ := step_forced hE₁ hV₁ L₁ e₁ hl₁ rfl hy₂ x₁ _
    (LabelData.down_pos _ _ _ _ hpos) hL₁lab.symm hL₁w.symm
  have hV₂ := newV_injective hV₁ x₁
  obtain ⟨hd₂lab, hd₂⟩ := unique_data hE₁ L₁ e₁ hl₁ (hy₂ _) x₁
    (R₃.down hE₂ e₂ x₂) (R₃'.down hE₂ e₂ x₂')
    (fun z ↦ by rw [hL₁lab, LabelData.down_lab])
    (fun e₀' he ↦ by rw [hL₁w, LabelData.down_w₁ _ _ _ _ _ he]) (by rw [hL₁w, LabelData.down_w₂])
    (fun z ↦ by rw [hL₁lab, hd₁lab, LabelData.down_lab])
    (fun e₀' he ↦ by rw [hL₁w, hd₁, LabelData.down_w₁ _ _ _ _ _ he])
    (by rw [hL₁w, hd₁, LabelData.down_w₂])
  -- stage three
  have h₂ := step_same hE₂ L₂ e₂ hl₂ hy₃ x₂ x₂' R₃ hpos hL₂lab.symm hL₂w.symm R₃'
    (hd₂lab.symm.trans hL₂lab.symm) (hd₂.symm.trans hL₂w.symm)
  subst h₂
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- **The labels merged back at three marks**, at the `some`-pieces. -/
theorem LabelData.down₃_lab (hE₀ : E₀.Connected) (e₀ : Fin q) (e₁ : Fin (q + 1))
    (e₂ : Fin (q + 1 + 1)) {y₃ : Fin (q + 1 + 1 + 1) → ℚ}
    (x₀ : NonDanglingEdge E₀) (x₁ : NonDanglingEdge (refineDatum E₀ x₀.1.1.1))
    (x₂ : NonDanglingEdge (refineDatum (refineDatum E₀ x₀.1.1.1) x₁.1.1.1))
    (R₃ : LabelData (refineDatum (refineDatum (refineDatum E₀ x₀.1.1.1) x₁.1.1.1) x₂.1.1.1)
      (subdivide (subdivide (subdivide C₀ e₀) e₁) e₂) (newV (newV (newV V₀ x₀) x₁) x₂) y₃)
    (x : NonDanglingEdge E₀) :
    ((R₃.down (refineDatum_connected _ _ (refineDatum_connected _ _ hE₀)) e₂ x₂).down
      (refineDatum_connected _ _ hE₀) e₁ x₁ |>.down hE₀ e₀ x₀).lab x =
      mergeOne e₀ (mergeOne e₁ (mergeOne e₂ (R₃.lab
        (Refine.someHalfND _ x₂.1.1.1 (refineDatum_connected _ _ (refineDatum_connected _ _ hE₀))
          (Refine.someHalfND _ x₁.1.1.1 (refineDatum_connected _ _ hE₀)
            (Refine.someHalfND E₀ x₀.1.1.1 hE₀ x)))))) := by
  rw [← LabelData.down_lab, ← LabelData.down_lab, ← LabelData.down_lab,
    Refine.parentND_someHalfND, Refine.parentND_someHalfND, Refine.parentND_someHalfND]

end Forced










end Chains

end GenusSixExistence.Tripod.Gluing

end
