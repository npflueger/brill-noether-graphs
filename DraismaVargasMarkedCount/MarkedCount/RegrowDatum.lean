module

public import DraismaVargasMarkedCount.MarkedCount.RegrowTarget

@[expose] public section

/-!
# Regrowth, part 2: the regrown datum

A `Branching D k` records, for `k` source vertices `mark j` of a datum `D` (the marks), a second
sheet `other j` in the block of `mark j`. `regrowDatum β` is the datum over
`regrowTarget T β.x` (`β.x j` the image of mark `j`) with

* the partitions of `D` over the old vertices and edges;
* `P j := pair (a j) (other j)` (`a j` the representative sheet of `mark j`) over the bridge edge
  `t_b j`, at the middle vertex `u'_j` and at the tip `v_{C,j}`;
* the discrete partition over the leaf edge `t_l j`.

This is `Gluing.leafDatum` twice per mark, with the first leaf edge carrying `pair` instead of the
discrete partition.

Its source (`oldSV`, `midSV`, `tipSV`; `oldSE`, `bridgeSE`, `leafSE`) is the source of `D`
together with, per mark, the vertex `w j` (the block `{a, b}` over `u'_j`), the vertex `C j` (the
block `{a, b}` over the tip), the bridge `eb j` from `mark j` to `w j`, two parallel leaf edges
`e₁ j, e₂ j` from `w j` to `C j`, and one dangling path of length two in every other sheet.

Proved here: the source dictionaries and the incidence table, **Riemann--Hurwitz**
(`riemannHurwitz_regrowDatum`: at the mark `r⁺ = r - 1`, so ramification at the marks is what is
needed), **connectedness** and the **genus**, `g(R) = g(D) + k`.
-/

namespace DraismaVargas.Count.MarkedCount.Regrow

noncomputable section

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open GenusSixExistence.Tripod.Gluing (SheetOps.pair)

variable {T : CFGraph.{0}} {d k : ℕ}

/-! ## 1.  The partition `pair a b` -/

section Pair

variable {a b : Fin d}

theorem pair_repr (a b i : Fin d) : (SheetOps.pair a b).repr i = if i = b then a else i := rfl

theorem pair_repr_eq_self_iff (hab : a ≠ b) (i : Fin d) :
    (SheetOps.pair a b).repr i = i ↔ i ≠ b := by
  rw [pair_repr]
  by_cases hi : i = b
  · subst hi; simp [hab]
  · simp [hi]

theorem pair_rel_iff (hab : a ≠ b) (i j : Fin d) :
    (SheetOps.pair a b).Rel i j ↔ i = j ∨ ((i = a ∨ i = b) ∧ (j = a ∨ j = b)) := by
  unfold SheetPartition.Rel
  rw [pair_repr, pair_repr]
  by_cases hi : i = b <;> by_cases hj : j = b <;> simp only [hi, hj, ite_true, ite_false] <;>
    subst_vars <;> aesop

theorem pair_rel_left_iff (hab : a ≠ b) (i : Fin d) :
    (SheetOps.pair a b).Rel i a ↔ i = a ∨ i = b := by
  rw [pair_rel_iff hab]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact h
  · intro h; exact Or.inr ⟨h, Or.inl rfl⟩

theorem pair_rel_self (a b : Fin d) : (SheetOps.pair a b).Rel a b := by
  unfold SheetPartition.Rel
  rw [pair_repr, pair_repr]
  simp

/-- `pair a b` refines every partition in which `a` and `b` lie in one block. -/
theorem pair_refines {Q : SheetPartition d} (hQ : Q.Rel a b) : (SheetOps.pair a b).Refines Q := by
  intro i j hij
  unfold SheetPartition.Rel at hij
  rw [pair_repr, pair_repr] at hij
  by_cases hi : i = b <;> by_cases hj : j = b <;> simp only [hi, hj, ite_true, ite_false] at hij <;>
    subst_vars
  · rfl
  · exact hQ.symm
  · exact hQ
  · rfl

/-- The blocks of `pair a b` are the sheets other than `b`. -/
theorem card_blocks_pair (hab : a ≠ b) : Fintype.card (SheetOps.pair a b).Blocks = d - 1 := by
  classical
  change Fintype.card {i : Fin d // (SheetOps.pair a b).repr i = i} = d - 1
  rw [Fintype.card_congr (Equiv.subtypeEquivRight (pair_repr_eq_self_iff hab)),
    Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]

theorem card_blocks_discrete : Fintype.card (SheetPartition.discrete d).Blocks = d := by
  change Fintype.card {i : Fin d // (SheetPartition.discrete d).repr i = i} = d
  exact (Fintype.card_congr (Equiv.subtypeUnivEquiv fun _ ↦ rfl)).trans (Fintype.card_fin d)

/-- **`pair a b` inside a block of `Q` containing `a` and `b`**: as many blocks as sheets, minus
one when the block is the block of `a`. -/
theorem blockCountWithin_pair {Q : SheetPartition d} (hab : a ≠ b) (hQ : Q.Rel a b) (s : Fin d) :
    (SheetOps.pair a b).blockCountWithin Q s + (if Q.Rel s a then 1 else 0) = Q.blockCard s := by
  classical
  unfold SheetPartition.blockCountWithin SheetPartition.blockCard
  by_cases hs : Q.Rel s a
  · rw [ite_eq_left hs]
    have hb : b ∈ Q.block s := (Q.mem_block_iff s b).mpr (hs.trans hQ)
    have ha : a ∈ Q.block s := (Q.mem_block_iff s a).mpr hs
    have hImage : (Q.block s).image (SheetOps.pair a b).repr = (Q.block s).erase b := by
      ext i
      simp only [Finset.mem_image, Finset.mem_erase, pair_repr]
      constructor
      · rintro ⟨j, hj, rfl⟩
        by_cases hjb : j = b
        · simp only [hjb, ite_true]; exact ⟨hab, ha⟩
        · simp only [hjb, ite_false]; exact ⟨hjb, hj⟩
      · rintro ⟨hib, hi⟩
        exact ⟨i, hi, by simp [hib]⟩
    rw [hImage, Finset.card_erase_of_mem hb, Nat.sub_add_cancel (Finset.card_pos.mpr ⟨b, hb⟩)]
  · rw [ite_eq_right hs, add_zero]
    have hImage : (Q.block s).image (SheetOps.pair a b).repr = Q.block s := by
      ext i
      simp only [Finset.mem_image, pair_repr]
      constructor
      · rintro ⟨j, hj, hji⟩
        by_cases hjb : j = b
        · subst hjb
          exact absurd ((Q.mem_block_iff s j).mp hj |>.trans hQ.symm) hs
        · simp only [hjb, ite_false] at hji; rwa [← hji]
      · intro hi
        refine ⟨i, hi, ?_⟩
        have hib : i ≠ b := by
          rintro rfl
          exact hs (((Q.mem_block_iff s i).mp hi).trans hQ.symm)
        simp [hib]
    rw [hImage]

theorem one_le_blockCountWithin (fine coarse : SheetPartition d) (s : Fin d) :
    1 ≤ fine.blockCountWithin coarse s := by
  unfold SheetPartition.blockCountWithin
  exact Finset.card_pos.mpr ⟨_, Finset.mem_image_of_mem _ (coarse.self_mem_block s)⟩

end Pair

/-! ## 2.  Branchings and the regrown datum -/

/-- **The branching data of a regrowth**: the marks (source vertices of `D`) and, for each, a
second sheet in its block. -/
structure Branching (D : GluingDatum T d) (k : ℕ) where
  /-- The source vertex of mark `j`. -/
  mark : Fin k → D.SourceVertex
  /-- A second sheet in the block of mark `j`. -/
  other : Fin k → Fin d
  rel : ∀ j, (D.vertexPartition (mark j).1.1).Rel (mark j).1.2 (other j)
  ne : ∀ j, (mark j).1.2 ≠ other j

namespace Branching

variable {D : GluingDatum T d} (β : Branching D k)

/-- The image of mark `j`. -/
def x (j : Fin k) : T.V := (β.mark j).1.1

/-- The representative sheet of mark `j`. -/
def a (j : Fin k) : Fin d := (β.mark j).1.2

/-- The partition `{a, b} ∪ singletons` of the branch at mark `j`. -/
def P (j : Fin k) : SheetPartition d := SheetOps.pair (β.a j) (β.other j)

theorem a_ne (j : Fin k) : β.a j ≠ β.other j := β.ne j

theorem rel_a (j : Fin k) : (D.vertexPartition (β.x j)).Rel (β.a j) (β.other j) := β.rel j

theorem a_repr (j : Fin k) : (D.vertexPartition (β.x j)).repr (β.a j) = β.a j := (β.mark j).2

theorem P_refines (j : Fin k) : (β.P j).Refines (D.vertexPartition (β.x j)) :=
  pair_refines (β.rel_a j)

theorem P_rel_iff (j : Fin k) (i i' : Fin d) :
    (β.P j).Rel i i' ↔ i = i' ∨ ((i = β.a j ∨ i = β.other j) ∧ (i' = β.a j ∨ i' = β.other j)) :=
  pair_rel_iff (β.a_ne j) i i'

theorem P_rel_a_iff (j : Fin k) (i : Fin d) :
    (β.P j).Rel i (β.a j) ↔ i = β.a j ∨ i = β.other j :=
  pair_rel_left_iff (β.a_ne j) i

theorem P_rel_other (j : Fin k) : (β.P j).Rel (β.a j) (β.other j) := pair_rel_self _ _

theorem mark_eq (j : Fin k) : β.mark j = D.sourceEndpoint (β.x j) (β.a j) :=
  (D.sourceEndpoint_self (β.mark j)).symm

end Branching

variable {D : GluingDatum T d} (β : Branching D k)

/-- The partition over an occurrence of the regrown target. -/
def occPartition : Occ T k → SheetPartition d
  | .inl (.inl j) => β.P j
  | .inl (.inr _) => SheetPartition.discrete d
  | .inr e => D.edgePartition e

/-- The partition at a vertex of the regrown target. -/
def vtxPartition : Vtx T k → SheetPartition d :=
  Sum.elim D.vertexPartition (Sum.elim β.P β.P)

theorem occPartition_refines (o : Occ T k) :
    (occPartition β o).Refines (vtxPartition β (occEnds β.x o).1) ∧
      (occPartition β o).Refines (vtxPartition β (occEnds β.x o).2) := by
  rcases o with (j | j) | e
  · exact ⟨β.P_refines j, SheetPartition.Refines.refl _⟩
  · exact ⟨SheetPartition.discrete_refines _, SheetPartition.discrete_refines _⟩
  · exact ⟨D.refines_left e, D.refines_right e⟩

/-- **The regrown datum**. -/
def regrowDatum : GluingDatum (regrowTarget T β.x) d where
  degree_pos := D.degree_pos
  vertexPartition := vtxPartition β
  edgePartition e := occPartition β ((occEquiv β.x).symm e)
  refines_left e := by
    obtain ⟨o, rfl⟩ := (occEquiv β.x).surjective e
    rw [Equiv.symm_apply_apply, occEquiv_ends]
    exact (occPartition_refines β o).1
  refines_right e := by
    obtain ⟨o, rfl⟩ := (occEquiv β.x).surjective e
    rw [Equiv.symm_apply_apply, occEquiv_ends]
    exact (occPartition_refines β o).2

@[simp] theorem vp_oldV (v : T.V) :
    (regrowDatum β).vertexPartition (oldV β.x v) = D.vertexPartition v := rfl
@[simp] theorem vp_midV (j : Fin k) : (regrowDatum β).vertexPartition (midV β.x j) = β.P j := rfl
@[simp] theorem vp_tipV (j : Fin k) : (regrowDatum β).vertexPartition (tipV β.x j) = β.P j := rfl

@[simp] theorem ep_oldE (e : T.edges) :
    (regrowDatum β).edgePartition (oldE β.x e) = D.edgePartition e := by
  change occPartition β ((occEquiv β.x).symm (occEquiv β.x _)) = _
  rw [Equiv.symm_apply_apply]; rfl

@[simp] theorem ep_bridgeE (j : Fin k) : (regrowDatum β).edgePartition (bridgeE β.x j) = β.P j := by
  change occPartition β ((occEquiv β.x).symm (occEquiv β.x _)) = _
  rw [Equiv.symm_apply_apply]; rfl

@[simp] theorem ep_leafE (j : Fin k) :
    (regrowDatum β).edgePartition (leafE β.x j) = SheetPartition.discrete d := by
  change occPartition β ((occEquiv β.x).symm (occEquiv β.x _)) = _
  rw [Equiv.symm_apply_apply]; rfl

/-! ## 3.  The source -/

/-- An old source vertex. -/
def oldSV (X : D.SourceVertex) : (regrowDatum β).SourceVertex := ⟨(oldV β.x X.1.1, X.1.2), X.2⟩

/-- A source vertex over the middle vertex `u'_j`. -/
def midSV (j : Fin k) (i : Fin d) : (regrowDatum β).SourceVertex :=
  (regrowDatum β).sourceEndpoint (midV β.x j) i

/-- A source vertex over the tip `v_{C,j}`. -/
def tipSV (j : Fin k) (i : Fin d) : (regrowDatum β).SourceVertex :=
  (regrowDatum β).sourceEndpoint (tipV β.x j) i

/-- An old source edge. -/
def oldSE (E : D.SourceEdge) : (regrowDatum β).SourceEdge :=
  ⟨(oldE β.x E.1.1, E.1.2), by rw [ep_oldE]; exact E.2⟩

/-- A source edge over the bridge edge `t_b j`. -/
def bridgeSE (j : Fin k) (i : Fin d) : (regrowDatum β).SourceEdge :=
  (regrowDatum β).sourceEdge (bridgeE β.x j) i

/-- A source edge over the leaf edge `t_l j`. -/
def leafSE (j : Fin k) (i : Fin d) : (regrowDatum β).SourceEdge :=
  (regrowDatum β).sourceEdge (leafE β.x j) i

/-- The vertex `w j` of the lollipop at mark `j`. -/
def wSV (j : Fin k) : (regrowDatum β).SourceVertex := midSV β j (β.a j)

/-- The vertex `C j` (the tip of the loop) of the lollipop at mark `j`. -/
def cSV (j : Fin k) : (regrowDatum β).SourceVertex := tipSV β j (β.a j)

/-- The bridge `e_b j`. -/
def ebSE (j : Fin k) : (regrowDatum β).SourceEdge := bridgeSE β j (β.a j)

/-- The first loop edge `e₁ j`. -/
def e₁SE (j : Fin k) : (regrowDatum β).SourceEdge := leafSE β j (β.a j)

/-- The second loop edge `e₂ j`. -/
def e₂SE (j : Fin k) : (regrowDatum β).SourceEdge := leafSE β j (β.other j)

@[simp] theorem oldSV_target (X : D.SourceVertex) : (oldSV β X).1.1 = oldV β.x X.1.1 := rfl
@[simp] theorem midSV_target (j : Fin k) (i : Fin d) : (midSV β j i).1.1 = midV β.x j := rfl
@[simp] theorem tipSV_target (j : Fin k) (i : Fin d) : (tipSV β j i).1.1 = tipV β.x j := rfl
@[simp] theorem oldSE_target (E : D.SourceEdge) : (oldSE β E).1.1 = oldE β.x E.1.1 := rfl
@[simp] theorem bridgeSE_target (j : Fin k) (i : Fin d) :
    (bridgeSE β j i).1.1 = bridgeE β.x j := rfl
@[simp] theorem leafSE_target (j : Fin k) (i : Fin d) : (leafSE β j i).1.1 = leafE β.x j := rfl

theorem oldSV_injective : Function.Injective (oldSV β) := by
  intro X Y h
  have h1 := congrArg (fun Z : (regrowDatum β).SourceVertex ↦ Z.1.1) h
  have h2 := congrArg (fun Z : (regrowDatum β).SourceVertex ↦ Z.1.2) h
  simp only [oldSV_target, oldV_inj] at h1
  exact Subtype.ext (Prod.ext h1 h2)

@[simp] theorem oldSV_inj {X Y : D.SourceVertex} : oldSV β X = oldSV β Y ↔ X = Y :=
  (oldSV_injective β).eq_iff

theorem oldSE_injective : Function.Injective (oldSE β) := by
  intro X Y h
  have h1 := congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.1) h
  have h2 := congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.2) h
  simp only [oldSE_target, oldE_inj] at h1
  exact Subtype.ext (Prod.ext h1 h2)

@[simp] theorem oldSE_inj {X Y : D.SourceEdge} : oldSE β X = oldSE β Y ↔ X = Y :=
  (oldSE_injective β).eq_iff

theorem midSV_eq_iff (j j' : Fin k) (i i' : Fin d) :
    midSV β j i = midSV β j' i' ↔ j = j' ∧ (β.P j).Rel i i' := by
  constructor
  · intro h
    have hj : j = j' :=
      midV_injective β.x (congrArg (fun Z : (regrowDatum β).SourceVertex ↦ Z.1.1) h)
    subst hj
    refine ⟨rfl, ?_⟩
    have := ((regrowDatum β).sourceEndpoint_eq_iff (midV β.x j) i (midSV β j i')).mp h
    exact this.2.trans (((regrowDatum β).vertexPartition (midV β.x j)).rel_repr_left i')
  · rintro ⟨rfl, h⟩
    unfold midSV
    apply ((regrowDatum β).sourceEndpoint_eq_iff _ _ _).mpr
    refine ⟨rfl, ?_⟩
    exact h.trans (((regrowDatum β).vertexPartition (midV β.x j)).rel_repr_right i')

theorem tipSV_eq_iff (j j' : Fin k) (i i' : Fin d) :
    tipSV β j i = tipSV β j' i' ↔ j = j' ∧ (β.P j).Rel i i' := by
  constructor
  · intro h
    have hj : j = j' :=
      tipV_injective β.x (congrArg (fun Z : (regrowDatum β).SourceVertex ↦ Z.1.1) h)
    subst hj
    refine ⟨rfl, ?_⟩
    have := ((regrowDatum β).sourceEndpoint_eq_iff (tipV β.x j) i (tipSV β j i')).mp h
    exact this.2.trans (((regrowDatum β).vertexPartition (tipV β.x j)).rel_repr_left i')
  · rintro ⟨rfl, h⟩
    unfold tipSV
    apply ((regrowDatum β).sourceEndpoint_eq_iff _ _ _).mpr
    refine ⟨rfl, ?_⟩
    exact h.trans (((regrowDatum β).vertexPartition (tipV β.x j)).rel_repr_right i')

theorem bridgeSE_eq_iff (j j' : Fin k) (i i' : Fin d) :
    bridgeSE β j i = bridgeSE β j' i' ↔ j = j' ∧ (β.P j).Rel i i' := by
  constructor
  · intro h
    have hj : j = j' :=
      bridgeE_injective β.x (congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.1) h)
    subst hj
    refine ⟨rfl, ?_⟩
    have h2 := congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.2) h
    simp only [bridgeSE, GluingDatum.sourceEdge_sheet, ep_bridgeE] at h2
    exact h2
  · rintro ⟨rfl, h⟩
    apply Subtype.ext
    simp only [bridgeSE, GluingDatum.sourceEdge, ep_bridgeE]
    rw [show (β.P j).repr i = (β.P j).repr i' from h]

theorem leafSE_eq_iff (j j' : Fin k) (i i' : Fin d) :
    leafSE β j i = leafSE β j' i' ↔ j = j' ∧ i = i' := by
  constructor
  · intro h
    have hj : j = j' :=
      leafE_injective β.x (congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.1) h)
    subst hj
    refine ⟨rfl, ?_⟩
    have h2 := congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.2) h
    simp only [leafSE, GluingDatum.sourceEdge_sheet, ep_leafE] at h2
    exact h2
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem oldSV_ne_midSV (X : D.SourceVertex) (j : Fin k) (i : Fin d) :
    oldSV β X ≠ midSV β j i := fun h ↦
  oldV_ne_midV β.x j _ (congrArg (fun Z : (regrowDatum β).SourceVertex ↦ Z.1.1) h)
@[simp] theorem oldSV_ne_tipSV (X : D.SourceVertex) (j : Fin k) (i : Fin d) :
    oldSV β X ≠ tipSV β j i := fun h ↦
  oldV_ne_tipV β.x j _ (congrArg (fun Z : (regrowDatum β).SourceVertex ↦ Z.1.1) h)
@[simp] theorem midSV_ne_tipSV (j j' : Fin k) (i i' : Fin d) :
    midSV β j i ≠ tipSV β j' i' := fun h ↦
  midV_ne_tipV β.x j j' (congrArg (fun Z : (regrowDatum β).SourceVertex ↦ Z.1.1) h)
@[simp] theorem midSV_ne_oldSV (X : D.SourceVertex) (j : Fin k) (i : Fin d) :
    midSV β j i ≠ oldSV β X := fun h ↦ oldSV_ne_midSV β X j i h.symm
@[simp] theorem tipSV_ne_oldSV (X : D.SourceVertex) (j : Fin k) (i : Fin d) :
    tipSV β j i ≠ oldSV β X := fun h ↦ oldSV_ne_tipSV β X j i h.symm
@[simp] theorem tipSV_ne_midSV (j j' : Fin k) (i i' : Fin d) :
    tipSV β j i ≠ midSV β j' i' := fun h ↦ midSV_ne_tipSV β j' j i' i h.symm

@[simp] theorem oldSE_ne_bridgeSE (E : D.SourceEdge) (j : Fin k) (i : Fin d) :
    oldSE β E ≠ bridgeSE β j i := fun h ↦
  oldE_ne_bridgeE β.x _ j (congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.1) h)
@[simp] theorem oldSE_ne_leafSE (E : D.SourceEdge) (j : Fin k) (i : Fin d) :
    oldSE β E ≠ leafSE β j i := fun h ↦
  oldE_ne_leafE β.x _ j (congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.1) h)
@[simp] theorem bridgeSE_ne_leafSE (j j' : Fin k) (i i' : Fin d) :
    bridgeSE β j i ≠ leafSE β j' i' := fun h ↦
  bridgeE_ne_leafE β.x j j' (congrArg (fun Z : (regrowDatum β).SourceEdge ↦ Z.1.1) h)
@[simp] theorem bridgeSE_ne_oldSE (E : D.SourceEdge) (j : Fin k) (i : Fin d) :
    bridgeSE β j i ≠ oldSE β E := fun h ↦ oldSE_ne_bridgeSE β E j i h.symm
@[simp] theorem leafSE_ne_oldSE (E : D.SourceEdge) (j : Fin k) (i : Fin d) :
    leafSE β j i ≠ oldSE β E := fun h ↦ oldSE_ne_leafSE β E j i h.symm
@[simp] theorem leafSE_ne_bridgeSE (j j' : Fin k) (i i' : Fin d) :
    leafSE β j i ≠ bridgeSE β j' i' := fun h ↦ bridgeSE_ne_leafSE β j' j i' i h.symm

/-- **Every source vertex is old, over a middle vertex or over a tip.** -/
theorem sourceVertex_cases (X : (regrowDatum β).SourceVertex) :
    (∃ Y, X = oldSV β Y) ∨ (∃ j i, X = midSV β j i) ∨ (∃ j i, X = tipSV β j i) := by
  obtain ⟨⟨v, i⟩, hX⟩ := X
  rcases v with w | j | j
  · exact Or.inl ⟨⟨(w, i), hX⟩, rfl⟩
  · refine Or.inr (Or.inl ⟨j, i, ?_⟩)
    exact ((regrowDatum β).sourceEndpoint_self ⟨(Sum.inr (Sum.inl j), i), hX⟩).symm
  · refine Or.inr (Or.inr ⟨j, i, ?_⟩)
    exact ((regrowDatum β).sourceEndpoint_self ⟨(Sum.inr (Sum.inr j), i), hX⟩).symm

/-- **Every source edge is old, over a bridge edge or over a leaf edge.** -/
theorem sourceEdge_cases (E : (regrowDatum β).SourceEdge) :
    (∃ F, E = oldSE β F) ∨ (∃ j i, E = bridgeSE β j i) ∨ (∃ j i, E = leafSE β j i) := by
  rcases edge_cases β.x E.1.1 with ⟨f, hf⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · refine Or.inl ⟨⟨(f, E.1.2), ?_⟩, ?_⟩
    · have h := E.2
      rw [hf, ep_oldE] at h
      exact h
    · apply Subtype.ext
      exact Prod.ext hf rfl
  · refine Or.inr (Or.inl ⟨j, E.1.2, ?_⟩)
    have h := GluingDatum.sourceEdge_self (regrowDatum β) E
    rw [hj] at h
    exact h.symm
  · refine Or.inr (Or.inr ⟨j, E.1.2, ?_⟩)
    have h := GluingDatum.sourceEdge_self (regrowDatum β) E
    rw [hj] at h
    exact h.symm

/-! ### Endpoints -/

theorem sourceEndpoint_oldV (v : T.V) (i : Fin d) :
    (regrowDatum β).sourceEndpoint (oldV β.x v) i = oldSV β (D.sourceEndpoint v i) := rfl

theorem sourceEnds_oldSE (E : D.SourceEdge) :
    (regrowDatum β).sourceEnds (oldSE β E) =
      (oldSV β (D.sourceEnds E).1, oldSV β (D.sourceEnds E).2) := by
  unfold GluingDatum.sourceEnds
  simp only [oldSE, oldE_ends]
  rfl

theorem sourceEnds_bridgeSE (j : Fin k) (i : Fin d) :
    (regrowDatum β).sourceEnds (bridgeSE β j i) =
      (oldSV β (D.sourceEndpoint (β.x j) i), midSV β j i) := by
  unfold bridgeSE
  refine Prod.ext ?_ ?_
  · rw [GenusSixExistence.Tripod.Gluing.sourceEnds_sourceEdge_fst, bridgeE_ends]
    rfl
  · rw [GenusSixExistence.Tripod.Gluing.sourceEnds_sourceEdge_snd, bridgeE_ends]
    rfl

theorem sourceEnds_leafSE (j : Fin k) (i : Fin d) :
    (regrowDatum β).sourceEnds (leafSE β j i) = (midSV β j i, tipSV β j i) := by
  unfold leafSE
  refine Prod.ext ?_ ?_
  · rw [GenusSixExistence.Tripod.Gluing.sourceEnds_sourceEdge_fst, leafE_ends]
    rfl
  · rw [GenusSixExistence.Tripod.Gluing.sourceEnds_sourceEdge_snd, leafE_ends]
    rfl

/-! ### The incidence table -/

@[simp] theorem incident_oldSE_oldSV (E : D.SourceEdge) (X : D.SourceVertex) :
    Incident (regrowDatum β) (oldSE β E) (oldSV β X) ↔ Incident D E X := by
  unfold Incident
  rw [sourceEnds_oldSE]
  simp only [oldSV_inj]

@[simp] theorem incident_oldSE_midSV (E : D.SourceEdge) (j : Fin k) (i : Fin d) :
    ¬ Incident (regrowDatum β) (oldSE β E) (midSV β j i) := by
  unfold Incident
  rw [sourceEnds_oldSE]
  simp

@[simp] theorem incident_oldSE_tipSV (E : D.SourceEdge) (j : Fin k) (i : Fin d) :
    ¬ Incident (regrowDatum β) (oldSE β E) (tipSV β j i) := by
  unfold Incident
  rw [sourceEnds_oldSE]
  simp

@[simp] theorem incident_bridgeSE_oldSV (j : Fin k) (i : Fin d) (X : D.SourceVertex) :
    Incident (regrowDatum β) (bridgeSE β j i) (oldSV β X) ↔ D.sourceEndpoint (β.x j) i = X := by
  unfold Incident
  rw [sourceEnds_bridgeSE]
  simp

@[simp] theorem incident_bridgeSE_midSV (j j' : Fin k) (i i' : Fin d) :
    Incident (regrowDatum β) (bridgeSE β j i) (midSV β j' i') ↔ j = j' ∧ (β.P j).Rel i i' := by
  unfold Incident
  rw [sourceEnds_bridgeSE]
  simp [midSV_eq_iff]

@[simp] theorem incident_bridgeSE_tipSV (j j' : Fin k) (i i' : Fin d) :
    ¬ Incident (regrowDatum β) (bridgeSE β j i) (tipSV β j' i') := by
  unfold Incident
  rw [sourceEnds_bridgeSE]
  simp

@[simp] theorem incident_leafSE_oldSV (j : Fin k) (i : Fin d) (X : D.SourceVertex) :
    ¬ Incident (regrowDatum β) (leafSE β j i) (oldSV β X) := by
  unfold Incident
  rw [sourceEnds_leafSE]
  simp

@[simp] theorem incident_leafSE_midSV (j j' : Fin k) (i i' : Fin d) :
    Incident (regrowDatum β) (leafSE β j i) (midSV β j' i') ↔ j = j' ∧ (β.P j).Rel i i' := by
  unfold Incident
  rw [sourceEnds_leafSE]
  simp [midSV_eq_iff]

@[simp] theorem incident_leafSE_tipSV (j j' : Fin k) (i i' : Fin d) :
    Incident (regrowDatum β) (leafSE β j i) (tipSV β j' i') ↔ j = j' ∧ (β.P j).Rel i i' := by
  unfold Incident
  rw [sourceEnds_leafSE]
  simp [tipSV_eq_iff]

/-- The old endpoint of a bridge in the block of the mark is the mark. -/
theorem sourceEndpoint_x_of_rel (j : Fin k) {i : Fin d} (hi : (β.P j).Rel i (β.a j)) :
    D.sourceEndpoint (β.x j) i = β.mark j := by
  rw [β.mark_eq]
  apply (D.sourceEndpoint_eq_iff _ _ _).mpr
  refine ⟨rfl, ?_⟩
  have h := (β.P_refines j).rel hi
  exact h.trans ((D.vertexPartition (β.x j)).rel_repr_right (β.a j))

/-! ## 4.  Riemann--Hurwitz -/

/-- **Riemann--Hurwitz for the regrowth**: unchanged away from the marks,
`r⁺ = r - 1` at a mark (so the marks must be ramified), and the new vertices are fine. -/
theorem riemannHurwitz_regrowDatum (hRH : D.RiemannHurwitz) (hInj : Function.Injective β.mark)
    (hRam : ∀ j, 1 ≤ D.localRamification (β.x j) ⟨β.a j, β.a_repr j⟩) :
    (regrowDatum β).RiemannHurwitz := by
  classical
  intro v s
  rcases vertex_cases β.x v with ⟨w, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · -- an old vertex
    rw [sum_incidentEdges_oldV, card_incidentEdges_oldV]
    simp only [ep_oldE, ep_bridgeE, vp_oldV]
    have hOld := hRH w s
    set Q := D.vertexPartition w with hQ
    set J := Finset.univ.filter fun j ↦ β.x j = w
    have hPair : ∀ j ∈ J, ((β.P j).blockCountWithin Q s : ℤ) =
        Q.blockCard s - (if Q.Rel s (β.a j) then 1 else 0) := by
      intro j hj
      have hx : β.x j = w := (Finset.mem_filter.mp hj).2
      have hrel : Q.Rel (β.a j) (β.other j) := by
        have h := β.rel_a j
        rw [hx] at h
        exact h
      have h : (β.P j).blockCountWithin Q s + (if Q.Rel s (β.a j) then 1 else 0) =
          Q.blockCard s := blockCountWithin_pair (Q := Q) (β.a_ne j) hrel s
      by_cases hs : Q.Rel s (β.a j)
      · simp only [hs, ite_true] at h ⊢
        omega
      · simp only [hs, ite_false] at h ⊢
        omega
    rw [Finset.sum_congr rfl hPair]
    -- at most one mark in the block of `s`
    have hAtMost : (∑ j ∈ J, (if Q.Rel s (β.a j) then (1 : ℤ) else 0)) ≤
        (∑ edge ∈ GluingDatum.incidentEdges w,
          ((D.edgePartition edge).blockCountWithin Q s : ℤ)) - 2 -
          (Q.blockCard s : ℤ) * (((GluingDatum.incidentEdges w).card : ℤ) - 2) := by
      by_cases hEx : ∃ j ∈ J, Q.Rel s (β.a j)
      · obtain ⟨j, hj, hs⟩ := hEx
        have hx : β.x j = w := (Finset.mem_filter.mp hj).2
        have hOne : (∑ i ∈ J, (if Q.Rel s (β.a i) then (1 : ℤ) else 0)) = 1 := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_one]
          have hfilter : J.filter (fun i ↦ Q.Rel s (β.a i)) = {j} := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_singleton, J, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hxi, hsi⟩
              apply hInj
              rw [β.mark_eq i, β.mark_eq j]
              apply (D.sourceEndpoint_eq_iff _ _ _).mpr
              refine ⟨by rw [hxi, hx]; rfl, ?_⟩
              have hrel : Q.Rel (β.a i) (β.a j) := hsi.symm.trans hs
              show (D.vertexPartition (β.x i)).Rel (β.a i)
                ((D.vertexPartition (β.x j)).repr (β.a j))
              rw [hxi, hx]
              exact hrel.trans (Q.rel_repr_right _)
            · rintro rfl; exact ⟨hx, hs⟩
          rw [hfilter, Finset.card_singleton, Nat.cast_one]
        rw [hOne]
        have h := hRam j
        unfold GluingDatum.localRamification at h
        dsimp only at h
        rw [hx, ← hQ] at h
        have hBC : ∀ fine : SheetPartition d,
            fine.blockCountWithin Q (β.a j) = fine.blockCountWithin Q s := fun fine ↦
          ContractionRamification.blockCountWithin_congr fine Q hs.symm
        have hCard : Q.blockCard (β.a j) = Q.blockCard s :=
          ContractionRamification.blockCard_congr Q hs.symm
        simp only [hBC, hCard] at h
        linarith
      · push Not at hEx
        rw [Finset.sum_eq_zero fun j hj ↦ ite_eq_right_iff.mpr (fun h ↦ absurd h (hEx j hj))]
        linarith
    have hJ : (∑ j ∈ J, ((Q.blockCard s : ℤ) - (if Q.Rel s (β.a j) then 1 else 0))) =
        (J.card : ℤ) * Q.blockCard s - ∑ j ∈ J, (if Q.Rel s (β.a j) then (1 : ℤ) else 0) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [hJ]
    push_cast
    nlinarith
  · -- a middle vertex
    rw [card_incidentEdges_midV, incidentEdges_midV, Finset.sum_pair (bridgeE_ne_leafE β.x j j)]
    have h1 := one_le_blockCountWithin ((regrowDatum β).edgePartition (bridgeE β.x j))
      ((regrowDatum β).vertexPartition (midV β.x j)) s
    have h2 := one_le_blockCountWithin ((regrowDatum β).edgePartition (leafE β.x j))
      ((regrowDatum β).vertexPartition (midV β.x j)) s
    push_cast
    linarith
  · -- a tip
    rw [card_incidentEdges_tipV, incidentEdges_tipV, Finset.sum_singleton, ep_leafE]
    rw [ContractionRamification.blockCountWithin_of_discrete (fun _ ↦ rfl)]
    have := ((regrowDatum β).vertexPartition (tipV β.x j)).blockCard_pos s
    push_cast
    linarith

/-! ## 5.  Connectedness -/

open GenusSixExistence.Tripod.Gluing in
/-- **The regrown source is connected** when the old one is: every new source vertex hangs off
an old one by a path of at most two source edges. -/
theorem connected_regrowDatum (hD : D.Connected) : (regrowDatum β).Connected := by
  have hOld : ∀ X Y : D.SourceVertex,
      (srcGraph (regrowDatum β)).Reachable (oldSV β X) (oldSV β Y) := by
    refine reachable_of_sourceEdges D _ (oldSV β) (fun e i ↦ ?_) hD
    have h := adj_sourceEndpoint (regrowDatum β) (oldE β.x e) i
    rw [oldE_ends] at h
    exact h.reachable
  let X₀ : D.SourceVertex := D.sourceEndpoint (Classical.choice T.instNonempty) ⟨0, D.degree_pos⟩
  have hMid : ∀ j i, (srcGraph (regrowDatum β)).Reachable (oldSV β X₀) (midSV β j i) := by
    intro j i
    have h := adj_sourceEndpoint (regrowDatum β) (bridgeE β.x j) i
    rw [bridgeE_ends] at h
    exact (hOld X₀ (D.sourceEndpoint (β.x j) i)).trans h.reachable
  refine connected_of_reachable (regrowDatum β) (oldSV β X₀) fun X ↦ ?_
  rcases sourceVertex_cases β X with ⟨Y, rfl⟩ | ⟨j, i, rfl⟩ | ⟨j, i, rfl⟩
  · exact hOld X₀ Y
  · exact hMid j i
  · have h := adj_sourceEndpoint (regrowDatum β) (leafE β.x j) i
    rw [leafE_ends] at h
    exact (hMid j i).trans h.reachable

/-! ## 6.  The genus of the regrown source -/

/-- The source vertices of a datum are the blocks over the target vertices. -/
theorem card_sourceVertex {S : CFGraph} (E : GluingDatum S d) :
    Fintype.card E.SourceVertex = ∑ v, Fintype.card (E.vertexPartition v).Blocks := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun v i ↦ (E.vertexPartition v).repr i = i)

/-- The source edges of a datum are the blocks over the target edges. -/
theorem card_sourceEdge {S : CFGraph} (E : GluingDatum S d) :
    Fintype.card E.SourceEdge = ∑ e, Fintype.card (E.edgePartition e).Blocks := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    fun e i ↦ (E.edgePartition e).repr i = i)

theorem card_sourceVertex_regrowDatum :
    (Fintype.card (regrowDatum β).SourceVertex : ℤ) =
      Fintype.card D.SourceVertex + 2 * k * (d - 1) := by
  rw [card_sourceVertex, card_sourceVertex]
  change ((∑ v : T.V ⊕ (Fin k ⊕ Fin k),
    Fintype.card ((regrowDatum β).vertexPartition v).Blocks : ℕ) : ℤ) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hm : ∀ j : Fin k,
      Fintype.card ((regrowDatum β).vertexPartition (Sum.inr (Sum.inl j))).Blocks = d - 1 :=
    fun j ↦ card_blocks_pair (β.a_ne j)
  have ht : ∀ j : Fin k,
      Fintype.card ((regrowDatum β).vertexPartition (Sum.inr (Sum.inr j))).Blocks = d - 1 :=
    fun j ↦ card_blocks_pair (β.a_ne j)
  have h0 : ∀ v : T.V, Fintype.card ((regrowDatum β).vertexPartition (Sum.inl v)).Blocks =
      Fintype.card (D.vertexPartition v).Blocks := fun _ ↦ rfl
  rw [Finset.sum_congr rfl fun j _ ↦ hm j, Finset.sum_congr rfl fun j _ ↦ ht j,
    Finset.sum_congr rfl fun v _ ↦ h0 v]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hd := D.degree_pos
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hd.ne')]
  ring

theorem card_sourceEdge_regrowDatum :
    (Fintype.card (regrowDatum β).SourceEdge : ℤ) =
      Fintype.card D.SourceEdge + k * (d - 1) + k * d := by
  rw [card_sourceEdge, card_sourceEdge, sum_edges]
  have hc : ∀ j, Fintype.card (SheetOps.pair (β.a j) (β.other j)).Blocks = d - 1 :=
    fun j ↦ card_blocks_pair (β.a_ne j)
  simp only [ep_oldE, ep_bridgeE, ep_leafE, Branching.P, hc, card_blocks_discrete,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hd := D.degree_pos
  push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hd.ne')]
  ring

theorem genus_sourceGraph (E : GluingDatum T d) :
    genus E.sourceGraph = Fintype.card E.SourceEdge - Fintype.card E.SourceVertex + 1 := by
  unfold genus GluingDatum.sourceGraph
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ]

/-- **The genus of the regrown source** is the old genus plus one per mark (the loop). -/
theorem genus_regrowDatum :
    genus (regrowDatum β).sourceGraph = genus D.sourceGraph + k := by
  have h1 : genus (regrowDatum β).sourceGraph =
      Fintype.card (regrowDatum β).SourceEdge - Fintype.card (regrowDatum β).SourceVertex + 1 := by
    unfold genus GluingDatum.sourceGraph
    simp only [Multiset.card_map, Finset.card_val, Finset.card_univ]
  rw [h1, genus_sourceGraph, card_sourceEdge_regrowDatum, card_sourceVertex_regrowDatum]
  ring

end

end DraismaVargas.Count.MarkedCount.Regrow
