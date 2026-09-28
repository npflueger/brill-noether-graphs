import DraismaVargasCount.ValencyThreeSplit
import DraismaVargasCount.ResolutionExpansionFree

set_option autoImplicit false

/-!
# Valency-three rigidity: stages 4 and 5 of valency-three uniqueness

`ValencyThreeSplit` reduces near-side uniqueness at a valency-three metric limit to stage 3
(`TypeMatch`) and stages 4--5 (`SplitRigidity`).  This file proves **stage 5 in general** and
reduces `SplitRigidity` **exactly** to stage 4.  Stage 4 itself is proved in general in
`ValencyThreeResolutionMatch` (`resolutionMatch`, hence `splitRigidity`).

## What is proved

* **Stage 5, pinning the identifications** (`frameIso_of_columns`).  Over a connected core
  with at least three vertices, at a regrowth whose request has a vanishing coordinate
  (`y e₀ = 0`, which holds at every facet point), a datum isomorphism onto any frame of the
  core carrying every retained slot-aligned column to the matching one *is* a frame
  isomorphism.  Rows: the datum isomorphism reindexes the length matrix
  (`exists_matrix_submatrix`); the request row of `e₀` is supported on the degenerate column
  (`row_supported`); a row permutation fixing all other columns of a nonsingular matrix with
  such a row is the identity (`perm_eq_of_agree_off`, §1).  Vertices: by incidence vectors
  (`eq_of_coreIncidence_eq`, which needs connectivity and `3 ≤ n`).  The in-cone
  `StarFrameIso.ofLimitSquare` needs a nondegenerate request, so does not apply at facets.
* **`SplitRigidity` ⟺ stage 4** at such a request: `splitRigidity_of_anchorExtension` and
  its converse `anchorExtension_of_splitRigidity` (`ValencyThreeGeneral.slotColumn_frameIso`).
* **Stage 4 from a decoupled transport**: `extendsMetric_of_transportFree` glues the generic
  normal form `M11WallExhaustion.datumIso` on both sides to `ResolutionExpansionFree.liftFree`;
  hence `splitRigidity_of_resolutionMatch`.
* The composite `facetParity_of_typeMatch_resolutionMatch` (with `ValencyThreeSplit`'s
  `facetParity_of_stages`).

## A failure mode, checked

`SplitRigidity` is implied by labelled-metric uniqueness of the odd class, which computer
experiments support, and `ValencyThreeResolutionMatch.splitRigidity` proves it in general.  The
one candidate failure mode examined -- the join/overlap structure of the incoming partitions
on a non-anchor merged block, and the gluing of dangling occurrences, are not preserved by the
per-edge sheet permutations a limit isomorphism allows -- is exactly what the pendant
automorphisms of `W3Nd2StarExhaustionProof` (§9--§12) absorb, which is why every residual is
existential in the limit isomorphism: the universal form (every `ψ` lifts) fails in principle
(`W3Nd2StarExhaustionProof.Coherent`).

## Scope

* **Stage 4** (`AnchorExtension`, or the stronger `ResolutionMatch`) is not proved here; it is
  `ValencyThreeResolutionMatch.resolutionMatch`, at every core, request and degree.  What it
  needs: the incoming resolution on every merged block of the two regrowths, classified and
  matched.  On the anchor block the split forces it (two-picture: left = the `e₂ ∪ e₅` sheets
  plus singletons, right = `{A}`; three-picture: left = the `t_u` partition on `A`, right =
  `{e_δ sheets, rest}`); on a non-anchor block left = new-edge = the `t_u` partition and
  right = the join components; and the per-block matches must be made coherent through
  pendant automorphisms.
* Stage 5 carries `y e₀ = 0` for some `e₀`, `core.Connected` and `3 ≤ n`; all hold at a
  facet point of a cubic core of genus at least three, and
  `facetParity_of_typeMatch_resolutionMatch` supplies them.
* Stage 3 (`TypeMatch`) and the non-valency-three limits (`hrest`) are not treated here.

New `Prop`s, each with an interface line in its docstring: `ColumnIso`, `ExtendsMetric`,
`AnchorExtension`, `IsPlacement`, `ResolutionMatch`.
-/

namespace DraismaVargas.Count.ValencyThreeRigidity

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases

/-! ## 1.  Linear algebra: a vanishing row pins the row labels -/

section LinearAlgebra

variable {p : ℕ}

/-- Two distinct rows agreeing off one column, together with a third row supported on that
column, make a matrix singular. -/
theorem det_eq_zero_of_agree_off (K : Matrix (Fin p) (Fin p) ℚ) (c₀ a b r₀ : Fin p)
    (hab : a ≠ b) (ha : a ≠ r₀) (hr₀ : ∀ j, j ≠ c₀ → K r₀ j = 0) (hK0 : K r₀ c₀ ≠ 0)
    (hagree : ∀ j, j ≠ c₀ → K a j = K b j) : K.det = 0 := by
  classical
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  set lam := (K a c₀ - K b c₀) / K r₀ c₀
  refine ⟨Pi.single a 1 - Pi.single b 1 - lam • Pi.single r₀ 1, ?_, ?_⟩
  · intro h
    have := congrFun h a
    simp [hab, ha] at this
  · funext j
    simp only [Matrix.sub_vecMul, Matrix.smul_vecMul, Matrix.single_one_vecMul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row_apply]
    by_cases hj : j = c₀
    · subst hj
      simp only [lam]
      field_simp
      ring
    · rw [hagree j hj, hr₀ j hj]; ring

/-- Two distinct rows supported on one column, one of them nonzero there, make a matrix
singular. -/
theorem det_eq_zero_of_two_supported (K : Matrix (Fin p) (Fin p) ℚ) (c₀ a b : Fin p)
    (hab : a ≠ b) (ha : ∀ j, j ≠ c₀ → K a j = 0) (hb : ∀ j, j ≠ c₀ → K b j = 0)
    (hK0 : K b c₀ ≠ 0) : K.det = 0 := by
  classical
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨K b c₀ • Pi.single a 1 - K a c₀ • Pi.single b 1, ?_, ?_⟩
  · intro h
    have := congrFun h a
    simp [hab, hK0] at this
  · funext j
    simp only [Matrix.sub_vecMul, Matrix.smul_vecMul, Matrix.single_one_vecMul, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row_apply]
    by_cases hj : j = c₀
    · subst hj; ring
    · rw [ha j hj, hb j hj]; ring

/-- **A vanishing row pins the row labels.**  If a nonsingular matrix has a row supported on
one column, every permutation of its rows preserving all other columns is the identity. -/
theorem perm_eq_of_agree_off (K : Matrix (Fin p) (Fin p) ℚ) (hdet : K.det ≠ 0) (c₀ r₀ : Fin p)
    (hr₀ : ∀ j, j ≠ c₀ → K r₀ j = 0) (π : Equiv.Perm (Fin p))
    (hπ : ∀ r j, j ≠ c₀ → K (π r) j = K r j) (r : Fin p) : π r = r := by
  classical
  have hK0 : K r₀ c₀ ≠ 0 := by
    intro h0
    apply hdet
    refine Matrix.det_eq_zero_of_row_eq_zero r₀ fun j ↦ ?_
    by_cases hj : j = c₀
    · rw [hj]; exact h0
    · exact hr₀ j hj
  by_contra hne
  by_cases hr : r = r₀
  · subst hr
    have hsupp : ∀ j, j ≠ c₀ → K (π r) j = 0 := fun j hj ↦ (hπ r j hj).trans (hr₀ j hj)
    exact hdet (det_eq_zero_of_two_supported K c₀ (π r) r hne hsupp hr₀ hK0)
  · by_cases hpr : π r = r₀
    · have hsupp : ∀ j, j ≠ c₀ → K r j = 0 := fun j hj ↦ by
        rw [← hπ r j hj, hpr]; exact hr₀ j hj
      exact hdet (det_eq_zero_of_two_supported K c₀ r r₀ hr hsupp hr₀ hK0)
    · exact hdet (det_eq_zero_of_agree_off K c₀ (π r) r r₀ hne hpr hr₀ hK0 (hπ r))

end LinearAlgebra

/-! ## 2.  The core separates its vertices -/

section Separation

open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ}

/-- **A connected core with at least three vertices separates its vertices by incidence.**
Two vertices with the same incidence vector share every edge at either of them, so no edge
leaves the pair. -/
theorem eq_of_coreIncidence_eq {core : Core n p} (hconn : core.Connected) (hn : 3 ≤ n)
    {v v' : Fin n} (h : ∀ s, coreIncidence core v s = coreIncidence core v' s) : v = v' := by
  classical
  by_contra hne
  have hout : ∃ w : Fin n, w ∉ ({v, v'} : Finset (Fin n)) := by
    by_contra hall
    push Not at hall
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {v, v'} := fun w _ ↦ hall w
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at this
    have h2 := Finset.card_le_two (a := v) (b := v')
    omega
  obtain ⟨w, hw⟩ := hout
  obtain ⟨e, he⟩ := hconn {v, v'} ⟨v, w, by simp, hw⟩
  -- an edge at `v` is at `v'`, and conversely
  have hshare : ∀ x ∈ ({v, v'} : Finset (Fin n)), ∀ e : Fin p,
      (core.tail e = x ∨ core.head e = x) →
        (core.tail e ∈ ({v, v'} : Finset (Fin n)) ∧ core.head e ∈ ({v, v'} : Finset (Fin n))) := by
    intro x hx e hxe
    have hpos : 0 < coreIncidence core x e := by
      unfold coreIncidence; rcases hxe with h | h <;> simp [h]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · have hpos' : 0 < coreIncidence core v' e := (h e) ▸ hpos
      unfold coreIncidence at hpos hpos'
      by_cases ht : core.tail e = x <;> by_cases hh : core.head e = x <;>
        by_cases ht' : core.tail e = v' <;> by_cases hh' : core.head e = v' <;>
        simp_all
    · have hpos' : 0 < coreIncidence core v e := (h e).symm ▸ hpos
      unfold coreIncidence at hpos hpos'
      by_cases ht : core.tail e = x <;> by_cases hh : core.head e = x <;>
        by_cases ht' : core.tail e = v <;> by_cases hh' : core.head e = v <;>
        simp_all
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (hshare _ h1 e (Or.inl rfl)).2
  · exact h2 (hshare _ h1 e (Or.inr rfl)).1

end Separation

/-! ## 3.  Stage 5 at a facet: a column-compatible datum isomorphism pins the identification -/

section Pinning

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open ValencyThreeGeneral (slotColumn)

variable {n p degree : ℕ} {core : Core n p}

/-- The column of the second frame that a datum isomorphism assigns to a column of the
first. -/
noncomputable def colMap (k l : Frame core degree) (Φ : GeometricDatumIso k.data l.data)
    (j : Fin p) : Fin p :=
  l.fullDim.labelling.targetEdge.symm (Φ.targetEdge (k.fullDim.labelling.targetEdge j))

/-- **A datum isomorphism reindexes the length matrix.** -/
theorem exists_matrix_submatrix (k l : Frame core degree) (Φ : GeometricDatumIso k.data l.data) :
    ∃ ρ : Fin p ≃ Fin p,
      (∀ r c, l.matrix r (colMap k l Φ c) = k.matrix (ρ r) c) ∧
      ∀ r, Φ.stablePathEquiv k.fullDim.valid.1 (k.fullDim.labelling.row.symm (ρ r)) =
        l.fullDim.labelling.row.symm r := by
  classical
  set transported := GeometricMultiplicity.transportLabelling Φ k.fullDim.valid.1
    k.fullDim.labelling with htrans
  set ρ : Fin p ≃ Fin p := l.fullDim.labelling.row.symm.trans transported.row with hρ
  set γ : Fin p ≃ Fin p :=
    l.fullDim.labelling.targetEdge.trans transported.targetEdge.symm with hγ
  have hsub : l.matrix = k.matrix.submatrix ρ γ := by
    show GluingDatum.LengthMatrixPresentation.matrix l.fullDim.labelling.presentation =
      (GluingDatum.LengthMatrixPresentation.matrix k.fullDim.labelling.presentation).submatrix
        ρ γ
    rw [matrix_labelling_submatrix l.fullDim.labelling transported, hρ, hγ,
      GeometricMultiplicity.matrix_transportLabelling Φ k.fullDim.valid.1 k.fullDim.labelling]
  have hγc : ∀ c, γ (colMap k l Φ c) = c := by
    intro c
    rw [hγ, htrans]
    simp [GeometricMultiplicity.transportLabelling, colMap]
  refine ⟨ρ, fun r c ↦ ?_, fun r ↦ ?_⟩
  · rw [hsub, Matrix.submatrix_apply, hγc]
  · have : k.fullDim.labelling.row.symm (ρ r) =
        (Φ.stablePathEquiv k.fullDim.valid.1).symm (l.fullDim.labelling.row.symm r) := by
      rw [hρ, htrans]
      simp [GeometricMultiplicity.transportLabelling]
    rw [this, Equiv.apply_symm_apply]

/-- The vanishing request row of a regrowth is supported on its degenerate column. -/
theorem row_supported {y : Fin p → ℚ} (w : Regrowth core y degree) {e₀ : Fin p}
    (hy : y e₀ = 0) (j : Fin p) (hj : j ≠ w.column) :
    w.frame.matrix (w.frame.slot.symm e₀) j = 0 := by
  refine NonTrivalentLinkMatrix.row_supported_of_zero_image
    (fun row column ↦ NonTrivalentValencyTwoExit.matrix_labelling_nonneg
      w.frame.fullDim.labelling row column)
    w.degenerate.1 w.degenerate.2 ?_ j hj
  have := congrFun (w.frame.mulVec_coordsAt y) (w.frame.slot.symm e₀)
  rw [Equiv.apply_symm_apply, hy] at this
  exact this

/-- **Stage 5, rows.**  At a regrowth with a vanishing request coordinate, a datum
isomorphism onto another frame that carries every retained slot-aligned column to the
matching one carries every stable path to the stable path of the same core slot. -/
theorem overCore_row_of_columns {y : Fin p → ℚ} (w : Regrowth core y degree) (l : Frame core degree)
    {e₀ : Fin p} (hy : y e₀ = 0) (Φ : GeometricDatumIso w.frame.data l.data)
    (hcol : ∀ j, j ≠ w.column → slotColumn l (colMap w.frame l Φ j) = slotColumn w.frame j)
    (P : W4StableSource.StablePath w.frame.data) :
    l.ident.row (Φ.stablePathEquiv w.frame.fullDim.valid.1 P) = w.frame.ident.row P := by
  classical
  obtain ⟨ρ, hM, hρ⟩ := exists_matrix_submatrix w.frame l Φ
  set K := w.frame.matrix with hK
  let π : Equiv.Perm (Fin p) := (w.frame.slot.trans l.slot.symm).trans ρ
  have hπ : ∀ r j, j ≠ w.column → K (π r) j = K r j := by
    intro r j hj
    have h := congrFun (hcol j hj) (w.frame.slot r)
    simp only [slotColumn] at h
    rw [hM, Equiv.symm_apply_apply] at h
    exact h
  have hid := ValencyThreeRigidity.perm_eq_of_agree_off K w.frame.det_ne_zero w.column
    (w.frame.slot.symm e₀) (row_supported w hy) π hπ
  -- read the path through its row
  set r' := l.fullDim.labelling.row (Φ.stablePathEquiv w.frame.fullDim.valid.1 P) with hr'
  have hP : w.frame.fullDim.labelling.row.symm (ρ r') = P := by
    apply (Φ.stablePathEquiv w.frame.fullDim.valid.1).injective
    rw [hρ r', hr', Equiv.symm_apply_apply]
  have hslot : ρ r' = w.frame.slot.symm (l.slot r') := by
    have := hid (w.frame.slot.symm (l.slot r'))
    simp only [π, Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply] at this
    exact this
  have h1 : l.slot r' = l.ident.row (Φ.stablePathEquiv w.frame.fullDim.valid.1 P) := by
    show l.ident.row (l.fullDim.labelling.row.symm r') = _
    rw [hr', Equiv.symm_apply_apply]
  rw [← h1]
  have h2 : w.frame.slot (ρ r') = l.slot r' := by rw [hslot, Equiv.apply_symm_apply]
  rw [← h2]
  show w.frame.ident.row (w.frame.fullDim.labelling.row.symm (ρ r')) = _
  rw [hP]

/-- **Stage 5.**  At a regrowth with a vanishing request coordinate over a connected core
with at least three vertices, a datum isomorphism onto another frame carrying every retained
slot-aligned column to the matching one is a frame isomorphism: the identification is pinned
(rows by `overCore_row_of_columns`, branch vertices by their incidence vectors,
`eq_of_coreIncidence_eq`). -/
noncomputable def frameIso_of_columns {y : Fin p → ℚ} (w : Regrowth core y degree)
    (l : Frame core degree) (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p} (hy : y e₀ = 0)
    (Φ : GeometricDatumIso w.frame.data l.data)
    (hcol : ∀ j, j ≠ w.column → slotColumn l (colMap w.frame l Φ j) = slotColumn w.frame j) :
    FrameIso w.frame l where
  datum := Φ
  overCore_row := overCore_row_of_columns w l hy Φ hcol
  overCore_vertex := by
    intro b
    apply eq_of_coreIncidence_eq hconn hn
    intro s
    rw [← l.ident.incidence, ← w.frame.ident.incidence]
    have hrow : l.ident.row.symm s =
        Φ.stablePathEquiv w.frame.fullDim.valid.1 (w.frame.ident.row.symm s) := by
      apply l.ident.row.injective
      rw [Equiv.apply_symm_apply, overCore_row_of_columns w l hy Φ hcol, Equiv.apply_symm_apply]
    rw [hrow]
    exact (Φ.incidenceCount_map w.frame.fullDim.valid.1 b.1 _).symm

end Pinning

/-! ## 4.  Stage 4 as a named obligation, and the reduction of `SplitRigidity` to it -/

section Stage4

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyThreeGeneral (slotColumn limitCol)
open ValencyThreeSplit (RegrowthAnchor anchorOf uOf IsMetricIso Reads AnchorLabelling
  SplitRigidity)
open GluingContraction

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- **A column-compatible datum isomorphism** between two regrowths: an isomorphism of the
incoming gluing data carrying every retained slot-aligned column to the matching one.  This is
exactly the input of stage 5 (`frameIso_of_columns`).

Interface: consumed by `frameIso_of_columns`; implied by `ExtendsMetric`. -/
def ColumnIso (w w' : Regrowth core y degree) : Prop :=
  ∃ Φ : GeometricDatumIso w.frame.data w'.frame.data,
    ∀ j, j ≠ w.column → slotColumn w'.frame (colMap w.frame w'.frame Φ j) = slotColumn w.frame j

/-- **A datum isomorphism extending a labelled-metric limit isomorphism**: on every retained
target occurrence it is the limit isomorphism, read through the two contractions.

Interface: implies `ColumnIso` (`columnIso_of_extendsMetric`); produced from a decoupled
transport by `extendsMetric_of_transportFree`. -/
def ExtendsMetric (w w' : Regrowth core y degree) : Prop :=
  ∃ (ψ : GeometricDatumIso w.limit w'.limit) (Φ : GeometricDatumIso w.frame.data w'.frame.data),
    IsMetricIso w w' ψ ∧
      ∀ e, Φ.targetEdge (unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
          (w.frame.numEdges_edgeOf w.column) e) =
        unfoldEdge rfl (fst_ne_snd (w'.frame.edgeOf w'.column))
          (w'.frame.numEdges_edgeOf w'.column) (ψ.targetEdge e)

/-- An extension of a labelled-metric limit isomorphism is column-compatible. -/
theorem columnIso_of_extendsMetric {w w' : Regrowth core y degree} (h : ExtendsMetric w w') :
    ColumnIso w w' := by
  classical
  obtain ⟨ψ, Φ, hψ, hext⟩ := h
  refine ⟨Φ, fun j hj ↦ ?_⟩
  have hne : w.frame.edgeOf j ≠ w.frame.edgeOf w.column :=
    fun h' ↦ hj (w.frame.fullDim.labelling.targetEdge.injective h')
  set e := foldEdge (contracted := w.frame.edgeOf w.column) rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    ⟨w.frame.edgeOf j, hne⟩ with he
  have hunfold : unfoldEdge rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) e = w.frame.edgeOf j := by
    rw [he, unfoldEdge_foldEdge]
  have hcolw : limitCol w e = j := by
    unfold limitCol
    rw [hunfold]
    simp [SegmentWalls.Frame.edgeOf]
  have hcolw' : colMap w.frame w'.frame Φ j = limitCol w' (ψ.targetEdge e) := by
    unfold colMap limitCol
    rw [← hext e, hunfold]
    rfl
  rw [hcolw', (hψ e).2, hcolw]

/-- **Stage 4, extending the isomorphism across the anchor**, as the obligation stage 5
consumes: two odd classes of one core at one labelled metric limit with a valency-three
anchor, reading the same split for transported labellings, have column-compatible incoming
data.

Interface: implied by `ExtendsMetric` (`columnIso_of_extendsMetric`), which is what a lift
of the limit isomorphism across the anchor (`ResolutionExpansionFree.liftFree`) produces;
existential in the isomorphism, because a given limit isomorphism need not lift
(`W3Nd2StarExhaustionProof.Coherent`); not proved here (see
`ValencyThreeResolutionMatch.anchorExtension`). -/
def AnchorExtension (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ →
    ∀ (L : AnchorLabelling w.limit (anchorOf w block))
      (L' : AnchorLabelling w'.limit (anchorOf w' block')),
      (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) →
      (FrameClass.mk w.frame).IsOdd → (FrameClass.mk w'.frame).IsOdd →
      ∀ s : ValencyThreeGeneral.Split7.Split, Reads L (uOf w) s → Reads L' (uOf w') s →
        ColumnIso w w'

/-- **`SplitRigidity` from stage 4**: stage 5 is proved (`frameIso_of_columns`), so at a
request with a vanishing coordinate over a connected core with at least three vertices,
`SplitRigidity` is exactly as hard as `AnchorExtension`. -/
theorem splitRigidity_of_anchorExtension (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hy : y e₀ = 0) (h4 : AnchorExtension core y degree) : SplitRigidity core y degree := by
  intro w w' block block' H H' ψ hψ L L' hL hx hx' s hs hs'
  obtain ⟨Φ, hcol⟩ := h4 w w' block block' H H' ψ hψ L L' hL hx hx' s hs hs'
  exact FrameClass.mk_eq_mk_iff.mpr ⟨frameIso_of_columns w w'.frame hconn hn hy Φ hcol⟩

/-- Conversely, `SplitRigidity` gives stage 4 (a frame isomorphism is column-compatible,
`ValencyThreeGeneral.slotColumn_frameIso`): the two are equivalent at a facet. -/
theorem anchorExtension_of_splitRigidity (h : SplitRigidity core y degree) :
    AnchorExtension core y degree := by
  intro w w' block block' H H' ψ hψ L L' hL hx hx' s hs hs'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (h w w' block block' H H' ψ hψ L L' hL hx hx' s hs hs')
  refine ⟨fi.datum, fun j _ ↦ ?_⟩
  have hc : colMap w.frame w'.frame fi.datum j = fi.column j := by
    simp [colMap, GeometricSegmentWalls.FrameIso.column]
  rw [hc]
  exact ValencyThreeGeneral.slotColumn_frameIso fi j

end Stage4

/-! ## 5.  Stage 4 reduced to a decoupled transport of the two incoming resolutions -/

section Transport

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open ValencyThreeSplit (IsMetricIso)
open GluingContraction GraphContraction TargetExpansion

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The contracted occurrence's first end, the merged vertex of the limit. -/
abbrev endA (w : Regrowth core y degree) : w.frame.target.V :=
  (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).1

abbrev endB (w : Regrowth core y degree) : w.frame.target.V :=
  (w.frame.edgeOf w.column : w.frame.target.V × w.frame.target.V).2

/-- **A placement of a regrowth**: a side for every limit occurrence, agreeing with the
incoming side assignment at the merged vertex up to exchanging the two ends.

Interface: the hypothesis of the normal form `M11WallExhaustion.datumIso`;
inhabited by the incoming side assignment itself (`isPlacement_right`). -/
def IsPlacement (w : Regrowth core y degree)
    (second : (w.frame.limitTarget w.column).edges → Bool) : Prop :=
  (∀ edge ∈ GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
      ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩,
      IncomingTargetExpansion.right rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) edge = second edge) ∨
  (∀ edge ∈ GluingDatum.incidentEdges (target := w.frame.limitTarget w.column)
      ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩,
      IncomingTargetExpansion.right rfl (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) edge = !(second edge))

/-- **The local resolution a regrowth presents** at a placement: its two endpoint partitions
and its contracted occurrence's partition (`M11WallExhaustion.incomingResolution`). -/
noncomputable abbrev resolutionOf (w : Regrowth core y degree)
    (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second) :
    ResolutionM11.LocalResolution degree :=
  M11WallExhaustion.incomingResolution w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) second h

/-- The normal form of a regrowth: its datum is the resolution expansion of its own limit. -/
noncomputable abbrev normalForm (w : Regrowth core y degree)
    (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second) :=
  M11WallExhaustion.datumIso w.frame.data rfl (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) second h w.frame.fullDim.targetConnected
    w.frame.fullDim.targetGenus

/-- **Stage 4 in the language of the star machinery.**  A labelled-metric limit
isomorphism together with a decoupled transport (`ResolutionExpansionFree.TransportFree`) of
the two regrowths' incoming resolutions lifts, through the two normal forms and
`liftFree`, to a datum isomorphism extending it. -/
theorem extendsMetric_of_transportFree (w w' : Regrowth core y degree)
    (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second)
    (second' : (w'.frame.limitTarget w'.column).edges → Bool) (h' : IsPlacement w' second')
    (ψ : GeometricDatumIso w.limit w'.limit) (hψ : IsMetricIso w w' ψ)
    (T : ResolutionExpansionFree.TransportFree ψ ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
      ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ second second'
      (resolutionOf w second h) (resolutionOf w' second' h')) :
    ExtendsMetric w w' := by
  classical
  let L := ResolutionExpansionFree.liftFree ψ ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
    ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ second second'
    (resolutionOf w second h) (resolutionOf w' second' h')
    (M11WallExhaustion.incomingOldCompatible w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) second h
      w.frame.fullDim.targetConnected w.frame.fullDim.targetGenus)
    (M11WallExhaustion.incomingOldCompatible w'.frame.data rfl
      (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column) second' h'
      w'.frame.fullDim.targetConnected w'.frame.fullDim.targetGenus) T
  refine ⟨ψ, (normalForm w second h).trans (L.trans (normalForm w' second' h').symm), hψ,
    fun e ↦ ?_⟩
  show (normalForm w' second' h').targetEdge.symm
      (L.targetEdge ((normalForm w second h).targetEdge _)) = _
  have h1 := M11WallExhaustion.datumIso_occurrence w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) second h
    w.frame.fullDim.targetConnected w.frame.fullDim.targetGenus (some e)
  rw [M11IncomingCoordinates.incomingColumnEquiv_some] at h1
  rw [h1]
  have h3 := ResolutionExpansionFree.liftFree_targetEdge_occurrence ψ
    ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
    ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ second second'
    (resolutionOf w second h) (resolutionOf w' second' h')
    (M11WallExhaustion.incomingOldCompatible w.frame.data rfl
      (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column) second h
      w.frame.fullDim.targetConnected w.frame.fullDim.targetGenus)
    (M11WallExhaustion.incomingOldCompatible w'.frame.data rfl
      (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column) second' h'
      w'.frame.fullDim.targetConnected w'.frame.fullDim.targetGenus) T (some e)
  refine (congrArg (normalForm w' second' h').targetEdge.symm h3).trans ?_
  have h2 := M11WallExhaustion.datumIso_occurrence w'.frame.data rfl
    (fst_ne_snd (w'.frame.edgeOf w'.column)) (w'.frame.numEdges_edgeOf w'.column) second' h'
    w'.frame.fullDim.targetConnected w'.frame.fullDim.targetGenus (some (ψ.targetEdge e))
  exact ((normalForm w' second' h').targetEdge.symm_apply_eq).mpr h2.symm

/-- The incoming side assignment is itself a placement. -/
theorem isPlacement_right (w : Regrowth core y degree) :
    IsPlacement w (IncomingTargetExpansion.right rfl (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column)) :=
  Or.inl fun _ _ ↦ rfl

open ValencyThreeSplit (RegrowthAnchor anchorOf uOf Reads AnchorLabelling SplitRigidity)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)

/-- **Stage 4, the residual, in the language of the star censuses.**  Two odd classes of one core at
one labelled metric limit with a valency-three anchor, reading the same split for
transported labellings, admit placements, a labelled-metric limit isomorphism and a
decoupled transport (`ResolutionExpansionFree.TransportFree`) of their incoming resolutions.

Interface: what the star censuses produce family by family
(`ResolutionExpansionFree.CoversFreeSome`'s `MemberTransport`), here between two members at
one facet limit; existential in the limit isomorphism because a given one need not be coherent
(`W3Nd2StarExhaustionProof.Coherent`); implies `AnchorExtension`
(`anchorExtension_of_resolutionMatch`); not proved here (see
`ValencyThreeResolutionMatch.resolutionMatch`). -/
def ResolutionMatch (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) : Prop :=
  ∀ (w w' : Regrowth core y degree) (block block')
    (_H : RegrowthAnchor w block) (_H' : RegrowthAnchor w' block')
    (ψ : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ →
    ∀ (L : AnchorLabelling w.limit (anchorOf w block))
      (L' : AnchorLabelling w'.limit (anchorOf w' block')),
      (∀ i, L'.e i = ψ.sourceEdgeEquiv (L.e i)) →
      (FrameClass.mk w.frame).IsOdd → (FrameClass.mk w'.frame).IsOdd →
      ∀ s : ValencyThreeGeneral.Split7.Split, Reads L (uOf w) s → Reads L' (uOf w') s →
        ∃ (second : (w.frame.limitTarget w.column).edges → Bool) (h : IsPlacement w second)
          (second' : (w'.frame.limitTarget w'.column).edges → Bool) (h' : IsPlacement w' second')
          (ψ' : GeometricDatumIso w.limit w'.limit), IsMetricIso w w' ψ' ∧
          Nonempty (ResolutionExpansionFree.TransportFree ψ'
            ⟨endA w, fst_ne_snd (w.frame.edgeOf w.column)⟩
            ⟨endA w', fst_ne_snd (w'.frame.edgeOf w'.column)⟩ second second'
            (resolutionOf w second h) (resolutionOf w' second' h'))

theorem anchorExtension_of_resolutionMatch (h : ResolutionMatch core y degree) :
    AnchorExtension core y degree := by
  intro w w' block block' H H' ψ hψ L L' hL hx hx' s hs hs'
  obtain ⟨second, hp, second', hp', ψ', hψ', ⟨T⟩⟩ :=
    h w w' block block' H H' ψ hψ L L' hL hx hx' s hs hs'
  exact columnIso_of_extendsMetric
    (extendsMetric_of_transportFree w w' second hp second' hp' ψ' hψ' T)

/-- **`SplitRigidity` from the transport residual**, at a facet over a connected core with at
least three vertices. -/
theorem splitRigidity_of_resolutionMatch (hconn : core.Connected) (hn : 3 ≤ n) {e₀ : Fin p}
    (hy : y e₀ = 0) (h : ResolutionMatch core y degree) : SplitRigidity core y degree :=
  splitRigidity_of_anchorExtension hconn hn hy (anchorExtension_of_resolutionMatch h)

end Transport

/-! ## 6.  The composite at a Whitehead step -/

section Composite

open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.FacetMachine
open DraismaVargas.Count.FacetAdapterPilot (farCore)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open ValencyThreeSplit (TypeMatch V3Limit)
open ValencyThreeGeneral (MetricFacetLimit MSpecializesLeft)

variable {n p degree : ℕ} {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **`FacetParity` at a Whitehead step from stage 3 and the stage-4 residual** on both
sides (stage 5 proved here, stages 1--2 in `ValencyThreeSplit`), with uniqueness supplied at the
non-valency-three limits. -/
theorem facetParity_of_typeMatch_resolutionMatch (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree) (hn : 3 ≤ n)
    (h3 : TypeMatch c.core y₀ degree) (h4 : ResolutionMatch c.core y₀ degree)
    (h3' : TypeMatch (farCore m').core y₀ degree)
    (h4' : ResolutionMatch (farCore m').core y₀ degree)
    (hrest : ∀ m : MetricFacetLimit c.core (farCore m').core y₀ degree, ¬ V3Limit m →
      ∀ x x' : FrameClass c.core degree,
        x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x')
    (hrest' : ∀ m : MetricFacetLimit (farCore m').core c.core y₀ degree, ¬ V3Limit m →
      ∀ x x' : FrameClass (farCore m').core degree,
        x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x') :
    FacetParity c.core (farCore m').core degree y₀ :=
  ValencyThreeSplit.facetParity_of_stages m' hd hG hDegree h3
    (splitRigidity_of_resolutionMatch c.connected hn hd.point.1 h4) h3'
    (splitRigidity_of_resolutionMatch (farCore m').connected hn hd.point.1 h4') hrest hrest'

end Composite

end DraismaVargas.Count.ValencyThreeRigidity
