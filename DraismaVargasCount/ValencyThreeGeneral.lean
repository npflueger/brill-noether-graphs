module

public import DraismaVargasCount.LinkReceiptExport
public import DraismaVargasCount.FrameColumnRigidity

@[expose] public section

/-!
# Valency-three facet limits: retained data, labelled metric limits, split determination

A. Vargas, *Catalan-many tropical morphisms to trees; Part II: A space and a count*,
arXiv:2609.09109, subsection "Valency-3 limits: Case {v3-nd4}" (`subsec-case-v3`): at a
valency-three limit `φ₀` there is exactly one full-dimensional morphism of each of Types I, II,
III.  This module builds the notions of "limit" in which such statements are used in the
type-change step of the count (step 3 of `DraismaVargasCount.Assembly`), and proves the
arithmetic core of the valency-three case.

## Which limit a uniqueness statement is about

`FacetMachine.FacetLimit` is the **unlabelled, metric-free** limit (a `GeometricDatumIso`
class).  Part II's uniqueness is per **labelled metric** limit `φ₀`; a coarse class is a union
of fine ones, and distinct fine limits over one facet point can be isomorphic as unlabelled data
whenever `H₀ = c / e₀` has a label-moving symmetry.  So "at most one odd `FrameClass` on each
side per `FacetMachine.FacetLimit`" -- the coarse hypotheses `huniqL`/`huniqR` of
`LinkReceiptExport.facetParity_of_uniqueness` restricted to valency-three anchors -- can fail at
valency three, and uniqueness has to be read per labelled metric limit.  Refining the coarse
limit by the retained data of §1 (the multiset of slot-aligned columns and coordinates off the
vanishing column) is not enough either: the retained data does not pin the class.  The labelled
metric limit of §3 (an isomorphism of limit data preserving every surviving length *and*
slot-aligned column) is the right notion.

At valency four even a labelled metric limit carries several members of each type: by Part II
there are `min(k₂ - 1, |A| - k₅) + 1` of them.  The type-change step therefore compares the two
sides of a move by a census inside each labelled metric limit, with equal counts
(`FacetCensus`); the uniqueness consumers below (§2, §5) are valid implications whose uniqueness
hypotheses need not hold at every step.

## Main results

* **§1 retained data.**  `slotColumn` (a length column with rows read as core slots),
  `slotColumn_frameIso` (a geometric frame isomorphism carries it along its column
  dictionary -- the matrix identity behind `MemberIso.coords_column`),
  `retained`, `retained_eq_of_perm`, `retained_eq_of_frameIso`.
* **§2 retained consumer.**  `RSpecializesLeft/Right`, their uniqueness, and
  `facetParity_of_retained`: `FacetParity` from retained uniqueness plus retained existence
  both ways.
* **§3 the labelled metric facet limit.**  `limitCol`, `limitCol_limitIso`, `limitLength`,
  `limitSlotColumn`, `SameMetricLimit` (an equivalence), `MetricFacetLimit` with
  `ofLeft/ofRight/toCoarse`, `MSpecializesLeft/Right` (single-valued on classes:
  `MSpecializesLeft.unique`), and **`facetParity_of_metric`**: `FacetParity` from
  labelled-metric uniqueness on each side and labelled-metric existence both ways.
  `metricUniqueL_of_coarse`/`metricUniqueR_of_coarse`: the coarse hypotheses imply the metric
  ones, so the metric consumer is strictly more usable.
* **§4 what a Part I link keeps with no receipt.**  `slotColumn_farFrame`,
  `retained_farRegrowth` (the far regrowth of *any* `TypeChangeLink` has the regrowth's
  retained data), hence `exists_odd_rSpecializesRight/Left` **unconditionally** (with the
  receipts of `LinkReceiptExport`) and `facetParity_of_retainedUniqueness` -- whose uniqueness
  hypotheses, however, can fail at valency three (see above).
* **§5 the metric form at a step.**  `MetricLinkReceipts` (the length- and label-preserving
  strengthening of `FacetAdapterPilot.FacetLinkReceipts`), `ColumnLinkReceipts` (its plumbing
  core: the limit isomorphism matches column labels) with `metricLinkReceipts_of_column`,
  `exists_odd_mSpecializesRight/Left`, and **`facetParity_of_metricUniqueness`**:
  `FacetParity` at a Whitehead step from labelled-metric uniqueness on each side and the two
  metric receipts.  `ColumnReceiptExport` proves both receipts at every facet datum.
* **§7 split determination, the arithmetic core** of Part II's valency-three case.
  `AnchorIndices`, `Split`, `VType`, `Split.type`, `AnchorIndices.Valid`; `existsUnique`: for
  each of the three types **exactly one** realisable split (`(3,5)` never, `(3,2)`/`(4,5)`
  complementary); `r0_at_Av`, `degV_ge`: the derived `|A_v|` and bridge index satisfy Case (r0)
  and bound the incident indices.  **`exists_anchorIndices`** (anchor localization, numeric
  form): the census `ThreeBranchAnchor` of any actual wall block yields an `AnchorIndices`
  (`|A|` = the block's local degree, `k₂ + k₅` = the doubled direction's index sum,
  `k₃ + k₄` = the simple directions'), so `existsUnique` applies to every valency-three
  wall datum.

## Remarks

* The census (`NonTrivalentValencyThreeAnchor`) and rigidity
  (`NonTrivalentValencyThreeRigidity`) of Part I's library are statements about the *limit* (the
  wall datum): `2+1+1`, `(⊞)`, ramification one at the anchor.  They do not see the incoming
  cover's split.  What they leave is (a) the local equations of the cover at `A_u`, `A'`, `A_v`
  (Cases (r0)/(r1) of `prop-local`, available for divalent source vertices as
  `IndexPattern.sourceEdgeIndex_add_sourceEdgeIndex`, for the others as the excess formula
  used in `threeBranchAnchor`) and (b) the reading of `(base tree, α, δ)` off the cover.
  *Given* (a) and (b), the determination is pure arithmetic, and that is §7: no `Split` is
  read off an incoming cover here; what §7 proves is that *once* a cover's split is read off,
  its type pins it.
* `MetricLinkReceipts` and `ColumnLinkReceipts` are the new `Prop`s; `SameMetricLimit`,
  `MSpecializes*`, `RSpecializes*` are definitional predicates of the same kind as
  `FacetMachine.SpecializesLeft`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.ValencyThreeGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore Step)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.WallStar (Regrowth)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open DraismaVargas.Count.FacetMachine

variable {n p degree : ℕ}

/-! ## 1.  The retained data of a regrowth -/

section Retained

variable {core : Core n p}

/-- **The slot-aligned column** `j` of a frame: its length-matrix column `j`, with rows
read as core slots through the frame's own slot dictionary.  This is the column of
`FrameColumnRigidity.AgreeOffColumnSlot`. -/
noncomputable def slotColumn (k : Frame core degree) (j : Fin p) : Fin p → ℚ :=
  fun s ↦ k.matrix (k.slot.symm s) j

/-- **A geometric frame isomorphism carries slot-aligned columns along its column
dictionary.**  The matrix identity behind `MemberIso.coords_column`. -/
theorem slotColumn_frameIso {k l : Frame core degree} (fi : FrameIso k l) (j : Fin p) :
    slotColumn l (fi.column j) = slotColumn k j := by
  classical
  set transported := GeometricMultiplicity.transportLabelling fi.datum k.fullDim.valid.1
    k.fullDim.labelling with htrans
  set ρ : Fin p ≃ Fin p := l.fullDim.labelling.row.symm.trans transported.row with hρ
  set γ : Fin p ≃ Fin p :=
    l.fullDim.labelling.targetEdge.trans transported.targetEdge.symm with hγ
  have hsub : l.matrix = k.matrix.submatrix ρ γ := by
    show GluingDatum.LengthMatrixPresentation.matrix l.fullDim.labelling.presentation =
      (GluingDatum.LengthMatrixPresentation.matrix k.fullDim.labelling.presentation).submatrix
        ρ γ
    rw [matrix_labelling_submatrix l.fullDim.labelling transported, hρ, hγ,
      GeometricMultiplicity.matrix_transportLabelling fi.datum k.fullDim.valid.1
        k.fullDim.labelling]
  have hslot : ∀ r : Fin p, l.slot r = k.slot (ρ r) := by
    intro r
    have h := fi.overCore_row ((fi.datum.stablePathEquiv k.fullDim.valid.1).symm
      (l.fullDim.labelling.row.symm r))
    rw [Equiv.apply_symm_apply] at h
    have hrowsym : k.fullDim.labelling.row.symm (ρ r) =
        (fi.datum.stablePathEquiv k.fullDim.valid.1).symm (l.fullDim.labelling.row.symm r) := by
      rw [hρ, htrans]
      simp [GeometricMultiplicity.transportLabelling]
    show l.ident.row (l.fullDim.labelling.row.symm r) =
      k.ident.row (k.fullDim.labelling.row.symm (ρ r))
    rw [hrowsym]
    exact h
  have hγcol : γ (fi.column j) = j := by
    rw [hγ, htrans]
    simp [GeometricMultiplicity.transportLabelling, FrameIso.column]
  funext s
  have hs : ρ (l.slot.symm s) = k.slot.symm s := by
    apply k.slot.injective
    rw [← hslot, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  simp only [slotColumn]
  rw [hsub, Matrix.submatrix_apply, hγcol, hs]

variable {y₀ : Fin p → ℚ}

/-- **The retained data of a regrowth**: over the columns other than the vanishing one,
the multiset of pairs (slot-aligned column, coordinate at the facet point).  It is what a
Part I type-change link keeps: the outgoing length matrix agrees with the incoming one
off the vanishing column, the slot dictionary is kept, and so are the coordinates at the
facet point (`FacetAdapterPilot.farFrame_slot`, `farFrame_coordsAt`, `TypeChangeLink.agree`). -/
noncomputable def retained (w : Regrowth core y₀ degree) : Multiset ((Fin p → ℚ) × ℚ) :=
  (Finset.univ.erase w.column).val.map fun j ↦ (slotColumn w.frame j, w.frame.coordsAt y₀ j)

/-- The retained data read through any column bijection that matches the vanishing
columns, the slot-aligned columns and the coordinates. -/
theorem retained_eq_of_perm {core' : Core n p} (w : Regrowth core y₀ degree)
    (w' : Regrowth core' y₀ degree) (π : Fin p ≃ Fin p) (hcol : π w.column = w'.column)
    (hslot : ∀ j, j ≠ w.column → slotColumn w'.frame (π j) = slotColumn w.frame j)
    (hco : ∀ j, j ≠ w.column → w'.frame.coordsAt y₀ (π j) = w.frame.coordsAt y₀ j) :
    retained w' = retained w := by
  classical
  have hset : Finset.univ.erase w'.column = (Finset.univ.erase w.column).map π.toEmbedding := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_map_equiv]
    rw [← hcol]
    exact ⟨fun h h' ↦ h (by rw [← h', Equiv.apply_symm_apply]),
      fun h h' ↦ h (by rw [h', Equiv.symm_apply_apply])⟩
  unfold retained
  rw [hset, Finset.map_val, Multiset.map_map]
  refine Multiset.map_congr rfl fun j hj ↦ ?_
  have hj' : j ≠ w.column := (Finset.mem_erase.mp (Finset.mem_def.mpr hj)).1
  simp only [Function.comp_apply, Equiv.coe_toEmbedding]
  rw [hslot j hj', hco j hj']

/-- **The retained data is an invariant of the geometric frame class.** -/
theorem retained_eq_of_frameIso {w w' : Regrowth core y₀ degree}
    (fi : FrameIso w.frame w'.frame) : retained w' = retained w :=
  retained_eq_of_perm w w' fi.column (GeometricLimitTransport.column_eq_of_frameIso fi)
    (fun j _ ↦ slotColumn_frameIso fi j) (fun j _ ↦ fi.coordsAt_column y₀ j)

end Retained

/-! ## 2.  Specialisation with retained data, and the retained consumer -/

section Consumer

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

/-- A class of the first core specialises to the facet limit `l` **with retained
data `r`**. -/
def RSpecializesLeft (x : FrameClass c degree) (l : FacetLimit c c' y₀ degree)
    (r : Multiset ((Fin p → ℚ) × ℚ)) : Prop :=
  ∃ w : Regrowth c y₀ degree, FrameClass.mk w.frame = x ∧ FacetLimit.ofLeft w = l ∧
    retained w = r

/-- The same over the second core. -/
def RSpecializesRight (x : FrameClass c' degree) (l : FacetLimit c c' y₀ degree)
    (r : Multiset ((Fin p → ℚ) × ℚ)) : Prop :=
  ∃ w : Regrowth c' y₀ degree, FrameClass.mk w.frame = x ∧ FacetLimit.ofRight w = l ∧
    retained w = r

theorem RSpecializesLeft.specializesLeft {x : FrameClass c degree}
    {l : FacetLimit c c' y₀ degree} {r : Multiset ((Fin p → ℚ) × ℚ)}
    (h : RSpecializesLeft x l r) : SpecializesLeft x l :=
  let ⟨w, hx, hl, _⟩ := h; ⟨w, hx, hl⟩

theorem RSpecializesRight.specializesRight {x : FrameClass c' degree}
    {l : FacetLimit c c' y₀ degree} {r : Multiset ((Fin p → ℚ) × ℚ)}
    (h : RSpecializesRight x l r) : SpecializesRight x l :=
  let ⟨w, hx, hl, _⟩ := h; ⟨w, hx, hl⟩

theorem exists_retainedL {x : FrameClass c degree}
    {l : FacetLimit c c' y₀ degree} (h : SpecializesLeft x l) :
    ∃ r, RSpecializesLeft x l r :=
  let ⟨w, hx, hl⟩ := h; ⟨retained w, w, hx, hl, rfl⟩

theorem exists_retainedR {x : FrameClass c' degree}
    {l : FacetLimit c c' y₀ degree} (h : SpecializesRight x l) :
    ∃ r, RSpecializesRight x l r :=
  let ⟨w, hx, hl⟩ := h; ⟨retained w, w, hx, hl, rfl⟩

/-- **The retained data of a specialising class is single-valued.** -/
theorem RSpecializesLeft.unique {x : FrameClass c degree} {l l' : FacetLimit c c' y₀ degree}
    {r r' : Multiset ((Fin p → ℚ) × ℚ)} (h : RSpecializesLeft x l r)
    (h' : RSpecializesLeft x l' r') : r = r' := by
  obtain ⟨w, hw, -, rfl⟩ := h
  obtain ⟨w', hw', -, rfl⟩ := h'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (hw.trans hw'.symm)
  exact (retained_eq_of_frameIso fi).symm

theorem RSpecializesRight.unique {x : FrameClass c' degree} {l l' : FacetLimit c c' y₀ degree}
    {r r' : Multiset ((Fin p → ℚ) × ℚ)} (h : RSpecializesRight x l r)
    (h' : RSpecializesRight x l' r') : r = r' := by
  obtain ⟨w, hw, -, rfl⟩ := h
  obtain ⟨w', hw', -, rfl⟩ := h'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (hw.trans hw'.symm)
  exact (retained_eq_of_frameIso fi).symm

/-- **The retained consumer.**  `FacetParity` from *retained* uniqueness on each side
(at most one odd class per facet limit **and retained datum**) and retained-preserving
existence both ways.  Coarse uniqueness (`huniqL`/`huniqR` of
`LinkReceiptExport.facetParity_of_uniqueness`) implies the retained form
(`retainedUniqueL_of_coarse`), and can fail at valency three (see the module
docstring). -/
theorem facetParity_of_retained
    (huniqL : ∀ (l : FacetLimit c c' y₀ degree) (r : Multiset ((Fin p → ℚ) × ℚ))
      (x x' : FrameClass c degree), x.IsOdd → RSpecializesLeft x l r → x'.IsOdd →
        RSpecializesLeft x' l r → x = x')
    (huniqR : ∀ (l : FacetLimit c c' y₀ degree) (r : Multiset ((Fin p → ℚ) × ℚ))
      (x x' : FrameClass c' degree), x.IsOdd → RSpecializesRight x l r → x'.IsOdd →
        RSpecializesRight x' l r → x = x')
    (hLR : ∀ (l : FacetLimit c c' y₀ degree) (r : Multiset ((Fin p → ℚ) × ℚ))
      (x : FrameClass c degree), x.IsOdd → RSpecializesLeft x l r →
        ∃ x' : FrameClass c' degree, x'.IsOdd ∧ RSpecializesRight x' l r)
    (hRL : ∀ (l : FacetLimit c c' y₀ degree) (r : Multiset ((Fin p → ℚ) × ℚ))
      (x : FrameClass c' degree), x.IsOdd → RSpecializesRight x l r →
        ∃ x' : FrameClass c degree, x'.IsOdd ∧ RSpecializesLeft x' l r) :
    FacetParity c c' degree y₀ := by
  classical
  refine FacetParityPilot.facetParity_of_injective_index
    (ι := Multiset ((Fin p → ℚ) × ℚ))
    (fun l x ↦ (exists_retainedL x.2.2).choose) (fun l x ↦ (exists_retainedR x.2.2).choose)
    (fun l x x' h ↦ ?_) (fun l x x' h ↦ ?_) (fun l ↦ ?_)
  · have hx := (exists_retainedL x.2.2).choose_spec
    have hx' := (exists_retainedL x'.2.2).choose_spec
    simp only at h
    rw [h] at hx
    exact Subtype.ext (huniqL l _ x.1 x'.1 x.2.1 hx x'.2.1 hx')
  · have hx := (exists_retainedR x.2.2).choose_spec
    have hx' := (exists_retainedR x'.2.2).choose_spec
    simp only at h
    rw [h] at hx
    exact Subtype.ext (huniqR l _ x.1 x'.1 x.2.1 hx x'.2.1 hx')
  · ext r
    simp only [Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨x, ⟨hxo, hxs⟩, rfl⟩
      have hx := (exists_retainedL hxs).choose_spec
      obtain ⟨x', hx'o, hx'⟩ := hLR l _ x hxo hx
      exact ⟨x', ⟨hx'o, hx'.specializesRight⟩,
        (hx'.unique (exists_retainedR hx'.specializesRight).choose_spec).symm⟩
    · rintro ⟨x, ⟨hxo, hxs⟩, rfl⟩
      have hx := (exists_retainedR hxs).choose_spec
      obtain ⟨x', hx'o, hx'⟩ := hRL l _ x hxo hx
      exact ⟨x', ⟨hx'o, hx'.specializesLeft⟩,
        (hx'.unique (exists_retainedL hx'.specializesLeft).choose_spec).symm⟩

/-- Coarse uniqueness implies retained uniqueness (the retained form is weaker). -/
theorem retainedUniqueL_of_coarse
    (huniqL : ∀ (l : FacetLimit c c' y₀ degree) (x x' : FrameClass c degree),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x')
    (l : FacetLimit c c' y₀ degree) (r : Multiset ((Fin p → ℚ) × ℚ))
    (x x' : FrameClass c degree) (hx : x.IsOdd) (hs : RSpecializesLeft x l r)
    (hx' : x'.IsOdd) (hs' : RSpecializesLeft x' l r) : x = x' :=
  huniqL l x x' hx hs.specializesLeft hx' hs'.specializesLeft

theorem retainedUniqueR_of_coarse
    (huniqR : ∀ (l : FacetLimit c c' y₀ degree) (x x' : FrameClass c' degree),
      x.IsOdd → SpecializesRight x l → x'.IsOdd → SpecializesRight x' l → x = x')
    (l : FacetLimit c c' y₀ degree) (r : Multiset ((Fin p → ℚ) × ℚ))
    (x x' : FrameClass c' degree) (hx : x.IsOdd) (hs : RSpecializesRight x l r)
    (hx' : x'.IsOdd) (hs' : RSpecializesRight x' l r) : x = x' :=
  huniqR l x x' hx hs.specializesRight hx' hs'.specializesRight

end Consumer

/-! ## 3.  The metric facet limit -/

section Metric

variable {c c' : Core n p} {y₀ : Fin p → ℚ}

/-- The column of a surviving limit edge of a regrowth. -/
noncomputable def limitCol {core : Core n p} (w : Regrowth core y₀ degree)
    (e : (w.frame.limitTarget w.column).edges) : Fin p :=
  w.frame.fullDim.labelling.targetEdge.symm
    (GluingContraction.unfoldEdge rfl (GluingContraction.fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) e)

theorem limitLength_eq {core : Core n p} (w : Regrowth core y₀ degree)
    (e : (w.frame.limitTarget w.column).edges) :
    StarPilot.limitLength w e = w.frame.coordsAt y₀ (limitCol w e) := rfl

/-- A geometric frame isomorphism carries the column of a surviving limit edge along its
column dictionary. -/
theorem limitCol_limitIso {core : Core n p} {w w' : Regrowth core y₀ degree}
    (fi : FrameIso w.frame w'.frame) (e : (w.frame.limitTarget w.column).edges) :
    limitCol w' ((GeometricLimitTransport.limitIso fi).targetEdge e) =
      fi.column (limitCol w e) := by
  unfold limitCol
  rw [GeometricLimitTransport.unfoldEdge_limitIso]
  simp [FrameIso.column]

/-- The surviving target metric of a facet regrowth, on either side
(`StarPilot.limitLength`). -/
noncomputable def limitLength :
    (a : FacetRegrowth c c' y₀ degree) → (FacetRegrowth.limitTarget a).edges → ℚ
  | Sum.inl w => StarPilot.limitLength w
  | Sum.inr w => StarPilot.limitLength w

/-- The slot-aligned length column of a surviving limit edge, on either side: which core
slots' stable paths run over that target edge, and with what weight. -/
noncomputable def limitSlotColumn :
    (a : FacetRegrowth c c' y₀ degree) → (FacetRegrowth.limitTarget a).edges → Fin p → ℚ
  | Sum.inl w => fun e ↦ slotColumn w.frame (limitCol w e)
  | Sum.inr w => fun e ↦ slotColumn w.frame (limitCol w e)

/-- **Same labelled metric facet limit**: a geometric isomorphism of the two limit data
that preserves, edge by edge, the surviving target length and the slot-aligned length
column.  The slot-aligned column carries the core labels (it records which core slots
run over the edge), so this is the cross-core, facet-point form of the paper's labelled
metric limit `φ₀`; `GeometricLimitTransport.MetricLimitIso` is its same-core metric
half. -/
def SameMetricLimit (a b : FacetRegrowth c c' y₀ degree) : Prop :=
  ∃ iso : GeometricDatumIso (FacetRegrowth.limit a) (FacetRegrowth.limit b),
    ∀ e, limitLength b (iso.targetEdge e) = limitLength a e ∧
      limitSlotColumn b (iso.targetEdge e) = limitSlotColumn a e

theorem sameMetricLimit_equivalence :
    Equivalence (SameMetricLimit (c := c) (c' := c') (y₀ := y₀) (degree := degree)) := by
  refine ⟨fun a ↦ ⟨GeometricDatumIso.refl _, fun _ ↦ ⟨rfl, rfl⟩⟩, ?_, ?_⟩
  · rintro a b ⟨iso, h⟩
    refine ⟨iso.symm, fun e ↦ ?_⟩
    have := h (iso.targetEdge.symm e)
    rw [Equiv.apply_symm_apply] at this
    exact ⟨this.1.symm, this.2.symm⟩
  · rintro a b d ⟨iso, h⟩ ⟨iso', h'⟩
    exact ⟨iso.trans iso', fun e ↦ ⟨(h' (iso.targetEdge e)).1.trans (h e).1,
      (h' (iso.targetEdge e)).2.trans (h e).2⟩⟩

/-- The setoid of metric facet limits. -/
def metricSetoid (c c' : Core n p) (y₀ : Fin p → ℚ) (degree : ℕ) :
    Setoid (FacetRegrowth c c' y₀ degree) :=
  ⟨SameMetricLimit, sameMetricLimit_equivalence⟩

/-- **The metric facet limits**: regrowths at the facet point over either core, up to
length-preserving geometric isomorphism of their limit data.  Finer than
`FacetMachine.FacetLimit`; still unlabelled (no core labels). -/
def MetricFacetLimit (c c' : Core n p) (y₀ : Fin p → ℚ) (degree : ℕ) : Type 1 :=
  Quotient (metricSetoid c c' y₀ degree)

namespace MetricFacetLimit

/-- The metric facet limit of a regrowth over the first core. -/
def ofLeft (w : Regrowth c y₀ degree) : MetricFacetLimit c c' y₀ degree :=
  Quotient.mk _ (Sum.inl w)

/-- The metric facet limit of a regrowth over the second core. -/
def ofRight (w : Regrowth c' y₀ degree) : MetricFacetLimit c c' y₀ degree :=
  Quotient.mk _ (Sum.inr w)

/-- Forget the metric. -/
def toCoarse : MetricFacetLimit c c' y₀ degree → FacetLimit c c' y₀ degree :=
  Quotient.map id fun _ _ h ↦ h.elim fun iso _ ↦ ⟨iso⟩

@[simp] theorem toCoarse_ofLeft (w : Regrowth c y₀ degree) :
    toCoarse (ofLeft (c' := c') w) = FacetLimit.ofLeft w := rfl

@[simp] theorem toCoarse_ofRight (w : Regrowth c' y₀ degree) :
    toCoarse (ofRight (c := c) w) = FacetLimit.ofRight w := rfl

end MetricFacetLimit

/-- A class of the first core specialises to the metric facet limit `m`. -/
def MSpecializesLeft (x : FrameClass c degree) (m : MetricFacetLimit c c' y₀ degree) : Prop :=
  ∃ w : Regrowth c y₀ degree, FrameClass.mk w.frame = x ∧ MetricFacetLimit.ofLeft w = m

/-- The same over the second core. -/
def MSpecializesRight (x : FrameClass c' degree) (m : MetricFacetLimit c c' y₀ degree) :
    Prop :=
  ∃ w : Regrowth c' y₀ degree, FrameClass.mk w.frame = x ∧ MetricFacetLimit.ofRight w = m

theorem MSpecializesLeft.specializesLeft {x : FrameClass c degree}
    {m : MetricFacetLimit c c' y₀ degree} (h : MSpecializesLeft x m) :
    SpecializesLeft x m.toCoarse := by
  obtain ⟨w, hx, rfl⟩ := h
  exact ⟨w, hx, rfl⟩

theorem MSpecializesRight.specializesRight {x : FrameClass c' degree}
    {m : MetricFacetLimit c c' y₀ degree} (h : MSpecializesRight x m) :
    SpecializesRight x m.toCoarse := by
  obtain ⟨w, hx, rfl⟩ := h
  exact ⟨w, hx, rfl⟩

theorem exists_metricL {x : FrameClass c degree} {l : FacetLimit c c' y₀ degree}
    (h : SpecializesLeft x l) : ∃ m, m.toCoarse = l ∧ MSpecializesLeft x m := by
  obtain ⟨w, hx, rfl⟩ := h
  exact ⟨MetricFacetLimit.ofLeft w, rfl, w, hx, rfl⟩

theorem exists_metricR {x : FrameClass c' degree} {l : FacetLimit c c' y₀ degree}
    (h : SpecializesRight x l) : ∃ m, m.toCoarse = l ∧ MSpecializesRight x m := by
  obtain ⟨w, hx, rfl⟩ := h
  exact ⟨MetricFacetLimit.ofRight w, rfl, w, hx, rfl⟩

/-- **Metric specialisation is single-valued on classes**: a geometric frame isomorphism
carries the surviving metric (`GeometricLimitTransport.MetricLimitIso.ofFrameIso`). -/
theorem MSpecializesLeft.unique {x : FrameClass c degree}
    {m m' : MetricFacetLimit c c' y₀ degree} (h : MSpecializesLeft x m)
    (h' : MSpecializesLeft x m') : m = m' := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', rfl⟩ := h'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (hw.trans hw'.symm)
  exact Quotient.sound ⟨GeometricLimitTransport.limitIso fi, fun e ↦
    ⟨GeometricLimitTransport.limitLength_limitIso fi e,
      (congrArg (slotColumn w'.frame) (limitCol_limitIso fi e)).trans
        (slotColumn_frameIso fi _)⟩⟩

theorem MSpecializesRight.unique {x : FrameClass c' degree}
    {m m' : MetricFacetLimit c c' y₀ degree} (h : MSpecializesRight x m)
    (h' : MSpecializesRight x m') : m = m' := by
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨w', hw', rfl⟩ := h'
  obtain ⟨fi⟩ := FrameClass.mk_eq_mk_iff.mp (hw.trans hw'.symm)
  exact Quotient.sound ⟨GeometricLimitTransport.limitIso fi, fun e ↦
    ⟨GeometricLimitTransport.limitLength_limitIso fi e,
      (congrArg (slotColumn w'.frame) (limitCol_limitIso fi e)).trans
        (slotColumn_frameIso fi _)⟩⟩

/-! **Remark.**  The at-most-one-odd-class hypotheses consumed below fail in general at
valency four: by Part II a labelled metric limit carries `min(k₂-1, |A|-k₅)+1` members of
each type, two for instance at `(|A|; k) = (3; 2,2,2,2)` and `(4; 2,2,3,3)` in degree four.
The implication stands, but the type-change step uses a census inside each labelled metric
limit with equal counts on the two sides (`FacetCensus`) instead. -/
/-- **The consumer, metric form.**  `FacetParity` from *metric* uniqueness on
each side -- at most one odd class per **metric** facet limit -- and metric-preserving
existence both ways.  Coarse uniqueness implies metric uniqueness
(`metricUniqueL_of_coarse`); the converse can fail at valency three (see the module
docstring). -/
theorem facetParity_of_metric
    (huniqL : ∀ (m : MetricFacetLimit c c' y₀ degree) (x x' : FrameClass c degree),
      x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x')
    (huniqR : ∀ (m : MetricFacetLimit c c' y₀ degree) (x x' : FrameClass c' degree),
      x.IsOdd → MSpecializesRight x m → x'.IsOdd → MSpecializesRight x' m → x = x')
    (hLR : ∀ (m : MetricFacetLimit c c' y₀ degree) (x : FrameClass c degree),
      x.IsOdd → MSpecializesLeft x m → ∃ x' : FrameClass c' degree, x'.IsOdd ∧ MSpecializesRight x' m)
    (hRL : ∀ (m : MetricFacetLimit c c' y₀ degree) (x : FrameClass c' degree),
      x.IsOdd → MSpecializesRight x m → ∃ x' : FrameClass c degree, x'.IsOdd ∧ MSpecializesLeft x' m) :
    FacetParity c c' degree y₀ := by
  classical
  refine FacetParityPilot.facetParity_of_injective_index
    (ι := MetricFacetLimit c c' y₀ degree)
    (fun l x ↦ (exists_metricL x.2.2).choose) (fun l x ↦ (exists_metricR x.2.2).choose)
    (fun l x x' h ↦ ?_) (fun l x x' h ↦ ?_) (fun l ↦ ?_)
  · have hx := (exists_metricL x.2.2).choose_spec.2
    have hx' := (exists_metricL x'.2.2).choose_spec.2
    simp only at h
    rw [h] at hx
    exact Subtype.ext (huniqL _ x.1 x'.1 x.2.1 hx x'.2.1 hx')
  · have hx := (exists_metricR x.2.2).choose_spec.2
    have hx' := (exists_metricR x'.2.2).choose_spec.2
    simp only at h
    rw [h] at hx
    exact Subtype.ext (huniqR _ x.1 x'.1 x.2.1 hx x'.2.1 hx')
  · ext m
    simp only [Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨x, ⟨hxo, hxs⟩, rfl⟩
      obtain ⟨hl, hx⟩ := (exists_metricL hxs).choose_spec
      obtain ⟨x', hx'o, hx'⟩ := hLR _ x hxo hx
      have hs' : SpecializesRight x' l := hl ▸ hx'.specializesRight
      exact ⟨x', ⟨hx'o, hs'⟩, (hx'.unique (exists_metricR hs').choose_spec.2).symm⟩
    · rintro ⟨x, ⟨hxo, hxs⟩, rfl⟩
      obtain ⟨hl, hx⟩ := (exists_metricR hxs).choose_spec
      obtain ⟨x', hx'o, hx'⟩ := hRL _ x hxo hx
      have hs' : SpecializesLeft x' l := hl ▸ hx'.specializesLeft
      exact ⟨x', ⟨hx'o, hs'⟩, (hx'.unique (exists_metricL hs').choose_spec.2).symm⟩

/-- Coarse uniqueness implies metric uniqueness. -/
theorem metricUniqueL_of_coarse
    (huniqL : ∀ (l : FacetLimit c c' y₀ degree) (x x' : FrameClass c degree),
      x.IsOdd → SpecializesLeft x l → x'.IsOdd → SpecializesLeft x' l → x = x')
    (m : MetricFacetLimit c c' y₀ degree) (x x' : FrameClass c degree) (hx : x.IsOdd)
    (hs : MSpecializesLeft x m) (hx' : x'.IsOdd) (hs' : MSpecializesLeft x' m) : x = x' :=
  huniqL _ x x' hx hs.specializesLeft hx' hs'.specializesLeft

theorem metricUniqueR_of_coarse
    (huniqR : ∀ (l : FacetLimit c c' y₀ degree) (x x' : FrameClass c' degree),
      x.IsOdd → SpecializesRight x l → x'.IsOdd → SpecializesRight x' l → x = x')
    (m : MetricFacetLimit c c' y₀ degree) (x x' : FrameClass c' degree) (hx : x.IsOdd)
    (hs : MSpecializesRight x m) (hx' : x'.IsOdd) (hs' : MSpecializesRight x' m) : x = x' :=
  huniqR _ x x' hx hs.specializesRight hx' hs'.specializesRight

end Metric

/-! ## 4.  What the Part I link keeps, with no receipt: the retained data -/

section Transfer

open FacetAdapterPilot MemberCertifiedPencil OuterWalk

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **Off the vanishing column the far frame has the regrowth's slot-aligned columns**
(`TypeChangeLink.agree`, `farFrame_slot`, `MemberSeed.matrix_eq`). -/
theorem slotColumn_farFrame (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms))
    (j : Fin p) (hj : j ≠ w.column) :
    slotColumn (farFrame m' hd hG hDegree w ms link) j = slotColumn w.frame j := by
  funext s
  simp only [slotColumn]
  rw [farFrame_slot, farFrame_matrix]
  have h := link.agree (w.frame.slot.symm s) j hj
  have hin : (moveWallData m' hd hG hDegree w ms).incomingMatrix = w.frame.matrix :=
    ms.matrix_eq
  rw [hin] at h
  exact h.symm

/-- **The far regrowth of any Part I link has the regrowth's retained data.**  No
receipt is used. -/
theorem retained_farRegrowth (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀))
    (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms)) :
    retained (farRegrowth m' hd hG hDegree w ms link) = retained w :=
  retained_eq_of_perm w _ (Equiv.refl _) rfl
    (fun j hj ↦ slotColumn_farFrame m' hd hG hDegree w ms link j hj)
    (fun j _ ↦ congrFun (farFrame_coordsAt m' hd hG hDegree w ms link) j)

/-- **Retained existence transfer, forward, unconditional**: an odd class specialising on
the near side with retained data `r` has an odd far partner specialising to the same
facet limit with the same retained data (the receipts of `LinkReceiptExport` for the
limit, §4 for the data). -/
theorem exists_odd_rSpecializesRight (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (l : FacetLimit c.core (farCore m').core y₀ degree) (r : Multiset ((Fin p → ℚ) × ℚ))
    (x : FrameClass c.core degree) (hx : x.IsOdd) (hs : RSpecializesLeft x l r) :
    ∃ x' : FrameClass (farCore m').core degree, x'.IsOdd ∧ RSpecializesRight x' l r := by
  obtain ⟨w, rfl, rfl, rfl⟩ := hs
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member (w.frame.member y₀) hDegree
  obtain ⟨link, hlink⟩ := LinkReceiptExport.facetLinkReceipts m' hd hG (by omega) w ms
  refine ⟨FrameClass.mk (farFrame m' hd hG (by omega) w ms link),
    (farFrame_isOdd_iff m' hd hG (by omega) w ms link).mpr hx,
    farRegrowth m' hd hG (by omega) w ms link, rfl, ?_, retained_farRegrowth m' hd hG _ w ms link⟩
  exact (ofLeft_eq_ofRight_farRegrowth m' hd hG (by omega) w ms link hlink).symm

theorem rSpecializesLeft_swap_iff {c₁ c₂ : Core n p} {x : FrameClass c₁ degree}
    {l : FacetLimit c₁ c₂ y₀ degree} {r : Multiset ((Fin p → ℚ) × ℚ)} :
    RSpecializesLeft x l r ↔ RSpecializesRight x (FacetLimitSwap.swap l) r := by
  constructor
  · rintro ⟨w, hx, rfl, hr⟩
    exact ⟨w, hx, rfl, hr⟩
  · rintro ⟨w, hx, hl, hr⟩
    refine ⟨w, hx, ?_, hr⟩
    have := congrArg FacetLimitSwap.swap hl
    rwa [FacetLimitSwap.swap_ofRight, FacetLimitSwap.swap_swap] at this

theorem rSpecializesRight_swap_iff {c₁ c₂ : Core n p} {x : FrameClass c₂ degree}
    {l : FacetLimit c₁ c₂ y₀ degree} {r : Multiset ((Fin p → ℚ) × ℚ)} :
    RSpecializesRight x l r ↔ RSpecializesLeft x (FacetLimitSwap.swap l) r := by
  constructor
  · rintro ⟨w, hx, rfl, hr⟩
    exact ⟨w, hx, rfl, hr⟩
  · rintro ⟨w, hx, hl, hr⟩
    refine ⟨w, hx, ?_, hr⟩
    have := congrArg FacetLimitSwap.swap hl
    rwa [FacetLimitSwap.swap_ofLeft, FacetLimitSwap.swap_swap] at this

/-- **Retained existence transfer, reverse**, by the reversed move. -/
theorem exists_odd_rSpecializesLeft {c₁ c₂ : CubicCore n p} (m'' : c₁.graph.MoveData)
    (hback : farCore m'' = c₂)
    (hd : FacetDatum c₁.core (farCore m'').core degree m''.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (l : FacetLimit c₂.core c₁.core y₀ degree) (r : Multiset ((Fin p → ℚ) × ℚ))
    (x' : FrameClass c₁.core degree) (hx : x'.IsOdd) (hs : RSpecializesRight x' l r) :
    ∃ x : FrameClass c₂.core degree, x.IsOdd ∧ RSpecializesLeft x l r := by
  subst hback
  obtain ⟨x, hxo, hxs⟩ := exists_odd_rSpecializesRight m'' hd hG hDegree
    (FacetLimitSwap.swap l) r x' hx (rSpecializesRight_swap_iff.mp hs)
  refine ⟨x, hxo, ?_⟩
  have := rSpecializesRight_swap_iff.mp hxs
  rwa [FacetLimitSwap.swap_swap] at this

/-- **`FacetParity` at a Whitehead step from retained uniqueness alone** -- both existence
halves are discharged (the receipts of `LinkReceiptExport` plus
`retained_farRegrowth`).  Its two hypotheses are weaker than the coarse
`huniqL`/`huniqR` of `LinkReceiptExport.facetParity_of_uniqueness`, **but they too
can fail at valency three** (see the module docstring). -/
theorem facetParity_of_retainedUniqueness (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (huniqL : ∀ (l : FacetLimit c.core (farCore m').core y₀ degree)
      (r : Multiset ((Fin p → ℚ) × ℚ)) (x x' : FrameClass c.core degree),
      x.IsOdd → RSpecializesLeft x l r → x'.IsOdd → RSpecializesLeft x' l r → x = x')
    (huniqR : ∀ (l : FacetLimit c.core (farCore m').core y₀ degree)
      (r : Multiset ((Fin p → ℚ) × ℚ)) (x x' : FrameClass (farCore m').core degree),
      x.IsOdd → RSpecializesRight x l r → x'.IsOdd → RSpecializesRight x' l r → x = x') :
    FacetParity c.core (farCore m').core degree y₀ :=
  facetParity_of_retained huniqL huniqR
    (fun l r x hx hs ↦ exists_odd_rSpecializesRight m' hd hG hDegree l r x hx hs)
    (fun l r x hx hs ↦ exists_odd_rSpecializesLeft (revMove m') (farCore_revMove m')
      (facetDatum_rev m' hd) hG hDegree l r x hx hs)

end Transfer

/-! ## 5.  The metric form at a Whitehead step -/

section MetricStep

open FacetAdapterPilot MemberCertifiedPencil OuterWalk

/-- Exchange the two sides of a metric facet limit. -/
def metricSwap {c₁ c₂ : Core n p} {y₀ : Fin p → ℚ} :
    MetricFacetLimit c₁ c₂ y₀ degree → MetricFacetLimit c₂ c₁ y₀ degree :=
  Quotient.map Sum.swap (by rintro (a | a) (b | b) h <;> exact h)

theorem metricSwap_swap {c₁ c₂ : Core n p} {y₀ : Fin p → ℚ}
    (m : MetricFacetLimit c₁ c₂ y₀ degree) : metricSwap (metricSwap m) = m := by
  induction m using Quotient.inductionOn with
  | h a => rcases a with a | a <;> rfl

theorem mSpecializesLeft_swap_iff {c₁ c₂ : Core n p} {y₀ : Fin p → ℚ}
    {x : FrameClass c₁ degree} {m : MetricFacetLimit c₁ c₂ y₀ degree} :
    MSpecializesLeft x m ↔ MSpecializesRight x (metricSwap m) := by
  constructor
  · rintro ⟨w, hx, rfl⟩
    exact ⟨w, hx, rfl⟩
  · rintro ⟨w, hx, hm⟩
    refine ⟨w, hx, ?_⟩
    have := congrArg metricSwap hm
    rw [metricSwap_swap] at this
    exact this

theorem mSpecializesRight_swap_iff {c₁ c₂ : Core n p} {y₀ : Fin p → ℚ}
    {x : FrameClass c₂ degree} {m : MetricFacetLimit c₁ c₂ y₀ degree} :
    MSpecializesRight x m ↔ MSpecializesLeft x (metricSwap m) := by
  constructor
  · rintro ⟨w, hx, rfl⟩
    exact ⟨w, hx, rfl⟩
  · rintro ⟨w, hx, hm⟩
    refine ⟨w, hx, ?_⟩
    have := congrArg metricSwap hm
    rw [metricSwap_swap] at this
    exact this

variable {c : CubicCore n p} {y₀ : Fin p → ℚ} {ε : ℚ}

/-- **The metric link receipt, at one facet datum** -- the length-preserving
strengthening of `FacetAdapterPilot.FacetLinkReceipts`: every facet regrowth over the
near core admits a Part I link whose far regrowth has the regrowth's **metric** facet
limit.

As an interface: `FacetLinkReceipts` with the limit isomorphism required to preserve
the surviving target lengths.  By `retained_farRegrowth` the far frame already has the
regrowth's coordinates, slot dictionary and length columns off the vanishing column; what
remains is that the limit isomorphism assembled by
`FacetAdapterPilot.ofLeft_eq_ofRight_farRegrowth` matches column labels, i.e. that the
exits' base isomorphism (`LinkLimitReceipt.base_iso`, a sheet relabelling at every exit)
and outgoing labelling are the wall datum's on the retained columns.  It is a statement
about Part I's exits, not about uniqueness; `ColumnReceiptExport` proves it at every
facet datum. -/
def MetricLinkReceipts (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) : Prop :=
  ∀ (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)),
    ∃ link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms),
      SameMetricLimit (c := c.core) (c' := (farCore m').core) (Sum.inl w)
        (Sum.inr (farRegrowth m' hd hG hDegree w ms link))

/-- A surviving limit edge never sits in the vanishing column. -/
theorem limitCol_ne_column {core : Core n p} (w : Regrowth core y₀ degree)
    (e : (w.frame.limitTarget w.column).edges) : limitCol w e ≠ w.column := by
  intro h
  have heq := congrArg w.frame.fullDim.labelling.targetEdge h
  rw [limitCol, Equiv.apply_symm_apply] at heq
  exact GluingContraction.unfoldEdge_ne_contracted rfl
    (GluingContraction.fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    e heq

/-- **The column receipt, at one facet datum** -- the plumbing part of
`MetricLinkReceipts`: every facet regrowth admits a Part I link and an isomorphism of the
two limit data carrying each surviving edge to the surviving edge **of the same column**.

As an interface: a statement about Part I's exits only (the exits reindex the wall
labelling onto the outgoing candidate, and their base isomorphism is a sheet
relabelling); it implies `MetricLinkReceipts` (`metricLinkReceipts_of_column`) because the
far frame has the regrowth's coordinates and slot-aligned columns off the vanishing column
(`retained_farRegrowth`'s two ingredients).  `ColumnReceiptExport` proves it at every
facet datum. -/
def ColumnLinkReceipts (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree) : Prop :=
  ∀ (w : Regrowth c.core y₀ degree) (ms : MemberSeed (w.frame.member y₀)),
    ∃ (link : TypeChangeLink (pulledMove w ms m') (moveWallData m' hd hG hDegree w ms))
      (iso : GeometricDatumIso w.limit (farRegrowth m' hd hG hDegree w ms link).limit),
      ∀ e, limitCol (farRegrowth m' hd hG hDegree w ms link) (iso.targetEdge e) = limitCol w e

/-- **The column receipt gives the labelled metric receipt.** -/
theorem metricLinkReceipts_of_column (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 2 ≤ degree)
    (hcol : ColumnLinkReceipts m' hd hG hDegree) : MetricLinkReceipts m' hd hG hDegree := by
  intro w ms
  obtain ⟨link, iso, hiso⟩ := hcol w ms
  refine ⟨link, iso, fun e ↦ ⟨?_, ?_⟩⟩
  · exact (congrArg ((farRegrowth m' hd hG hDegree w ms link).frame.coordsAt y₀) (hiso e)).trans
      (congrFun (farFrame_coordsAt m' hd hG hDegree w ms link) (limitCol w e))
  · exact (congrArg (slotColumn (farFrame m' hd hG hDegree w ms link)) (hiso e)).trans
      (slotColumn_farFrame m' hd hG hDegree w ms link _ (limitCol_ne_column w e))

/-- The metric receipt implies the conclusion of the coarse receipt
`FacetAdapterPilot.FacetLinkReceipts` (the far regrowth has the
regrowth's facet limit). -/
theorem ofLeft_eq_ofRight_of_sameMetricLimit {c₁ c₂ : Core n p} {w : Regrowth c₁ y₀ degree}
    {w' : Regrowth c₂ y₀ degree}
    (h : SameMetricLimit (c := c₁) (c' := c₂) (Sum.inl w) (Sum.inr w')) :
    FacetLimit.ofLeft (c' := c₂) w = FacetLimit.ofRight w' :=
  Quotient.sound (h.elim fun iso _ ↦ ⟨iso⟩)

/-- **Metric existence transfer, forward, from the metric receipt.** -/
theorem exists_odd_mSpecializesRight (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (hrec : MetricLinkReceipts m' hd hG (by omega))
    (m : MetricFacetLimit c.core (farCore m').core y₀ degree) (x : FrameClass c.core degree)
    (hx : x.IsOdd) (hs : MSpecializesLeft x m) :
    ∃ x' : FrameClass (farCore m').core degree, x'.IsOdd ∧ MSpecializesRight x' m := by
  obtain ⟨w, rfl, rfl⟩ := hs
  obtain ⟨ms⟩ := MemberSeedExists.nonempty_memberSeed_of_member (w.frame.member y₀) hDegree
  obtain ⟨link, hlink⟩ := hrec w ms
  exact ⟨FrameClass.mk (farFrame m' hd hG (by omega) w ms link),
    (farFrame_isOdd_iff m' hd hG (by omega) w ms link).mpr hx,
    farRegrowth m' hd hG (by omega) w ms link, rfl, (Quotient.sound hlink).symm⟩

/-- **Metric existence transfer, reverse**, by the reversed move. -/
theorem exists_odd_mSpecializesLeft {c₁ c₂ : CubicCore n p} (m'' : c₁.graph.MoveData)
    (hback : farCore m'' = c₂)
    (hd : FacetDatum c₁.core (farCore m'').core degree m''.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (hrec : MetricLinkReceipts m'' hd hG (by omega))
    (m : MetricFacetLimit c₂.core c₁.core y₀ degree) (x' : FrameClass c₁.core degree)
    (hx : x'.IsOdd) (hs : MSpecializesRight x' m) :
    ∃ x : FrameClass c₂.core degree, x.IsOdd ∧ MSpecializesLeft x m := by
  subst hback
  obtain ⟨x, hxo, hxs⟩ := exists_odd_mSpecializesRight m'' hd hG hDegree hrec
    (metricSwap m) x' hx (mSpecializesRight_swap_iff.mp hs)
  refine ⟨x, hxo, ?_⟩
  have := mSpecializesRight_swap_iff.mp hxs
  rwa [metricSwap_swap] at this

/-! **Remark.**  As for `facetParity_of_metric`, the at-most-one-odd-class hypotheses
consumed below fail in general at valency four, where a labelled metric limit carries
`min(k₂-1, |A|-k₅)+1` members of each type; the type-change step uses the census of
`FacetCensus` instead. -/
/-- **Valency-three uniqueness in metric form, at a Whitehead step.**  `FacetParity`
from metric uniqueness on each side and the metric link receipts in both directions.
With `metricUniqueL_of_coarse` it contains `LinkReceiptExport.facetParity_of_uniqueness`
modulo the receipts. -/
theorem facetParity_of_metricUniqueness (m' : c.graph.MoveData)
    (hd : FacetDatum c.core (farCore m').core degree m'.base.1 y₀ ε)
    (hG : FacetGenericity.FacetGeneric degree y₀) (hDegree : 3 ≤ degree)
    (huniqL : ∀ (m : MetricFacetLimit c.core (farCore m').core y₀ degree)
      (x x' : FrameClass c.core degree),
      x.IsOdd → MSpecializesLeft x m → x'.IsOdd → MSpecializesLeft x' m → x = x')
    (huniqR : ∀ (m : MetricFacetLimit c.core (farCore m').core y₀ degree)
      (x x' : FrameClass (farCore m').core degree),
      x.IsOdd → MSpecializesRight x m → x'.IsOdd → MSpecializesRight x' m → x = x')
    (hrec : MetricLinkReceipts m' hd hG (by omega))
    (hrec' : MetricLinkReceipts (revMove m') (facetDatum_rev m' hd) hG (by omega)) :
    FacetParity c.core (farCore m').core degree y₀ :=
  facetParity_of_metric huniqL huniqR
    (fun m x hx hs ↦ exists_odd_mSpecializesRight m' hd hG hDegree hrec m x hx hs)
    (fun m x hx hs ↦ exists_odd_mSpecializesLeft (revMove m') (farCore_revMove m')
      (facetDatum_rev m' hd) hG hDegree hrec' m x hx hs)

end MetricStep

/-! ## 7.  Split determination: the arithmetic core -/

namespace Split7

/-- **The survivor indices at a valency-three anchor** (Part II, `subsec-case-v3`), ordered as the
source does: `k₂ ≤ k₅` on the two survivors above the doubled direction `t₂`, `k₃ ≤ k₄` on
the simple directions `t₃`, `t₄`; `(⊞)` is `ThreeBranchAnchor.survivor_index_sum`, and the
three bounds by `|A|` are harmonicity in each direction
(`NonTrivalentValencyThreeAnchor.sum_survivor_index_le_activeTargets`'s fibrewise form). -/
structure AnchorIndices where
  A : ℕ
  k₂ : ℕ
  k₃ : ℕ
  k₄ : ℕ
  k₅ : ℕ
  h25 : k₂ ≤ k₅
  h34 : k₃ ≤ k₄
  tri : k₂ + k₃ + k₄ + k₅ = 2 * A + 1
  doubled : k₂ + k₅ ≤ A
  simple₃ : k₃ ≤ A
  simple₄ : k₄ ≤ A

/-- **A split of the anchor**: the base tree `T₂` (the doubled direction
at the divalent end `u`), or a base tree `T_α` with `α ∈ {3, 4}` (`α4`) together with the
survivor `e_δ`, `δ ∈ {2, 5}` (`δ5`), carried by the divalent vertex `A'`. -/
inductive Split
  | base₂
  | simple (α4 : Bool) (δ5 : Bool)
  deriving DecidableEq

/-- The three combinatorial types `H_{2,3}`, `H_{2,4}`, `H_{2,5}` (Types I, II, III). -/
inductive VType | I | II | III
  deriving DecidableEq

namespace AnchorIndices
variable (a : AnchorIndices)

def kα (α4 : Bool) : ℕ := if α4 then a.k₄ else a.k₃
def kβ (α4 : Bool) : ℕ := if α4 then a.k₃ else a.k₄
def kδ (δ5 : Bool) : ℕ := if δ5 then a.k₅ else a.k₂
def kγ (δ5 : Bool) : ℕ := if δ5 then a.k₂ else a.k₅

/-- Realisability of a split. -/
def Valid : Split → Prop
  | .base₂ => True
  | .simple α4 δ5 => a.kδ δ5 < a.kα α4 ∧ a.kβ α4 + a.kδ δ5 ≤ a.A

instance : DecidablePred a.Valid := fun s ↦ by cases s <;> unfold Valid <;> infer_instance

end AnchorIndices

/-- The type a split produces. -/
def Split.type : Split → VType
  | .base₂ => .III
  | .simple α4 false => if α4 then .II else .I
  | .simple α4 true => if α4 then .I else .II

/-- The split realising each type. -/
def chosen (A k₂ k₄ : ℕ) : VType → Split
  | .I => if k₄ + k₂ ≤ A then .simple false false else .simple true true
  | .II => .simple true false
  | .III => .base₂

/-- Every realisable split is the chosen one of its type. -/
theorem eq_chosen (a : AnchorIndices) (s : Split) (hv : a.Valid s) :
    s = chosen a.A a.k₂ a.k₄ s.type := by
  obtain ⟨A, k₂, k₃, k₄, k₅, h25, h34, tri, dbl, s3, s4⟩ := a
  rcases s with _ | ⟨_ | _, _ | _⟩ <;>
    simp_all [chosen, Split.type, AnchorIndices.Valid, AnchorIndices.kδ, AnchorIndices.kα,
      AnchorIndices.kβ]
  all_goals omega

/-- The chosen split is realisable. -/
theorem valid_chosen (a : AnchorIndices) (t : VType) : a.Valid (chosen a.A a.k₂ a.k₄ t) := by
  obtain ⟨A, k₂, k₃, k₄, k₅, h25, h34, tri, dbl, s3, s4⟩ := a
  cases t
  · by_cases h : k₄ + k₂ ≤ A
    · simp only [chosen, h, ite_true, AnchorIndices.Valid, AnchorIndices.kδ,
        AnchorIndices.kα, AnchorIndices.kβ, Bool.false_eq_true, ite_false, and_true]
      omega
    · simp only [chosen, h, ite_false, AnchorIndices.Valid, AnchorIndices.kδ,
        AnchorIndices.kα, AnchorIndices.kβ, ite_true]
      omega
  · simp only [chosen, AnchorIndices.Valid, AnchorIndices.kδ, AnchorIndices.kα,
      AnchorIndices.kβ, ite_true, Bool.false_eq_true, ite_false]
    constructor <;> omega
  · trivial

theorem type_chosen (A k₂ k₄ : ℕ) (t : VType) : (chosen A k₂ k₄ t).type = t := by
  cases t
  · by_cases h : k₄ + k₂ ≤ A <;> simp [chosen, h, Split.type]
  · rfl
  · rfl

/-- **Split determination, the arithmetic core**: for every type exactly
one split is realisable.  In particular `(3, 5)` never is, and `(3, 2)`, `(4, 5)` are
complementary. -/
theorem existsUnique (a : AnchorIndices) (t : VType) :
    ∃! s : Split, a.Valid s ∧ s.type = t :=
  ⟨chosen a.A a.k₂ a.k₄ t, ⟨valid_chosen a t, type_chosen _ _ _ t⟩, fun s hs ↦
    (eq_chosen a s hs.1).trans (by rw [hs.2])⟩


/-- The derived anchor data of a split: the bridge index `k₁`, the local
degrees `|A_u|`, `|A_v|`. -/
def AnchorIndices.bridge (a : AnchorIndices) : Split → ℕ
  | .base₂ => a.k₂ + a.k₅
  | .simple α4 δ5 => a.kα α4 - a.kδ δ5

def AnchorIndices.degV (a : AnchorIndices) : Split → ℕ
  | .base₂ => a.A
  | .simple _ δ5 => a.A - a.kδ δ5

/-- **Case (r0) at `A_v`**: `2|A_v| + 1` is the sum of its three surviving indices, for
every realisable split (the identity the source uses to *compute* `|A_v|`). -/
theorem AnchorIndices.r0_at_Av (a : AnchorIndices) (s : Split) (hv : a.Valid s) :
    2 * a.degV s + 1 = a.bridge s + (match s with
      | .base₂ => a.k₃ + a.k₄
      | .simple α4 δ5 => a.kβ α4 + a.kγ δ5) := by
  obtain ⟨A, k₂, k₃, k₄, k₅, h25, h34, tri, dbl, s3, s4⟩ := a
  rcases s with _ | ⟨_ | _, _ | _⟩
  all_goals simp only [AnchorIndices.degV, AnchorIndices.bridge, AnchorIndices.Valid,
    AnchorIndices.kδ, AnchorIndices.kα, AnchorIndices.kβ, AnchorIndices.kγ,
    Bool.false_eq_true, ite_true, ite_false] at hv ⊢
  all_goals omega

/-- **`A_v` is a valid vertex** at every realisable split: its local degree bounds each
incident index. -/
theorem AnchorIndices.degV_ge (a : AnchorIndices) (s : Split) (hv : a.Valid s) :
    a.bridge s ≤ a.degV s ∧ (match s with
      | .base₂ => a.k₃ ≤ a.degV s ∧ a.k₄ ≤ a.degV s
      | .simple α4 δ5 => a.kβ α4 ≤ a.degV s ∧ a.kγ δ5 ≤ a.degV s) := by
  obtain ⟨A, k₂, k₃, k₄, k₅, h25, h34, tri, dbl, s3, s4⟩ := a
  rcases s with _ | ⟨_ | _, _ | _⟩
  all_goals simp only [AnchorIndices.degV, AnchorIndices.bridge, AnchorIndices.Valid,
    AnchorIndices.kδ, AnchorIndices.kα, AnchorIndices.kβ, AnchorIndices.kγ,
    Bool.false_eq_true, ite_true, ite_false] at hv ⊢
  all_goals refine ⟨?_, ?_, ?_⟩
  all_goals omega

/-! ### The anchor indices of an actual wall datum -/

section AnchorBridge

open DraismaVargas.LocalCases.W4Assembly DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.W3R1SourceProfile
open DraismaVargas.LocalCases.NonTrivalentValencyThreeAnchor
open DraismaVargas.LocalCases.ThirdEquation (ThreeStar)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

theorem fin3_others (d : Fin 3) :
    ∃ l l' : Fin 3, l ≠ d ∧ l' ≠ d ∧ l ≠ l' ∧ ∀ x : Fin 3, x = d ∨ x = l ∨ x = l' := by
  fin_cases d
  · exact ⟨1, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide, by decide⟩

/-- **Anchor localization, numeric form.**  The valency-three census
(`NonTrivalentValencyThreeAnchor.ThreeBranchAnchor`) of an actual wall block produces the
source's ordered survivor indices: an `AnchorIndices` whose `|A|` is the block's local
degree, whose `k₂ + k₅` is the index sum over the doubled direction, and whose `k₃ + k₄`
is the index sum over the two simple directions.  So `existsUnique` applies to every
actual valency-three wall datum. -/
theorem exists_anchorIndices (data : GluingDatum target degree) (star : ThreeStar target wall)
    (block : WallBlock data wall) (h : ThreeBranchAnchor data star block) :
    ∃ (a : AnchorIndices) (d : Fin 3),
      a.A = (data.vertexPartition wall).blockCard block.1 ∧
      (∑ e ∈ directionSurvivors data star block d, (data.sourceEdgeIndex e.1 : ℤ)) =
        a.k₂ + a.k₅ ∧
      (∑ e ∈ (survivors data block).filter (fun e ↦ survivorLabel data star block e ≠ d),
        (data.sourceEdgeIndex e.1 : ℤ)) = a.k₃ + a.k₄ := by
  classical
  obtain ⟨d, hd2, hd1⟩ := h.distribution
  obtain ⟨l, l', hl, hl', hll', hall⟩ := fin3_others d
  obtain ⟨x, y, hxy, hxyEq⟩ := Finset.card_eq_two.mp hd2
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp (hd1 l hl)
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp (hd1 l' hl')
  set idx : IncidentSourceEdge data (WallBlock.sourceVertex data wall block) → ℕ :=
    fun e ↦ data.sourceEdgeIndex e.1 with hidx
  set A := (data.vertexPartition wall).blockCard block.1 with hA
  -- harmonicity in each direction
  have harm : ∀ lab : Fin 3,
      (∑ e ∈ directionSurvivors data star block lab, (idx e : ℤ)) ≤ (A : ℤ) := by
    intro lab
    have hb := sum_index_le_of_same_target data (WallBlock.sourceVertex data wall block)
      (directionSurvivors data star block lab) (directionEdge star lab)
      (by
        change directionEdge star lab ∈ GluingDatum.incidentEdges wall
        exact directionEdge_mem_incidentEdges star lab)
      (fun e he ↦ ((mem_directionSurvivors data star block lab e).mp he).2)
    simpa only [WallBlock.sourceVertex, GluingDatum.sourceEndpoint, block.2] using hb
  -- the survivor sum splits by direction
  have hsplit : (∑ e ∈ survivors data block, (idx e : ℤ)) =
      ∑ lab : Fin 3, ∑ e ∈ directionSurvivors data star block lab, (idx e : ℤ) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (s := survivors data block) (t := (Finset.univ : Finset (Fin 3)))
      (g := survivorLabel data star block) (fun _ _ ↦ Finset.mem_univ _)
      (fun e ↦ (idx e : ℤ))]
    rfl
  have hsum := h.survivor_index_sum
  have hd := harm d
  have hlb := harm l
  have hl'b := harm l'
  rw [hxyEq, Finset.sum_pair hxy] at hd
  rw [hz, Finset.sum_singleton] at hlb
  rw [hw, Finset.sum_singleton] at hl'b
  have htot : (idx x : ℤ) + idx y + idx z + idx w = 2 * (A : ℤ) + 1 := by
    -- the three labels are d, l, l'
    have key : (∑ lab : Fin 3, ∑ e ∈ directionSurvivors data star block lab, (idx e : ℤ)) =
        (∑ e ∈ directionSurvivors data star block d, (idx e : ℤ)) +
        (∑ e ∈ directionSurvivors data star block l, (idx e : ℤ)) +
        (∑ e ∈ directionSurvivors data star block l', (idx e : ℤ)) := by
      have huniv : (Finset.univ : Finset (Fin 3)) = {d, l, l'} := by
        ext x'
        simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
        exact hall x'
      rw [huniv, Finset.sum_insert (by simp [Ne.symm hl, Ne.symm hl']),
        Finset.sum_pair hll', add_assoc]
    have h2 := hsplit.symm.trans hsum
    rw [key, hxyEq, Finset.sum_pair hxy, hz, Finset.sum_singleton, hw,
      Finset.sum_singleton] at h2
    linarith
  have hxyN : idx x + idx y ≤ A := by exact_mod_cast hd
  have hzN : idx z ≤ A := by exact_mod_cast hlb
  have hwN : idx w ≤ A := by exact_mod_cast hl'b
  have htotN : idx x + idx y + idx z + idx w = 2 * A + 1 := by exact_mod_cast htot
  obtain ⟨k₂, k₅, hk25, hs25⟩ : ∃ k₂ k₅ : ℕ, k₂ ≤ k₅ ∧ k₂ + k₅ = idx x + idx y := by
    rcases le_total (idx x) (idx y) with h' | h'
    · exact ⟨_, _, h', rfl⟩
    · exact ⟨_, _, h', add_comm _ _⟩
  obtain ⟨k₃, k₄, hk34, hs34, hk3, hk4⟩ : ∃ k₃ k₄ : ℕ, k₃ ≤ k₄ ∧ k₃ + k₄ = idx z + idx w ∧
      k₃ ≤ A ∧ k₄ ≤ A := by
    rcases le_total (idx z) (idx w) with h' | h'
    · exact ⟨_, _, h', rfl, hzN, hwN⟩
    · exact ⟨_, _, h', add_comm _ _, hwN, hzN⟩
  have hzw : z ≠ w := by
    intro hzw
    have hzl : z ∈ directionSurvivors data star block l := by rw [hz]; simp
    have hwl : w ∈ directionSurvivors data star block l' := by rw [hw]; simp
    rw [directionSurvivors, Finset.mem_filter] at hzl hwl
    exact hll' (hzl.2.symm.trans (hzw ▸ hwl.2))
  have hfilter : (survivors data block).filter (fun e ↦ survivorLabel data star block e ≠ d) =
      {z, w} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hs, hne⟩
      rcases hall (survivorLabel data star block e) with h' | h' | h'
      · exact absurd h' hne
      · left
        have : e ∈ directionSurvivors data star block l := by
          rw [directionSurvivors, Finset.mem_filter]; exact ⟨hs, h'⟩
        rw [hz] at this
        exact Finset.mem_singleton.mp this
      · right
        have : e ∈ directionSurvivors data star block l' := by
          rw [directionSurvivors, Finset.mem_filter]; exact ⟨hs, h'⟩
        rw [hw] at this
        exact Finset.mem_singleton.mp this
    · rintro (rfl | rfl)
      · have : e ∈ directionSurvivors data star block l := by rw [hz]; simp
        rw [directionSurvivors, Finset.mem_filter] at this
        exact ⟨this.1, this.2 ▸ hl⟩
      · have : e ∈ directionSurvivors data star block l' := by rw [hw]; simp
        rw [directionSurvivors, Finset.mem_filter] at this
        exact ⟨this.1, this.2 ▸ hl'⟩
  refine ⟨⟨A, k₂, k₃, k₄, k₅, hk25, hk34, by omega, by omega, hk3, hk4⟩, d, rfl, ?_, ?_⟩
  · rw [hxyEq, Finset.sum_pair hxy]
    exact_mod_cast hs25.symm
  · rw [hfilter, Finset.sum_pair hzw]
    exact_mod_cast hs34.symm

end AnchorBridge

end Split7

end DraismaVargas.Count.ValencyThreeGeneral
