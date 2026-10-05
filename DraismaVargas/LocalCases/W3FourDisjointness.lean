module

public import DraismaVargas.LocalCases.W3FourSourceCandidates
public import DraismaVargas.LocalCases.RelabelFullDimensional

@[expose] public section

/-!
# Figure 28: `Disjoint e₂ e₃` is a sheet-labelling gauge, not a datum invariant

Source: Draisma--Vargas Part I (arXiv:1909.12924).  The case is
`{w3-r1-nd3-t2-(a=k₄)}` of Section 6, with Figure 28 and the Positions defined
in Case `{w3-r1-nd3-t2}`.  The decisive statements are, in Section 3, the
**branch-swap** (introduced just before Definition `definition-gd-iso`), the
Definition of *gluing datum isomorphism* (`definition-gd-iso`) and Lemma
`lemma-iso-classes-dtmor-gd` (isomorphism classes of gluing datums are in
bijection with isomorphism classes of `Δ`-morphisms); and, in Section 6, the
definition of `ℙ𝒞*(M₀)` as a set of **isomorphism classes** of possibly
full-dimensional gluing datums contracting to a limit *isomorphic to* `M₀`.

## The question this module answers

`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint` shows that, on
one fixed wall datum, Position I (which forces `e₂` and `e₃` to tile `A₀`) and
Position II.b (which forces them to meet) cannot both hold.  The question is
whether some global hypothesis -- full-dimensionality, `lemma-pass-once`,
`prop-adm-matrix`, the global no-return corollary -- decides which of the two
occurs.

It does not, and no hypothesis of that kind can: `Disjoint e₂ e₃` is not an
isomorphism invariant of the wall datum.  The branch-swap of Part I picks a
connected component of `T ∖ {w₀}` and applies one sheet permutation to every
gluing relation in it; when the permutation preserves each block of `∼_{w₀}`
this is an isomorphism of gluing datums by `definition-gd-iso`, hence an
isomorphism of the associated `Δ`-morphism by `lemma-iso-classes-dtmor-gd`.
Choosing the branch
through `t₃` leaves `A₀`, `e₂` and `e₄` *literally* unchanged and replaces `e₃`
by its image, which can be placed either inside or outside `e₂`.

Two things in that paragraph are readings of the source rather than Lean
theorems, and are flagged as such wherever they are used below: that
`GluingDatum.SheetRelabeling` is the Definition `definition-gd-iso` (it is that
definition's data -- one permutation per target vertex and per target edge,
with the incidence condition -- for a fixed base tree), and that `ℙ𝒞*(M₀)`'s
members are therefore free to use different representatives of `M₀`.  The Lean
content is the construction of the swap and the list of things it does not
move.

## What is proved here

* `branchSwapOfPerm` -- the branch swap at a wall by an arbitrary permutation
  preserving every wall block setwise, generalizing
  `ResolutionM11.wallBranchSwap` from a transposition.  Its wall vertex
  partition and every unmoved edge partition are equalities of terms, not
  isomorphisms (`branchSwapOfPerm_vertexPartition_wall`,
  `branchSwapOfPerm_edgePartition_of_fixed`).
* `BranchGauge` -- the package of wall data the swap leaves alone:
  the wall partition, every unmoved edge partition, `targetExcess wall`,
  `Valid`, `DanglingEdgeNoGlue`, and the stable-row count.  These cover every
  field of `ThirdEquation.W3SourceInput` except `nonDangling_valency`, which
  transports along `SheetRelabelStable.nonDanglingValency_map`; that last
  assembly is not carried out here, so no transported `W3SourceInput` is
  claimed.
* `fullDimensional_gauge` -- a `FullDimensionalSourcePresentation` transports
  across any branch swap (immediately from
  `RelabelFullDimensional.sheetPresentation`).  This is the precise sense in
  which `det_ne_zero` cannot see the disjointness: the swapped datum has the
  same length matrix.
* `exists_perm_image_disjoint` -- inside one wall block, a series of
  transpositions moves `e₃` off `e₂` whenever `|e₂| + |e₃| = |A₀|`; this is
  Part I's "a series of branch-swaps".
* `exists_branchGauge_not_disjoint` and `exists_branchGauge_disjoint` -- both
  Figure 28 alternatives are realized on branch-swapped copies of *the same*
  datum, with `e₂` fixed and `e₃` keeping its index.
* `disjointness_not_gauge_invariant` -- the verdict in one statement.

## Why the hypotheses can hold at once

`exists_branchGauge_disjoint` bundles refinement, two wall relations and an
index identity about one datum.  They are jointly satisfiable because a
`W3FourSourceCandidates.GrowProfile` supplies all four at once on the actual
case datum: `growTarget_refines` and `refines_of_mem_incidentEdges` give the
two refinements, `growAnchor_wall_rel` and `otherAnchor_wall_rel` the two wall
relations, and the field `index_sum` is exactly `k₂ + k₃ = |A₀|`, the defining
identity of `{w3-r1-nd3-t2-(a=k₄)}`.  The two branch flags are independent of
those and are satisfiable on any target tree; see the last section below.

## Which datum this is about

Everything is stated for an arbitrary `GluingDatum`, so both sides of the
bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput` are covered:
the wall/limit side, where `ThirdEquation.W3SourceInput` lives and
`targetExcess wall = 1`, and the full-dimensional side, where
`FullDimensionalSourcePresentation` lives and every target vertex is
change-minimal.  No single object is asked to satisfy both; `BranchGauge`
speaks about the first and `fullDimensional_gauge` about the second.

## What is not proved here

That Figure 28's `M⁽¹⁾` and `M⁽²⁾` *exist* as members of `ℙ𝒞*(M₀)`.  On one
fixed sheet labelling the two Positions exclude each other
(`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`); this module
shows that exclusion to be an artefact of fixing one sheet labelling -- the two
Positions do not demand contradictory things of one isomorphism class -- but
it does not build the regrown candidates themselves.  Nor is the branch
containing `t₃` and avoiding
`t₂`, `t₄` constructed: that needs the target to be a tree, and is left as the
hypotheses `hGrowFixed`, `hOtherMoved` below, which
`TargetBranchRegion.vertexMoved` makes decidable on any concrete target.  On a
target tree they hold with `root` the far endpoint of `t₃`: the components of
`T ∖ {w₀}` through `t₂`, `t₃`, `t₄` are then distinct.
`Infrastructure.TargetSeparation.separated_of_genus_zero` proves exactly
this pair from `graph_connected target` and `genus target = 0`, but
`exists_branchGauge_disjoint`, `exists_branchGauge_not_disjoint` and
`disjointness_not_gauge_invariant` take neither of those two hypotheses --
only `data`, `wall`, `root`, `hRoot`, and the two named occurrences with their
anchors -- so `hGrowFixed` and `hOtherMoved` stay carried below: adding the
target-tree hypotheses to these signatures would only relocate the carried
assumption, not discharge it.
-/

namespace DraismaVargas.LocalCases.W3FourDisjointness

open DraismaVargas.Infrastructure
open GluingDatum.SheetRelabeling
open W4StableSource FullDimensionalSource

variable {target : CFGraph} {degree : ℕ}

section BranchSwap

/-! ## The branch swap by an arbitrary block-preserving permutation -/

/-- A permutation that preserves one block setwise and fixes everything
outside it moves every sheet inside its own block. -/
theorem rel_of_stabilizes_block (partition : SheetPartition degree)
    (anchor : Fin degree) (permutation : Equiv.Perm (Fin degree))
    (hInside : ∀ sheet ∈ partition.block anchor,
      permutation sheet ∈ partition.block anchor)
    (hOutside : ∀ sheet, sheet ∉ partition.block anchor → permutation sheet = sheet)
    (sheet : Fin degree) : partition.Rel (permutation sheet) sheet := by
  by_cases hMem : sheet ∈ partition.block anchor
  · have hImage := hInside sheet hMem
    exact ((partition.mem_block_iff anchor _).mp hImage).symm.trans
      ((partition.mem_block_iff anchor sheet).mp hMem)
  · rw [hOutside sheet hMem]
    exact rfl

/-- **The branch-swap of Draisma--Vargas Part I at an arbitrary degree, by an
arbitrary permutation.**  Select the connected component of `root` in the
target with
`wall` deleted and relabel every gluing relation there.  Every
selected/unselected incidence is forced to sit at `wall`, where the
permutation preserves the partition by hypothesis.  This generalizes
`ResolutionM11.wallBranchSwap`, which is the special case of a
transposition. -/
def branchSwapOfPerm (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall)
    (permutation : Equiv.Perm (Fin degree))
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet) :
    data.SheetRelabeling :=
  GluingDatum.SheetRelabeling.ofRegion
    (TargetBranchRegion.vertexMoved wall root hRoot)
    (TargetBranchRegion.edgeMoved wall root hRoot)
    permutation
    (fun edge hDifferent sheet ↦ by
      rw [TargetBranchRegion.boundary_left wall root hRoot edge hDifferent]
      exact hFix sheet)
    (fun edge hDifferent sheet ↦ by
      rw [TargetBranchRegion.boundary_right wall root hRoot edge hDifferent]
      exact hFix sheet)

variable (data : GluingDatum target degree) (wall root : target.V)
  (hRoot : root ≠ wall) (permutation : Equiv.Perm (Fin degree))
  (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)

/-- The cut vertex is outside the moved branch, so its partition is unchanged
as a term. -/
theorem branchSwapOfPerm_vertexPartition_wall :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.vertexPartition
        wall = data.vertexPartition wall := by
  change (data.vertexPartition wall).relabel
    (togglePermutation (TargetBranchRegion.vertexMoved wall root hRoot wall)
      permutation) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  cases hPartition : data.vertexPartition wall
  rfl

/-- Every target edge outside the moved branch keeps its partition as a
term. -/
theorem branchSwapOfPerm_edgePartition_of_fixed (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        edge = data.edgePartition edge := by
  change (data.edgePartition edge).relabel
    (togglePermutation (TargetBranchRegion.edgeMoved wall root hRoot edge)
      permutation) = _
  rw [hFixed]
  cases hPartition : data.edgePartition edge
  rfl

/-- Every target edge inside the moved branch is relabelled. -/
theorem branchSwapOfPerm_edgePartition_of_moved (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
        edge = (data.edgePartition edge).relabel permutation := by
  change (data.edgePartition edge).relabel
    (togglePermutation (TargetBranchRegion.edgeMoved wall root hRoot edge)
      permutation) = _
  rw [hMoved]
  rfl

/-- The wall's local Riemann--Hurwitz census is untouched: the relabelled edge
partition induces the same number of blocks inside every wall block. -/
theorem branchSwapOfPerm_blockCountWithin_wall (edge : target.edges)
    (sheet : Fin degree) :
    ((branchSwapOfPerm data wall root hRoot permutation hFix).apply.edgePartition
          edge).blockCountWithin
        ((branchSwapOfPerm data wall root hRoot permutation
          hFix).apply.vertexPartition wall) sheet =
      (data.edgePartition edge).blockCountWithin
        (data.vertexPartition wall) sheet := by
  rw [branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix]
  cases hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge
  · rw [branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot permutation
      hFix edge hMoved]
  · rw [branchSwapOfPerm_edgePartition_of_moved data wall root hRoot permutation
      hFix edge hMoved]
    exact SheetPartition.relabel_blockCountWithin_fixed_of_pointwise
      (data.edgePartition edge) (data.vertexPartition wall) permutation hFix sheet

omit hFix in
/-- `ch(v)` depends only on the vertex partition at `v` and on the induced
block counts of the incident edge partitions. -/
theorem targetChange_congr {first second : GluingDatum target degree}
    {vertex : target.V}
    (hVertex : first.vertexPartition vertex = second.vertexPartition vertex)
    (hCount : ∀ edge sheet,
      (first.edgePartition edge).blockCountWithin
          (first.vertexPartition vertex) sheet =
        (second.edgePartition edge).blockCountWithin
          (second.vertexPartition vertex) sheet) :
    first.targetChange vertex = second.targetChange vertex := by
  unfold GluingDatum.targetChange GluingDatum.localRamification
  rw [hVertex]
  refine Finset.sum_congr rfl ?_
  intro sourceBlock _
  rw [hVertex] at hCount
  rw [Finset.sum_congr rfl (fun edge _ ↦ by rw [hCount edge sourceBlock.1])]

/-- Equation (C)'s wall excess is a branch-swap invariant.  A
`ThirdEquation.W3SourceInput`'s `equation_c` therefore survives the swap. -/
theorem branchSwapOfPerm_targetExcess_wall :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.targetExcess
        wall = data.targetExcess wall := by
  unfold GluingDatum.targetExcess
  rw [targetChange_congr
    (branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix)
    (branchSwapOfPerm_blockCountWithin_wall data wall root hRoot permutation hFix)]

/-! ## The invariants a branch swap does not move -/

/-- The wall data a branch swap leaves alone.  These are the fields of
`ThirdEquation.W3SourceInput` other than `nonDangling_valency`. -/
structure BranchGauge (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall)
    (relabeling : data.SheetRelabeling) : Prop where
  /-- The wall block structure is literally the same partition. -/
  wallPartition : relabeling.apply.vertexPartition wall = data.vertexPartition wall
  /-- Every target edge outside the moved branch keeps its partition. -/
  fixedEdges : ∀ edge, TargetBranchRegion.edgeMoved wall root hRoot edge = false →
    relabeling.apply.edgePartition edge = data.edgePartition edge
  /-- Equation (C)'s excess at the wall is unchanged. -/
  targetExcess : relabeling.apply.targetExcess wall = data.targetExcess wall
  /-- Gluing-datum validity is preserved. -/
  valid : data.Valid → relabeling.apply.Valid
  /-- Dangling-no-glue is preserved. -/
  noGlue : data.Valid → DanglingEdgeNoGlue data → DanglingEdgeNoGlue relabeling.apply
  /-- The stable-row count is preserved. -/
  stablePathCard : data.Valid →
    Fintype.card (StablePath relabeling.apply) = Fintype.card (StablePath data)

/-- Every branch swap by a block-preserving permutation is a gauge. -/
theorem branchSwapOfPerm_branchGauge :
    BranchGauge data wall root hRoot
      (branchSwapOfPerm data wall root hRoot permutation hFix) where
  wallPartition :=
    branchSwapOfPerm_vertexPartition_wall data wall root hRoot permutation hFix
  fixedEdges := branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot
    permutation hFix
  targetExcess :=
    branchSwapOfPerm_targetExcess_wall data wall root hRoot permutation hFix
  valid := fun hValid ↦ GluingDatum.SheetRelabeling.valid _ hValid
  noGlue := fun hValid hNoGlue ↦
    SheetRelabelStable.danglingEdgeNoGlue_map _ hValid.1 hNoGlue
  stablePathCard := fun hValid ↦
    (Fintype.card_congr (SheetRelabelStable.stablePathEquiv _ hValid.1)).symm

omit hFix in
/-- **Full-dimensionality is blind to a branch swap.**  The relabelled datum
carries a full-dimensional presentation in the same coordinates, with the same
length matrix, hence the same determinant.  So neither `det_ne_zero` nor
anything derived from it -- `lemma-pass-once`, `prop-adm-matrix`, the global
no-return corollary -- can distinguish a datum from its branch swap. -/
noncomputable def fullDimensional_gauge {coordinate : Type*}
    [Fintype coordinate] [DecidableEq coordinate]
    (source : FullDimensionalSourcePresentation data coordinate) :
    FullDimensionalSourcePresentation
      (branchSwapOfPerm data wall root hRoot permutation hFix).apply coordinate :=
  RelabelFullDimensional.sheetPresentation _ source

end BranchSwap

/-! ## A series of branch-swaps inside one wall block

Part I, in the discussion before `definition-gd-iso`: "A series of
branch-swaps enables us to relate two distinct choices."  The permutation below
is exactly such a series: each step is a transposition
of two sheets of the wall block `A`, so each step is a legal branch-swap.
-/

/-- Membership in the image of a finset under a transposition. -/
theorem mem_image_swap {first second : Fin degree} (sheets : Finset (Fin degree))
    (sheet : Fin degree) :
    sheet ∈ sheets.image (Equiv.swap first second) ↔
      (Equiv.swap first second) sheet ∈ sheets := by
  classical
  constructor
  · intro hMem
    obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hMem
    simpa using hSource
  · intro hMem
    exact Finset.mem_image.mpr ⟨(Equiv.swap first second) sheet, hMem, by simp⟩

private theorem exists_perm_image_disjoint_aux (whole small : Finset (Fin degree))
    (hSmall : small ⊆ whole) :
    ∀ steps (other : Finset (Fin degree)), (small ∩ other).card ≤ steps →
      other ⊆ whole → small.card + other.card = whole.card →
      ∃ permutation : Equiv.Perm (Fin degree),
        (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
          (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
          Disjoint small (other.image permutation) := by
  classical
  intro steps
  induction steps with
  | zero =>
      intro other hLe _ _
      refine ⟨Equiv.refl _, fun sheet hSheet ↦ hSheet, fun _ _ ↦ rfl, ?_⟩
      have hEmpty : small ∩ other = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hLe)
      simpa [Finset.disjoint_iff_inter_eq_empty] using hEmpty
  | succ steps ih =>
      intro other hLe hOther hCard
      by_cases hDone : (small ∩ other).card = 0
      · refine ⟨Equiv.refl _, fun sheet hSheet ↦ hSheet, fun _ _ ↦ rfl, ?_⟩
        have hEmpty : small ∩ other = ∅ := Finset.card_eq_zero.mp hDone
        simpa [Finset.disjoint_iff_inter_eq_empty] using hEmpty
      · obtain ⟨shared, hShared⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hDone)
        have hSharedSmall : shared ∈ small := (Finset.mem_inter.mp hShared).1
        have hSharedOther : shared ∈ other := (Finset.mem_inter.mp hShared).2
        have hUnionSub : small ∪ other ⊆ whole := Finset.union_subset hSmall hOther
        have hUnionCard := Finset.card_union_add_card_inter small other
        have hFreeExists : (whole \ (small ∪ other)).Nonempty := by
          rw [← Finset.card_pos, Finset.card_sdiff,
            Finset.inter_eq_left.mpr hUnionSub]
          have hPos : 0 < (small ∩ other).card := Nat.pos_of_ne_zero hDone
          omega
        obtain ⟨free, hFree⟩ := hFreeExists
        have hFreeWhole : free ∈ whole := (Finset.mem_sdiff.mp hFree).1
        have hFreeNot : free ∉ small ∪ other := (Finset.mem_sdiff.mp hFree).2
        have hFreeSmall : free ∉ small := fun h ↦ hFreeNot (Finset.mem_union_left _ h)
        have hFreeOther : free ∉ other := fun h ↦ hFreeNot (Finset.mem_union_right _ h)
        have hSharedWhole : shared ∈ whole := hSmall hSharedSmall
        have hStepWhole : ∀ sheet, sheet ∈ whole →
            (Equiv.swap free shared) sheet ∈ whole := by
          intro sheet hSheet
          rw [Equiv.swap_apply_def]
          split_ifs
          · exact hSharedWhole
          · exact hFreeWhole
          · exact hSheet
        have hStepOut : ∀ sheet, sheet ∉ whole →
            (Equiv.swap free shared) sheet = sheet := by
          intro sheet hSheet
          refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
          · rintro rfl; exact hSheet hFreeWhole
          · rintro rfl; exact hSheet hSharedWhole
        have hNextSub : other.image (Equiv.swap free shared) ⊆ whole := by
          intro sheet hSheet
          obtain ⟨source, hSource, rfl⟩ := Finset.mem_image.mp hSheet
          exact hStepWhole source (hOther hSource)
        have hNextCard : (other.image (Equiv.swap free shared)).card = other.card :=
          Finset.card_image_of_injective _ (Equiv.injective _)
        have hNextInter :
            small ∩ other.image (Equiv.swap free shared) = (small ∩ other).erase shared := by
          ext sheet
          simp only [Finset.mem_inter, Finset.mem_erase, mem_image_swap]
          constructor
          · rintro ⟨hSheetSmall, hSheetOther⟩
            have hNeShared : sheet ≠ shared := by
              rintro rfl
              rw [Equiv.swap_apply_right] at hSheetOther
              exact hFreeOther hSheetOther
            have hNeFree : sheet ≠ free := fun h ↦ hFreeSmall (h ▸ hSheetSmall)
            exact ⟨hNeShared, hSheetSmall, by
              rwa [Equiv.swap_apply_of_ne_of_ne hNeFree hNeShared] at hSheetOther⟩
          · rintro ⟨hNeShared, hSheetSmall, hSheetOther⟩
            have hNeFree : sheet ≠ free := fun h ↦ hFreeSmall (h ▸ hSheetSmall)
            exact ⟨hSheetSmall, by
              rwa [Equiv.swap_apply_of_ne_of_ne hNeFree hNeShared]⟩
        have hNextLe : (small ∩ other.image (Equiv.swap free shared)).card ≤ steps := by
          rw [hNextInter, Finset.card_erase_of_mem hShared]
          omega
        obtain ⟨rest, hRestWhole, hRestOut, hRestDisjoint⟩ :=
          ih (other.image (Equiv.swap free shared)) hNextLe hNextSub
            (by rw [hNextCard]; exact hCard)
        refine ⟨(Equiv.swap free shared).trans rest, ?_, ?_, ?_⟩
        · intro sheet hSheet
          exact hRestWhole _ (hStepWhole sheet hSheet)
        · intro sheet hSheet
          simp only [Equiv.trans_apply]
          rw [hStepOut sheet hSheet]
          exact hRestOut sheet hSheet
        · have hImage : other.image ((Equiv.swap free shared).trans rest) =
              (other.image (Equiv.swap free shared)).image rest := by
            rw [Finset.image_image]
            rfl
          rw [hImage]
          exact hRestDisjoint

/-- **Inside one wall block, a series of transpositions moves `e₃` off `e₂`.**
If `e₂` and `e₃` sit inside `A₀` and their cardinalities already sum to
`|A₀|`, some permutation of the sheets that preserves `A₀` and fixes every
sheet outside it carries `e₃` onto the complement of `e₂`.  Each transposition
used is a legal DV branch-swap at the wall. -/
theorem exists_perm_image_disjoint (whole small other : Finset (Fin degree))
    (hSmall : small ⊆ whole) (hOther : other ⊆ whole)
    (hCard : small.card + other.card = whole.card) :
    ∃ permutation : Equiv.Perm (Fin degree),
      (∀ sheet ∈ whole, permutation sheet ∈ whole) ∧
        (∀ sheet, sheet ∉ whole → permutation sheet = sheet) ∧
        Disjoint small (other.image permutation) :=
  exists_perm_image_disjoint_aux whole small hSmall (small ∩ other).card other
    le_rfl hOther hCard

/-! ## The two Figure 28 alternatives on one isomorphism class -/

/-- A non-dangling edge class above an incident target edge sits inside the
wall block of any sheet it is related to. -/
theorem block_subset_wallBlock (data : GluingDatum target degree)
    (wall : target.V) (edge : target.edges) (anchor edgeAnchor : Fin degree)
    (hRefines : (data.edgePartition edge).Refines (data.vertexPartition wall))
    (hRel : (data.vertexPartition wall).Rel anchor edgeAnchor) :
    (data.edgePartition edge).block edgeAnchor ⊆
      (data.vertexPartition wall).block anchor := by
  intro sheet hSheet
  exact ((data.vertexPartition wall).mem_block_iff anchor sheet).mpr
    (hRel.trans (hRefines.rel
      (((data.edgePartition edge).mem_block_iff edgeAnchor sheet).mp hSheet)))

/-- **Gauge move A: make `e₂` and `e₃` meet.**  One DV branch-swap on the
branch through `t₃`, by the transposition of the two class anchors, leaves the
wall block and the `t₂` class untouched and drags `e₃` across `e₂`.  This is
Position II.b's requirement, produced from an arbitrary datum of the case. -/
theorem exists_branchGauge_not_disjoint (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall)
    (growTarget otherTarget : target.edges)
    (anchor growAnchor otherAnchor : Fin degree)
    (hGrowRel : (data.vertexPartition wall).Rel anchor growAnchor)
    (hOtherRel : (data.vertexPartition wall).Rel anchor otherAnchor)
    (hGrowFixed : TargetBranchRegion.edgeMoved wall root hRoot growTarget = false)
    (hOtherMoved : TargetBranchRegion.edgeMoved wall root hRoot otherTarget = true) :
    ∃ relabeling : data.SheetRelabeling,
      BranchGauge data wall root hRoot relabeling ∧
        relabeling.apply.edgePartition growTarget = data.edgePartition growTarget ∧
        (data.vertexPartition wall).Rel anchor growAnchor ∧
        (relabeling.apply.edgePartition otherTarget).blockCard growAnchor =
          (data.edgePartition otherTarget).blockCard otherAnchor ∧
        ¬ Disjoint ((relabeling.apply.edgePartition growTarget).block growAnchor)
          ((relabeling.apply.edgePartition otherTarget).block growAnchor) := by
  classical
  have hTogether : (data.vertexPartition wall).Rel growAnchor otherAnchor :=
    hGrowRel.symm.trans hOtherRel
  have hFix : ∀ sheet, (data.vertexPartition wall).Rel
      ((Equiv.swap growAnchor otherAnchor) sheet) sheet :=
    (data.vertexPartition wall).swap_apply_rel_self_of_rel hTogether
  refine ⟨branchSwapOfPerm data wall root hRoot
    (Equiv.swap growAnchor otherAnchor) hFix,
    branchSwapOfPerm_branchGauge data wall root hRoot _ hFix, ?_, hGrowRel, ?_, ?_⟩
  · exact branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot _ hFix
      growTarget hGrowFixed
  · rw [branchSwapOfPerm_edgePartition_of_moved data wall root hRoot _ hFix
      otherTarget hOtherMoved]
    have hSwap : (Equiv.swap growAnchor otherAnchor) otherAnchor = growAnchor :=
      Equiv.swap_apply_right growAnchor otherAnchor
    have hCard := (data.edgePartition otherTarget).relabel_blockCard
      (Equiv.swap growAnchor otherAnchor) otherAnchor
    rw [hSwap] at hCard
    exact hCard
  · rw [branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot _ hFix
      growTarget hGrowFixed,
      branchSwapOfPerm_edgePartition_of_moved data wall root hRoot _ hFix
      otherTarget hOtherMoved]
    refine Finset.not_disjoint_iff.mpr ⟨growAnchor, ?_, ?_⟩
    · exact ((data.edgePartition growTarget).mem_block_iff growAnchor
        growAnchor).mpr rfl
    · have hSwap : (Equiv.swap growAnchor otherAnchor) otherAnchor = growAnchor :=
        Equiv.swap_apply_right growAnchor otherAnchor
      have hBlock := (data.edgePartition otherTarget).relabel_block
        (Equiv.swap growAnchor otherAnchor) otherAnchor
      rw [hSwap] at hBlock
      rw [hBlock]
      exact Finset.mem_image.mpr ⟨otherAnchor,
        ((data.edgePartition otherTarget).mem_block_iff otherAnchor
          otherAnchor).mpr rfl, hSwap⟩

/-- **Gauge move B: make `e₂` and `e₃` tile `A₀`.**  A series of DV
branch-swaps on the branch through `t₃` carries `e₃` into the complement of
`e₂` inside the wall block, using only the case's own index identity
`k₂ + k₃ = |A₀|`.  This is Position I's requirement, produced from an
arbitrary datum of the case. -/
theorem exists_branchGauge_disjoint (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall)
    (growTarget otherTarget : target.edges)
    (anchor growAnchor otherAnchor : Fin degree)
    (hGrowRefines : (data.edgePartition growTarget).Refines
      (data.vertexPartition wall))
    (hOtherRefines : (data.edgePartition otherTarget).Refines
      (data.vertexPartition wall))
    (hGrowRel : (data.vertexPartition wall).Rel anchor growAnchor)
    (hOtherRel : (data.vertexPartition wall).Rel anchor otherAnchor)
    (hIndexSum : (data.edgePartition growTarget).blockCard growAnchor +
        (data.edgePartition otherTarget).blockCard otherAnchor =
      (data.vertexPartition wall).blockCard anchor)
    (hGrowFixed : TargetBranchRegion.edgeMoved wall root hRoot growTarget = false)
    (hOtherMoved : TargetBranchRegion.edgeMoved wall root hRoot otherTarget = true) :
    ∃ (relabeling : data.SheetRelabeling) (newAnchor : Fin degree),
      BranchGauge data wall root hRoot relabeling ∧
        relabeling.apply.edgePartition growTarget = data.edgePartition growTarget ∧
        (data.vertexPartition wall).Rel anchor newAnchor ∧
        (relabeling.apply.edgePartition otherTarget).blockCard newAnchor =
          (data.edgePartition otherTarget).blockCard otherAnchor ∧
        Disjoint ((relabeling.apply.edgePartition growTarget).block growAnchor)
          ((relabeling.apply.edgePartition otherTarget).block newAnchor) := by
  classical
  obtain ⟨permutation, hInside, hOutside, hDisjoint⟩ :=
    exists_perm_image_disjoint ((data.vertexPartition wall).block anchor)
      ((data.edgePartition growTarget).block growAnchor)
      ((data.edgePartition otherTarget).block otherAnchor)
      (block_subset_wallBlock data wall growTarget anchor growAnchor
        hGrowRefines hGrowRel)
      (block_subset_wallBlock data wall otherTarget anchor otherAnchor
        hOtherRefines hOtherRel)
      hIndexSum
  have hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet :=
    rel_of_stabilizes_block (data.vertexPartition wall) anchor permutation
      hInside hOutside
  have hOtherMem : otherAnchor ∈ (data.vertexPartition wall).block anchor :=
    ((data.vertexPartition wall).mem_block_iff anchor otherAnchor).mpr hOtherRel
  refine ⟨branchSwapOfPerm data wall root hRoot permutation hFix,
    permutation otherAnchor,
    branchSwapOfPerm_branchGauge data wall root hRoot permutation hFix, ?_, ?_, ?_, ?_⟩
  · exact branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot permutation
      hFix growTarget hGrowFixed
  · exact ((data.vertexPartition wall).mem_block_iff anchor _).mp
      (hInside otherAnchor hOtherMem)
  · rw [branchSwapOfPerm_edgePartition_of_moved data wall root hRoot permutation
      hFix otherTarget hOtherMoved]
    exact (data.edgePartition otherTarget).relabel_blockCard permutation otherAnchor
  · rw [branchSwapOfPerm_edgePartition_of_fixed data wall root hRoot permutation
      hFix growTarget hGrowFixed,
      branchSwapOfPerm_edgePartition_of_moved data wall root hRoot permutation
      hFix otherTarget hOtherMoved,
      (data.edgePartition otherTarget).relabel_block permutation otherAnchor]
    exact hDisjoint

/-- **The verdict.**  On one and the same wall datum of case
`{w3-r1-nd3-t2-(a=k₄)}`, branch-swaps along the branch through `t₃`
produce both Figure 28 alternatives: a representative where the two smaller
classes tile the wall block, as Position I demands, and one where they
overlap, as Position II.b demands.  Every swap keeps `A₀` and `e₂` as literal
terms, keeps `e₃`'s index, and preserves `targetExcess wall`, validity,
dangling-no-glue and the stable-row count (`BranchGauge`); on the
full-dimensional side it preserves the whole length matrix
(`fullDimensional_gauge`).

Reading the swap as a gluing-datum isomorphism in the sense of Part I
(`definition-gd-iso`), which this Lean statement does not itself assert,
`Disjoint e₂ e₃` is therefore not a property of the isomorphism class of the
limit, so no global hypothesis on the limit can decide it.  Since `ℙ𝒞*(M₀)` is
by definition (Part I, Section 6) a set of isomorphism classes of data
contracting to a limit *isomorphic to* `M₀`, and compatibility of labellings at
`t₁` (Part I, Section 5) is stated through an isomorphism of the two
limits rather than their equality, Positions I and II.b are both available
over one class.  Figure 28's four-member family is then not excluded by the
dichotomy of
`W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`. -/
theorem disjointness_not_gauge_invariant (data : GluingDatum target degree)
    (wall root : target.V) (hRoot : root ≠ wall)
    (growTarget otherTarget : target.edges)
    (anchor growAnchor otherAnchor : Fin degree)
    (hGrowRefines : (data.edgePartition growTarget).Refines
      (data.vertexPartition wall))
    (hOtherRefines : (data.edgePartition otherTarget).Refines
      (data.vertexPartition wall))
    (hGrowRel : (data.vertexPartition wall).Rel anchor growAnchor)
    (hOtherRel : (data.vertexPartition wall).Rel anchor otherAnchor)
    (hIndexSum : (data.edgePartition growTarget).blockCard growAnchor +
        (data.edgePartition otherTarget).blockCard otherAnchor =
      (data.vertexPartition wall).blockCard anchor)
    (hGrowFixed : TargetBranchRegion.edgeMoved wall root hRoot growTarget = false)
    (hOtherMoved : TargetBranchRegion.edgeMoved wall root hRoot otherTarget = true) :
    (∃ (relabeling : data.SheetRelabeling) (newAnchor : Fin degree),
        BranchGauge data wall root hRoot relabeling ∧
          relabeling.apply.edgePartition growTarget = data.edgePartition growTarget ∧
          (data.vertexPartition wall).Rel anchor newAnchor ∧
          (relabeling.apply.edgePartition otherTarget).blockCard newAnchor =
            (data.edgePartition otherTarget).blockCard otherAnchor ∧
          Disjoint ((relabeling.apply.edgePartition growTarget).block growAnchor)
            ((relabeling.apply.edgePartition otherTarget).block newAnchor)) ∧
      ∃ (relabeling : data.SheetRelabeling) (newAnchor : Fin degree),
        BranchGauge data wall root hRoot relabeling ∧
          relabeling.apply.edgePartition growTarget = data.edgePartition growTarget ∧
          (data.vertexPartition wall).Rel anchor newAnchor ∧
          (relabeling.apply.edgePartition otherTarget).blockCard newAnchor =
            (data.edgePartition otherTarget).blockCard otherAnchor ∧
          ¬ Disjoint ((relabeling.apply.edgePartition growTarget).block growAnchor)
            ((relabeling.apply.edgePartition otherTarget).block newAnchor) := by
  refine ⟨exists_branchGauge_disjoint data wall root hRoot growTarget otherTarget
      anchor growAnchor otherAnchor hGrowRefines hOtherRefines hGrowRel hOtherRel
      hIndexSum hGrowFixed hOtherMoved, ?_⟩
  obtain ⟨relabeling, hGauge, hGrow, hRel, hCard, hMeet⟩ :=
    exists_branchGauge_not_disjoint data wall root hRoot growTarget otherTarget
      anchor growAnchor otherAnchor hGrowRel hOtherRel hGrowFixed hOtherMoved
  exact ⟨relabeling, growAnchor, hGauge, hGrow, hRel, hCard, hMeet⟩

end DraismaVargas.LocalCases.W3FourDisjointness
