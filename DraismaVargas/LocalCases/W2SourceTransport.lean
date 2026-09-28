import DraismaVargas.LocalCases.W2M1kSwapped
import DraismaVargas.LocalCases.SheetRelabelStable

/-!
# Transporting a W2 source input and its occurrence profile along a sheet relabelling

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}` and Figure 33; the
Base I/II vocabulary of the divalent wall is defined once for the whole
section, in case `{w2-r2}`.  Part I compares gluing data up to isomorphism, so
the members of one family may legitimately live over different representatives
of a single isomorphism class; this file uses that freedom.

## What this file proves

`W2M1kSwapped.nonempty_swappedBundle_iff_aligned` shows the swapped Figure 33
bundle exists over a given `w2M1k` datum **exactly when** the two wall
directions pin the same sheet, and `W2M1kSwapped.exists_aligned_gauge` shows
that condition is a *gauge* condition: every profile has a branch-swapped datum,
valid whenever the original is, on which both directions isolate one sheet.
Between the two one needs a `SecondEquation.W2SourceInput` and a
`W2R2SourceProfile.SourceProfile` **on that swapped datum**; this file supplies
them, and `exists_gauge_swappedBundle` is the unconditional instantiation of
the swapped Figure 33 bundle.

## The transport is general

Everything below is stated for an **arbitrary** `GluingDatum.SheetRelabeling`,
not only for a branch swap.  Nothing in the W2 input or in the W2-r2 occurrence
profile is sensitive to *which* region is relabelled:

* `input_relabel` transports all five fields of `SecondEquation.W2SourceInput`.
  Four of them are already available in the general form --
  `GluingDatum.SheetRelabeling.valid`, `SheetRelabelStable.stablePathEquiv`,
  `SheetRelabelStable.danglingEdgeNoGlue_map` and
  `SheetRelabelStable.nonDanglingValency_map`.  The fifth, `equation_c`, needed
  the general excess invariance, proved here as `targetExcess_relabel`; it
  strengthens `W3FourDisjointness.BranchGauge`'s `targetExcess` field from one
  branch swap at one wall to any relabelling at any target vertex, and rests on
  `SheetPartition.relabel_blockCard` together with
  `SheetPartition.relabel_blockCountWithin_of_relative_pointwise` applied
  through the relabelling's own `compatible_left` / `compatible_right`.
* `sourceProfile_relabel` transports every field of
  `W2R2SourceProfile.SourceProfile`: the three survivors and the unique dangling
  occurrence travel by `sourceEdgeEquiv`, which keeps each one's *target
  direction* (`incidentEquiv_target`, a `rfl`) and its *source index*
  (`SheetRelabelStable.sourceEdgeIndex_map`), so the two labels, the fibre
  identities, exhaustiveness and the M/P case disjunction all come across
  unchanged.  `shape_relabel` does the same for the M-1k refinement
  `W2M1kSourceCandidates.Shape`.

**No field needed a hypothesis the case does not supply.**  The only hypothesis
used anywhere beyond the relabelling itself is `data.Connected`, which every
`W2SourceInput` already carries in `valid`, and -- in the M-1k application
alone, never in the transport -- `graph_connected target` and
`genus target = 0`, which `W2M1kSwapped.separated` already consumes.

`W3ShiftClosure.branchSwapInput` / `branchSwapProfile` are the W3 analogues and
were followed field for field; the difference is that they are stated for
`W3FourDisjointness.branchSwapOfPerm` and read the wall permutation off as the
identity, whereas here the wall permutation is arbitrary and is carried by
`wallBlockEquiv`.

## Why the relabelling is exposed rather than an existential datum

`W3ShiftShrinkExistence.exists_branchGauge_shrinkSheet` could not be used as a
black box because its conclusion produced an anonymous `GluingDatum` about which
nothing further could be said.  Every statement below instead names an explicit
`data.SheetRelabeling`, so `relabeling.apply` is a term the caller can go on
carrying facts onto, and `exists_gauge_swappedBundle` returns that relabelling
together with the transported input, profile and shape.

## Where these lemmas would belong

Only `blockCountWithin_relabel` could move to `Infrastructure.GluingRelabel`:
it mentions just `SheetRelabeling`, `GluingDatum.incidentEdges` and
`SheetPartition.relabel_blockCountWithin_of_relative_pointwise`.

The other five -- `wallBlockEquiv`, `sourceVertex_relabel`,
`localRamification_relabel`, `targetChange_relabel`, `targetExcess_relabel` --
**cannot** go there.  `GluingRelabel` reaches neither `Infrastructure.Change`,
where `localRamification`, `targetChange` and `targetExcess` are defined, nor
`LocalCases.W4Assembly` / `LocalCases.W4StableSource`, where `WallBlock` and
`nonDanglingValency` are -- and it must not reach the latter, since
`Infrastructure` importing `LocalCases` would invert the library's layering.

Their natural home, and `incidentEquiv`'s with its four `rfl`-level
companions, is `SheetRelabelStable`, beside `nonDanglingValency_map`, which
reaches all five of `Infrastructure.Change`, `LocalCases.W4Assembly`,
`LocalCases.W4StableSource`, `Infrastructure.GluingRelabel` and
`LocalCases.SheetRelabelPruning`.  There,
`W3FourDisjointness.BranchGauge.targetExcess` would be a corollary of
`targetExcess_relabel` and `W3ShiftClosure.branchSwapIncident` a special case
of `incidentEquiv`.

## What is not proved here

Equation (7) on actual matrices, the honest stable presentations, the common
retained columns and the stable-graph incidence transport for M-1k: those are
in `W2M1kCommonBalance`, `W2M1kLimitColumns` and `W2M1kStableIncidence`.
-/

namespace DraismaVargas.LocalCases.W2SourceTransport

open DraismaVargas.Infrastructure
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open W2R2SourceProfile W2M1kSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

/-! ## Wall blocks travel by the relabelling's own vertex permutation -/

/-- The blocks above a target vertex are permuted by the relabelling's
permutation there.  This is the piece `W3ShiftClosure` did not need: its branch
swap is the identity at the wall, so its `hVal` could read `swappedBlock.1 =
block.1`. -/
def wallBlockEquiv (relabeling : data.SheetRelabeling) (vertex : target.V) :
    WallBlock data vertex ≃ WallBlock relabeling.apply vertex where
  toFun block := ⟨relabeling.vertexPermutation vertex block.1, by
    show relabeling.vertexPermutation vertex
        ((data.vertexPartition vertex).repr
          ((relabeling.vertexPermutation vertex).symm
            (relabeling.vertexPermutation vertex block.1))) = _
    rw [Equiv.symm_apply_apply, block.2]⟩
  invFun block := ⟨(relabeling.vertexPermutation vertex).symm block.1, by
    have hBlock : relabeling.vertexPermutation vertex
        ((data.vertexPartition vertex).repr
          ((relabeling.vertexPermutation vertex).symm block.1)) = block.1 := block.2
    exact (relabeling.vertexPermutation vertex).eq_symm_apply.mpr hBlock⟩
  left_inv := fun _ ↦ Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv := fun _ ↦ Subtype.ext (Equiv.apply_symm_apply _ _)

@[simp] theorem wallBlockEquiv_val (relabeling : data.SheetRelabeling)
    (vertex : target.V) (block : WallBlock data vertex) :
    (wallBlockEquiv relabeling vertex block).1 =
      relabeling.vertexPermutation vertex block.1 := rfl

theorem wallBlockEquiv_symm_val (relabeling : data.SheetRelabeling)
    (vertex : target.V) (block : WallBlock relabeling.apply vertex) :
    ((wallBlockEquiv relabeling vertex).symm block).1 =
      (relabeling.vertexPermutation vertex).symm block.1 := rfl

/-- A wall block of the relabelled datum names the relabelled image of the
corresponding source vertex. -/
theorem sourceVertex_relabel (relabeling : data.SheetRelabeling) (vertex : target.V)
    (block : WallBlock data vertex) (swapped : WallBlock relabeling.apply vertex)
    (hVal : swapped.1 = relabeling.vertexPermutation vertex block.1) :
    WallBlock.sourceVertex relabeling.apply vertex swapped =
      relabeling.sourceVertexEquiv (WallBlock.sourceVertex data vertex block) := by
  unfold WallBlock.sourceVertex
  rw [SheetRelabelPruning.sourceVertexEquiv_sourceEndpoint, hVal]

/-- The size of a wall block is a relabelling invariant. -/
theorem blockCard_relabel (relabeling : data.SheetRelabeling) (vertex : target.V)
    (block : WallBlock data vertex) (swapped : WallBlock relabeling.apply vertex)
    (hVal : swapped.1 = relabeling.vertexPermutation vertex block.1) :
    (relabeling.apply.vertexPartition vertex).blockCard swapped.1 =
      (data.vertexPartition vertex).blockCard block.1 := by
  rw [hVal]
  exact (data.vertexPartition vertex).relabel_blockCard
    (relabeling.vertexPermutation vertex) block.1

/-- The induced block count of an incident occurrence partition inside a wall
block is a relabelling invariant: the relative permutation stays inside every
block of the endpoint partition, which is exactly `compatible_left` /
`compatible_right`. -/
theorem blockCountWithin_relabel (relabeling : data.SheetRelabeling)
    (vertex : target.V) (edge : target.edges)
    (hIncident : edge ∈ GluingDatum.incidentEdges vertex) (sheet : Fin degree) :
    (relabeling.apply.edgePartition edge).blockCountWithin
        (relabeling.apply.vertexPartition vertex)
        (relabeling.vertexPermutation vertex sheet) =
      (data.edgePartition edge).blockCountWithin (data.vertexPartition vertex) sheet := by
  have hEnds : (edge : target.V × target.V).1 = vertex ∨
      (edge : target.V × target.V).2 = vertex := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hIncident
  rcases hEnds with hLeft | hRight
  · subst hLeft
    exact SheetPartition.relabel_blockCountWithin_of_relative_pointwise
      (data.edgePartition edge) (data.vertexPartition (edge : target.V × target.V).1)
      (relabeling.edgePermutation edge)
      (relabeling.vertexPermutation (edge : target.V × target.V).1)
      (relabeling.compatible_left edge) sheet
  · subst hRight
    exact SheetPartition.relabel_blockCountWithin_of_relative_pointwise
      (data.edgePartition edge) (data.vertexPartition (edge : target.V × target.V).2)
      (relabeling.edgePermutation edge)
      (relabeling.vertexPermutation (edge : target.V × target.V).2)
      (relabeling.compatible_right edge) sheet

/-- Local ramification is a relabelling invariant. -/
theorem localRamification_relabel (relabeling : data.SheetRelabeling)
    (vertex : target.V) (block : WallBlock data vertex)
    (swapped : WallBlock relabeling.apply vertex)
    (hVal : swapped.1 = relabeling.vertexPermutation vertex block.1) :
    relabeling.apply.localRamification vertex swapped =
      data.localRamification vertex block := by
  unfold GluingDatum.localRamification
  rw [blockCard_relabel relabeling vertex block swapped hVal, hVal,
    Finset.sum_congr rfl (fun edge hEdge ↦ by
      rw [blockCountWithin_relabel relabeling vertex edge hEdge block.1])]

/-- **The change at a target vertex is a relabelling invariant.**  The general
form of `W3FourDisjointness.BranchGauge`'s `targetExcess` field. -/
theorem targetChange_relabel (relabeling : data.SheetRelabeling) (vertex : target.V) :
    relabeling.apply.targetChange vertex = data.targetChange vertex := by
  unfold GluingDatum.targetChange
  refine (Fintype.sum_equiv (wallBlockEquiv relabeling vertex)
    (fun block ↦ data.localRamification vertex block)
    (fun block ↦ relabeling.apply.localRamification vertex block) ?_).symm
  intro block
  exact (localRamification_relabel relabeling vertex block _ rfl).symm

/-- **Equation (C)'s excess is a relabelling invariant**, at every target vertex
and for every compatible sheet relabelling. -/
theorem targetExcess_relabel (relabeling : data.SheetRelabeling) (vertex : target.V) :
    relabeling.apply.targetExcess vertex = data.targetExcess vertex := by
  unfold GluingDatum.targetExcess
  rw [targetChange_relabel relabeling vertex]

/-- Surviving valency at a wall block is a relabelling invariant. -/
theorem nonDanglingValency_relabel (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (vertex : target.V) (block : WallBlock data vertex)
    (swapped : WallBlock relabeling.apply vertex)
    (hVal : swapped.1 = relabeling.vertexPermutation vertex block.1) :
    nonDanglingValency relabeling.apply
        (WallBlock.sourceVertex relabeling.apply vertex swapped) =
      nonDanglingValency data (WallBlock.sourceVertex data vertex block) := by
  rw [sourceVertex_relabel relabeling vertex block swapped hVal,
    SheetRelabelStable.nonDanglingValency_map relabeling hConnected]

/-! ## The occurrences at a wall block travel by `sourceEdgeEquiv` -/

/-- Incident source occurrences at a wall block transport across an arbitrary
sheet relabelling.  The W2 analogue of `W3ShiftClosure.branchSwapIncident`. -/
noncomputable def incidentEquiv (relabeling : data.SheetRelabeling)
    (vertex : target.V) (block : WallBlock data vertex)
    (swapped : WallBlock relabeling.apply vertex)
    (hVal : swapped.1 = relabeling.vertexPermutation vertex block.1) :
    IncidentSourceEdge data (WallBlock.sourceVertex data vertex block) ≃
      IncidentSourceEdge relabeling.apply
        (WallBlock.sourceVertex relabeling.apply vertex swapped) :=
  relabeling.sourceEdgeEquiv.subtypeEquiv fun edge ↦ by
    rw [sourceVertex_relabel relabeling vertex block swapped hVal]
    exact (SheetRelabelPruning.incident_sourceEdgeEquiv_iff relabeling edge _).symm

section Incident

variable (relabeling : data.SheetRelabeling) (vertex : target.V)
  (block : WallBlock data vertex) (swapped : WallBlock relabeling.apply vertex)
  (hVal : swapped.1 = relabeling.vertexPermutation vertex block.1)

theorem incidentEquiv_val
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data vertex block)) :
    (incidentEquiv relabeling vertex block swapped hVal edge).1 =
      relabeling.sourceEdgeEquiv edge.1 := rfl

/-- The transported occurrence lies above the same target direction. -/
theorem incidentEquiv_target
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data vertex block)) :
    (incidentEquiv relabeling vertex block swapped hVal edge).1.1.1 = edge.1.1.1 := rfl

/-- The transported occurrence keeps its source index. -/
theorem incidentEquiv_index
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data vertex block)) :
    relabeling.apply.sourceEdgeIndex
        (incidentEquiv relabeling vertex block swapped hVal edge).1 =
      data.sourceEdgeIndex edge.1 :=
  SheetRelabelStable.sourceEdgeIndex_map relabeling edge.1

/-- Pruning is preserved in both directions. -/
theorem incidentEquiv_isDangling_iff (hConnected : data.Connected)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data vertex block)) :
    IsDangling relabeling.apply
        (incidentEquiv relabeling vertex block swapped hVal edge).1 ↔
      IsDangling data edge.1 :=
  SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff relabeling hConnected edge.1

end Incident

section Fibres

variable {relabeling : data.SheetRelabeling} {block : WallBlock data wall}
  {swapped : WallBlock relabeling.apply wall}

/-- Surviving fibres transport: same direction, pruning preserved. -/
theorem survivingFibre_relabel (star : TwoStar target wall)
    (hConnected : data.Connected)
    (hVal : swapped.1 = relabeling.vertexPermutation wall block.1) (label : Fin 2) :
    survivingFibre relabeling.apply star swapped label =
      (survivingFibre data star block label).image
        (incidentEquiv relabeling wall block swapped hVal) := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨pre, rfl⟩ :=
      (incidentEquiv relabeling wall block swapped hVal).surjective edge
    refine Finset.mem_image.mpr ⟨pre, ?_, rfl⟩
    rw [survivingFibre.mem] at hEdge ⊢
    exact ⟨hEdge.1, fun hDangling ↦ hEdge.2
      ((incidentEquiv_isDangling_iff relabeling wall block swapped hVal
        hConnected pre).mpr hDangling)⟩
  · intro hEdge
    obtain ⟨pre, hPre, rfl⟩ := Finset.mem_image.mp hEdge
    rw [survivingFibre.mem] at hPre ⊢
    exact ⟨hPre.1, fun hDangling ↦ hPre.2
      ((incidentEquiv_isDangling_iff relabeling wall block swapped hVal
        hConnected pre).mp hDangling)⟩

/-- The unique dangling occurrence transports, with its index and its
uniqueness. -/
noncomputable def deletedOccurrence_relabel (hConnected : data.Connected)
    (hVal : swapped.1 = relabeling.vertexPermutation wall block.1)
    (deleted : DeletedOccurrence data block) :
    DeletedOccurrence relabeling.apply swapped where
  edge := incidentEquiv relabeling wall block swapped hVal deleted.edge
  dangling := (incidentEquiv_isDangling_iff relabeling wall block swapped hVal
    hConnected deleted.edge).mpr deleted.dangling
  index_one := by
    rw [incidentEquiv_index relabeling wall block swapped hVal]
    exact deleted.index_one
  unique := by
    intro other
    obtain ⟨pre, rfl⟩ :=
      (incidentEquiv relabeling wall block swapped hVal).surjective other
    constructor
    · intro hDangling
      exact congrArg _ ((deleted.unique pre).mp
        ((incidentEquiv_isDangling_iff relabeling wall block swapped hVal hConnected
          pre).mp hDangling))
    · intro hEq
      exact (incidentEquiv_isDangling_iff relabeling wall block swapped hVal hConnected
        pre).mpr ((deleted.unique pre).mpr
          ((incidentEquiv relabeling wall block swapped hVal).injective hEq))

@[simp] theorem deletedOccurrence_relabel_edge (hConnected : data.Connected)
    (hVal : swapped.1 = relabeling.vertexPermutation wall block.1)
    (deleted : DeletedOccurrence data block) :
    (deletedOccurrence_relabel hConnected hVal deleted).edge =
      incidentEquiv relabeling wall block swapped hVal deleted.edge := rfl

end Fibres

/-! ## The two structures the M-1k bundle needs -/

/-- **`SecondEquation.W2SourceInput` transports along an arbitrary compatible
sheet relabelling.**  The W2 analogue of `W3ShiftClosure.branchSwapInput`, and
general where that one is a branch swap: `valid` from
`GluingDatum.SheetRelabeling.valid`, `stablePath_card` from
`SheetRelabelStable.stablePathEquiv`, `dangling_no_glue` from
`SheetRelabelStable.danglingEdgeNoGlue_map`, `nonDangling_valency` from
`SheetRelabelStable.nonDanglingValency_map` through `wallBlockEquiv`, and
`equation_c` from `targetExcess_relabel`.  No field needs a hypothesis the case
does not already supply. -/
theorem input_relabel (input : W2SourceInput data star)
    (relabeling : data.SheetRelabeling) : W2SourceInput relabeling.apply star := by
  refine { valid := relabeling.valid input.valid
           stablePath_card := ?_
           dangling_no_glue := SheetRelabelStable.danglingEdgeNoGlue_map relabeling
             input.valid.1 input.dangling_no_glue
           nonDangling_valency := ?_
           equation_c := by
             rw [targetExcess_relabel relabeling wall]; exact input.equation_c }
  · exact (Fintype.card_congr
      (SheetRelabelStable.stablePathEquiv relabeling input.valid.1)).symm.trans
      input.stablePath_card
  · intro sourceBlock
    rw [nonDanglingValency_relabel relabeling input.valid.1 wall
      ((wallBlockEquiv relabeling wall).symm sourceBlock) sourceBlock
      ((relabeling.vertexPermutation wall).apply_symm_apply sourceBlock.1).symm]
    exact input.nonDangling_valency _

/-- **`W2R2SourceProfile.SourceProfile` transports along an arbitrary compatible
sheet relabelling.**  The W2 analogue of `W3ShiftClosure.branchSwapProfile`: the
three survivors and the unique dangling occurrence go across by
`sourceEdgeEquiv`, which keeps each one's target direction and its source index,
so both labels, both fibre identities, exhaustiveness and the M/P case
disjunction survive verbatim. -/
noncomputable def sourceProfile_relabel {block : WallBlock data wall}
    (profile : SourceProfile data star block) (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) (swapped : WallBlock relabeling.apply wall)
    (hVal : swapped.1 = relabeling.vertexPermutation wall block.1) :
    SourceProfile relabeling.apply star swapped where
  ramification := by
    rw [localRamification_relabel relabeling wall block swapped hVal]
    exact profile.ramification
  valency := by
    rw [nonDanglingValency_relabel relabeling hConnected wall block swapped hVal]
    exact profile.valency
  doubleLabel := profile.doubleLabel
  singleLabel := profile.singleLabel
  labels_ne := profile.labels_ne
  first := incidentEquiv relabeling wall block swapped hVal profile.first
  second := incidentEquiv relabeling wall block swapped hVal profile.second
  third := incidentEquiv relabeling wall block swapped hVal profile.third
  deleted := deletedOccurrence_relabel hConnected hVal profile.deleted
  first_ne_second := fun hEq ↦ profile.first_ne_second
    ((incidentEquiv relabeling wall block swapped hVal).injective hEq)
  first_target := profile.first_target
  second_target := profile.second_target
  third_target := profile.third_target
  first_survives := fun hDangling ↦ profile.first_survives
    ((incidentEquiv_isDangling_iff relabeling wall block swapped hVal hConnected
      profile.first).mp hDangling)
  second_survives := fun hDangling ↦ profile.second_survives
    ((incidentEquiv_isDangling_iff relabeling wall block swapped hVal hConnected
      profile.second).mp hDangling)
  third_survives := fun hDangling ↦ profile.third_survives
    ((incidentEquiv_isDangling_iff relabeling wall block swapped hVal hConnected
      profile.third).mp hDangling)
  double_fibre := by
    rw [survivingFibre_relabel star hConnected hVal, profile.double_fibre]
    simp only [Finset.image_insert, Finset.image_singleton]
  single_fibre := by
    rw [survivingFibre_relabel star hConnected hVal, profile.single_fibre]
    simp only [Finset.image_singleton]
  exhaustive := by
    intro edge
    obtain ⟨pre, rfl⟩ :=
      (incidentEquiv relabeling wall block swapped hVal).surjective edge
    rcases profile.exhaustive pre with hEq | hEq | hEq | hEq <;>
      [exact Or.inl (congrArg _ hEq);
        exact Or.inr (Or.inl (congrArg _ hEq));
        exact Or.inr (Or.inr (Or.inl (congrArg _ hEq)));
        exact Or.inr (Or.inr (Or.inr (congrArg _ hEq)))]
  cases := by
    rw [incidentEquiv_index relabeling wall block swapped hVal,
      incidentEquiv_index relabeling wall block swapped hVal,
      incidentEquiv_index relabeling wall block swapped hVal,
      blockCard_relabel relabeling wall block swapped hVal]
    exact profile.cases

/-- The M-1k refinement of the profile transports too: `k`, the block size, the
Cardinality M placement of the dangling occurrence and `k₁ = 1` are all read off
transported data. -/
noncomputable def shape_relabel {block : WallBlock data wall}
    {profile : SourceProfile data star block} (shape : Shape profile)
    (relabeling : data.SheetRelabeling) (hConnected : data.Connected)
    (swapped : WallBlock relabeling.apply wall)
    (hVal : swapped.1 = relabeling.vertexPermutation wall block.1) :
    Shape (sourceProfile_relabel profile relabeling hConnected swapped hVal) where
  k := shape.k
  one_lt_k := shape.one_lt_k
  blockCard := by
    rw [blockCard_relabel relabeling wall block swapped hVal]
    exact shape.blockCard
  deleted_single := shape.deleted_single
  unit_index := by
    show relabeling.apply.sourceEdgeIndex
      (incidentEquiv relabeling wall block swapped hVal profile.first).1 = 1
    rw [incidentEquiv_index relabeling wall block swapped hVal]
    exact shape.unit_index

@[simp] theorem shape_relabel_k {block : WallBlock data wall}
    {profile : SourceProfile data star block} (shape : Shape profile)
    (relabeling : data.SheetRelabeling) (hConnected : data.Connected)
    (swapped : WallBlock relabeling.apply wall)
    (hVal : swapped.1 = relabeling.vertexPermutation wall block.1) :
    (shape_relabel shape relabeling hConnected swapped hVal).k = shape.k := rfl

/-! ## The M-1k bundle at an arbitrary profile

The gauge move is `W2M1kSwapped.exists_aligned_gauge`'s own: the branch swap
across the `t₃` branch transposing the two pinned sheets.  Its wall permutation
is the identity, so the wall block, the wall partition and the alignment
statement are all literal. -/

/-- The branch swap is the identity at the wall: `TargetBranchRegion` never puts
the wall in the moved branch.  (`W3ShiftClosure.branchSwap_vertexPermutation_wall`
is the same fact for `W3FourDisjointness.branchSwapOfPerm`; this is the
`ResolutionM11.wallBranchSwap` form, which would sit naturally in
`ResolutionM11`.) -/
theorem wallBranchSwap_vertexPermutation_wall_local (root : target.V)
    (hRoot : root ≠ wall) (first second : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel first second) :
    (ResolutionM11.wallBranchSwap data wall root hRoot first second
        hTogether).vertexPermutation wall = Equiv.refl _ := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall root hRoot wall) (Equiv.swap first second) = _
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

/-- Hence the wall partition itself is unchanged as a term. -/
theorem wallBranchSwap_vertexPartition_wall_local (root : target.V)
    (hRoot : root ≠ wall) (first second : Fin degree)
    (hTogether : (data.vertexPartition wall).Rel first second) :
    (ResolutionM11.wallBranchSwap data wall root hRoot first second
        hTogether).apply.vertexPartition wall = data.vertexPartition wall := by
  change (data.vertexPartition wall).relabel
    ((ResolutionM11.wallBranchSwap data wall root hRoot first second
      hTogether).vertexPermutation wall) = _
  rw [wallBranchSwap_vertexPermutation_wall_local root hRoot first second hTogether]
  cases hPartition : data.vertexPartition wall
  rfl

/-- The two pinned sheets lie in one wall block, so their transposition is a
legal branch swap. -/
theorem alignedTogether {block : WallBlock data wall}
    (profile : SourceProfile data star block) :
    (data.vertexPartition wall).Rel (pinSheet profile 0) (pinSheet profile 1) :=
  (pinSheet_rel (profile := profile) 0).symm.trans
    (pinSheet_rel (profile := profile) 1)

/-- The gauge move of `W2M1kSwapped.exists_aligned_gauge`, as an explicit
`GluingDatum.SheetRelabeling` rather than an anonymous datum: the branch swap
across the `t₃` branch which transposes the two pinned sheets. -/
noncomputable def alignedRelabeling {block : WallBlock data wall}
    (profile : SourceProfile data star block) : data.SheetRelabeling :=
  ResolutionM11.wallBranchSwap data wall (M11RemoteCandidates.branchRoot star 1)
    (M11RemoteCandidates.branchRoot_ne star 1)
    (pinSheet profile 0) (pinSheet profile 1) (alignedTogether profile)

/-- The gauge move is the identity at the wall. -/
theorem alignedRelabeling_vertexPermutation_wall {block : WallBlock data wall}
    (profile : SourceProfile data star block) :
    (alignedRelabeling profile).vertexPermutation wall = Equiv.refl _ :=
  wallBranchSwap_vertexPermutation_wall_local _ _ _ _ _

/-- Hence it leaves the wall partition literally alone. -/
theorem alignedRelabeling_vertexPartition_wall {block : WallBlock data wall}
    (profile : SourceProfile data star block) :
    (alignedRelabeling profile).apply.vertexPartition wall =
      data.vertexPartition wall :=
  wallBranchSwap_vertexPartition_wall_local _ _ _ _ _

/-- The gauge copy of the distinguished wall block: the same block, since the
swap is the identity at the wall. -/
noncomputable def alignedBlock {block : WallBlock data wall}
    (profile : SourceProfile data star block) :
    WallBlock (alignedRelabeling profile).apply wall :=
  (wallBlockEquiv (alignedRelabeling profile) wall) block

theorem alignedBlock_val {block : WallBlock data wall}
    (profile : SourceProfile data star block) :
    (alignedBlock profile).1 = block.1 := by
  show (alignedRelabeling profile).vertexPermutation wall block.1 = block.1
  rw [alignedRelabeling_vertexPermutation_wall]
  rfl

/-- The transported W2 source input on the gauge copy. -/
theorem alignedInput {block : WallBlock data wall}
    (input : W2SourceInput data star) (profile : SourceProfile data star block) :
    W2SourceInput (alignedRelabeling profile).apply star :=
  input_relabel input (alignedRelabeling profile)

/-- The transported occurrence profile on the gauge copy. -/
noncomputable def alignedProfile {block : WallBlock data wall}
    (profile : SourceProfile data star block) (hConnected : data.Connected) :
    SourceProfile (alignedRelabeling profile).apply star (alignedBlock profile) :=
  sourceProfile_relabel profile (alignedRelabeling profile) hConnected
    (alignedBlock profile) rfl

/-- The transported M-1k shape on the gauge copy. -/
noncomputable def alignedShape {block : WallBlock data wall}
    {profile : SourceProfile data star block} (shape : Shape profile)
    (hConnected : data.Connected) : Shape (alignedProfile profile hConnected) :=
  shape_relabel shape (alignedRelabeling profile) hConnected
    (alignedBlock profile) rfl

/-- **The gauge copy is aligned.**  Both wall directions of the swapped datum
isolate the original's first pinned sheet
(`W2M1kSwapped.branchSwap_aligns_of_genus_zero`), and on an M-1k block the only
sheet a direction isolates is its own pinned sheet
(`W2M1kSourceCandidates.eq_pinSheet_of_block_singleton`).  So both pinned sheets
of the transported profile equal that one sheet. -/
theorem alignedProfile_aligned {block : WallBlock data wall}
    {profile : SourceProfile data star block} (shape : Shape profile)
    (hConnected : data.Connected) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    pinSheet (alignedProfile profile hConnected) 0 =
      pinSheet (alignedProfile profile hConnected) 1 := by
  have hRel : ((alignedRelabeling profile).apply.vertexPartition wall).Rel
      (alignedBlock profile).1 (pinSheet profile 0) := by
    rw [alignedBlock_val, alignedRelabeling_vertexPartition_wall]
    exact pinSheet_rel (profile := profile) 0
  have hSingleton : ∀ label : Fin 2,
      ((alignedRelabeling profile).apply.edgePartition (star.edge label)).block
          (pinSheet profile 0) = {pinSheet profile 0} := fun label ↦
    W2M1kSwapped.branchSwap_aligns_of_genus_zero shape hTargetConnected hGenus label
  have hZero := eq_pinSheet_of_block_singleton (alignedShape shape hConnected) 0
    (pinSheet profile 0) hRel (hSingleton 0)
  have hOne := eq_pinSheet_of_block_singleton (alignedShape shape hConnected) 1
    (pinSheet profile 0) hRel (hSingleton 1)
  exact hZero.symm.trans hOne

/-- **The swapped Figure 33 bundle, unconditionally.**  For an *arbitrary* `w2M1k` source profile on a
connected genus-zero target -- aligned or not -- there is an explicit gauge
relabelling of the datum carrying a transported `W2SourceInput`, a transported
`W2R2SourceProfile.SourceProfile` on the same wall block, a transported M-1k
`Shape` with the same `k`, and over that copy all three Figure 33 members, so
`W2M1kSwapped.SwappedBundle` is inhabited and every member is valid whenever the
gauge copy is -- which it is whenever the original datum is, since a sheet
relabelling preserves validity.

Compare `W2M1kSwapped.nonempty_swappedBundle`, which needs `pinSheet profile 0 =
pinSheet profile 1` as a hypothesis, and
`W2M1kSwapped.nonempty_swappedBundle_iff_aligned`, which shows no such bundle
exists over a non-aligned datum.  The price is that the bundle lives over a
different representative of the same isomorphism class of gluing data. -/
theorem exists_gauge_swappedBundle {block : WallBlock data wall}
    (input : W2SourceInput data star) {profile : SourceProfile data star block}
    (shape : Shape profile) (hTargetConnected : graph_connected target)
    (hGenus : genus target = 0) :
    ∃ (relabeling : data.SheetRelabeling)
      (swappedBlock : WallBlock relabeling.apply wall)
      (swappedProfile : SourceProfile relabeling.apply star swappedBlock)
      (swappedShape : Shape swappedProfile),
      W2SourceInput relabeling.apply star ∧
      swappedBlock.1 = block.1 ∧ swappedShape.k = shape.k ∧
      ∃ geometry : GlobalM1k.Geometry relabeling.apply wall,
        (relabeling.apply.vertexPartition wall).Rel swappedBlock.1 geometry.first ∧
          geometry.k = shape.k ∧
          ∃ bundle : W2M1kSwapped.SwappedBundle geometry,
            ∀ index, relabeling.apply.Valid →
              (bundle.candidates index).datum.Valid := by
  classical
  refine ⟨alignedRelabeling profile, alignedBlock profile,
    alignedProfile profile input.valid.1, alignedShape shape input.valid.1,
    alignedInput input profile, alignedBlock_val profile, rfl, ?_⟩
  obtain ⟨geometry, hRel, hk, bundle, hValid⟩ :=
    W2M1kSwapped.nonempty_swappedBundle (alignedInput input profile)
      (alignedShape shape input.valid.1)
      (alignedProfile_aligned shape input.valid.1 hTargetConnected hGenus)
      hTargetConnected hGenus
  exact ⟨geometry, hRel, hk, bundle, hValid⟩

end DraismaVargas.LocalCases.W2SourceTransport
