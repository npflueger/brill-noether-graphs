module

public import DraismaVargas.LocalCases.W3FourLimitRows
public import DraismaVargas.LocalCases.W3Nd3StableGraph

@[expose] public section

/-!
# Outgoing survival and the endpoint census of Figure 28's four members

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a=k₄)}`, its Positions
I/II.a/II.b, Figure 28 and Equation (2).  Figure 28's members may live over
different representatives of one isomorphism class of gluing data (see
`W3FourSourceCandidates`).

`W3FourLimitRows` derives `W3FourStableGraph.LimitRows`, so Figure 28's
receipts stand over the *limit's* own stable rows.  What remains is that those
rows are the **members'** rows, and the retained half of that is this module:
which occurrences of each outgoing member survive, what the
complete surviving star at each new endpoint is, and which stable row each
surviving new occurrence joins.

## Does the census cross the branch swap?

It does -- but not along `W3FourStableGraph.WallTransport`, and not member to
member.

* `WallTransport` is only a map of occurrence sets preserving target
  occurrence and dilation index.  That is exactly what a *length matrix*
  reads, and nothing more: a `WallTransport` need not be injective, need not
  preserve incidence, and is not a morphism of source graphs.  `IsDangling`,
  `nonDanglingIncident`, `nonDanglingValency` and `Consecutive` are none of
  them functions of (target occurrence, index), so
  `WallTransport.ofSheetRelabeling` does **not** extend to them and nothing
  below is routed through `WallTransport`.
* The gauge Figure 28 actually uses is `W3FourDisjointness.branchSwapOfPerm`,
  which is a `GluingDatum.SheetRelabeling` -- a genuine isomorphism of gluing
  data.  Along one of those the entire census already transports:
  `SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff`,
  `incident_sourceEdgeEquiv_iff`, and `SheetRelabelStable`'s
  `nonDanglingIncident_map`, `nonDanglingValency_map`, `consecutive_map_iff`
  and `stablePathEquiv`, needing only `data.Connected`.  `BranchGauge` has no
  `nonDangling_valency` field, but `SheetRelabelStable.nonDanglingValency_map`
  supplies it, as `W3FourDisjointness`'s module docstring notes.
* The transport nevertheless cannot run from an outgoing member over `data` to
  an outgoing member over the swapped copy, because **there is no Position I
  or Position II.b member over `data`**: that is exactly
  `W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`.  There is no
  outgoing census on the unswapped datum to push forward.

So the census is stated and proved **once**, over
`W3FourClosure.FourStarGeometry` together with the one further datum it needs,
`SelectedSurvival` -- the incoming selected-star census.  `SelectedSurvival`
is the only non-`FourStarGeometry` input, it is *not* length-matrix data, and
it is exactly what the branch swap has to carry: `SelectedSurvival.swap`
transports it along `branchSwapOfPerm`, at the cost of `data.Connected` and
nothing else.  Per swapped copy the census costs one application of that
lemma; per member it costs nothing.

## What is proved here

* `SelectedSurvival`, `SelectedSurvival.ofGrowProfile`, `SelectedSurvival.swap`
  -- the incoming selected-star census, derived from
  `ThirdEquation.W3SourceInput` plus `W3FourSourceCandidates.GrowProfile`, and
  transported across DV's branch swap.
* `ReversedMember` and its census: `M⁽¹⁾` and `M⁽²⁾` share the shape
  `FourStarGeometry.reversedCandidate`, so their surviving-star statements are
  proved once for an arbitrary refinement `fine` and then instantiated.
  `ReversedMember.nonDanglingIncident_fresh_grow`, `_fresh_other` and
  `_fresh_triple` are the trivalent endpoints' complete surviving stars, and
  `nonDanglingIncident_old_pair` / `_old_triple` the divalent endpoint's.
* `PositionOne`: `new_grow_survives` and `new_other_survives` -- **both**
  selected new occurrences survive; `nonDanglingIncident_fresh_grow` /
  `nonDanglingIncident_fresh_other` and the two `…_eq_two` valencies -- each
  meets its own retained smaller survivor at a **valency-two trivalent**
  endpoint; `new_grow_stablePath` / `new_other_stablePath` -- their rows;
  `nonDanglingIncident_old` and `old_nonDanglingValency_eq_three` -- the
  divalent endpoint is the branch vertex.
* `PositionTwo`: `new_outside_dangles` and `nonDanglingIncident_fresh_outside`
  -- the detached singleton new occurrence **dangles** and its endpoint is
  entirely pruned; `new_grow_survives`, `nonDanglingIncident_old` and
  `old_nonDanglingValency_eq_two` -- the big new occurrence survives and meets
  `e₄` at the **valency-two divalent** endpoint, whose row it joins
  (`new_grow_stablePath`); `fresh_grow_nonDanglingValency_eq_three` -- the
  trivalent endpoint is the branch vertex.
* `GrowMember` (Position II.a, so `M⁽³⁾` and `M⁽⁴⁾` at once):
  `new_dangles_of_separate` and `nonDanglingIncident_old_separate` -- every
  selected new occurrence outside the enlarged class **dangles** and its
  endpoint is entirely pruned; `new_grow_survives`,
  `nonDanglingIncident_old_grow`, `old_grow_nonDanglingValency_eq_two` and
  `new_grow_stablePath` -- the `k+1` occurrence survives, meets `e₂` at the
  valency-two divalent endpoint and joins its row;
  `nonDanglingIncident_fresh` and `fresh_nonDanglingValency_eq_three` -- the
  trivalent endpoint is the branch vertex.
* `BackgroundShape` -- the census at every *background* wall block, where all
  four members install one surviving direction's own edge partition on the new
  edge: `incident_old_cases` (the complete literal incidence),
  `new_isDangling_iff` (pruning equivalence with the old representative),
  `nonDanglingIncident_old` / `old_nonDanglingValency_eq_two`,
  `new_stablePath_eq` (consecutiveness, hence the shared row) and
  `newIndex_eq`.  `ReversedMember.toBackgroundShape` and
  `GrowMember.toBackgroundShape` install it with `t₄` and with the grow
  direction respectively, which is Figure 28's `α = 4, 4, 2, 3`.

Every endpoint statement is an identity of **occurrence** sets
(`nonDanglingIncident`), never of stable-row labels; nothing below asks the
rows of `e₂`, `e₃`, `e₄` to be distinct, so a stable loop through a branch
vertex is not excluded.

## Which datum this is about

`ThirdEquation.W3SourceInput` carries `equation_c : data.targetExcess wall = 1`,
so the incoming half lives on the wall/limit side of the bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`, exactly as
`W3FourClosure`, `W3FourStableGraph` and `W3FourLimitRows` do.  The surviving
stars computed here are stars of the **outgoing** members' data, which is the
other side; no single object is asked to be both.
-/

namespace DraismaVargas.LocalCases.W3FourSurvival

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine ResolutionM11
open W3FourSourceCandidates
open W3FourDisjointness
open W3FourClosure

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-! ## The incoming selected star

Everything the outgoing census needs from the incoming datum beyond
`FourStarGeometry`: which occurrences above the distinguished wall block
survive.  Stated on plain source occurrences rather than on
`IncidentSourceEdge` subtypes, because that is the form a sheet relabelling
transports without a cast. -/

/-- The incoming survival census at the distinguished wall block: the three
occurrences `e₂`, `e₃`, `e₄` survive, and nothing else above `A₀` does. -/
structure SelectedSurvival (data : GluingDatum target degree) (wall : target.V)
    (geometry : FourStarGeometry data wall) : Prop where
  /-- `e₂` survives. -/
  grow_survives : ¬ IsDangling data
    (data.sourceEdge geometry.growTarget geometry.growAnchor)
  /-- `e₃` survives. -/
  other_survives : ¬ IsDangling data
    (data.sourceEdge geometry.otherTarget geometry.otherAnchor)
  /-- `e₄` survives. -/
  largest_survives : ¬ IsDangling data
    (data.sourceEdge geometry.largestTarget geometry.largestAnchor)
  /-- The literal `nd = 3` statement: those three exhaust the survivors of
  `A₀`. -/
  exhaustive : ∀ edge : data.SourceEdge,
    Incident data edge (data.sourceEndpoint wall geometry.growAnchor) →
    ¬ IsDangling data edge →
      edge = data.sourceEdge geometry.growTarget geometry.growAnchor ∨
      edge = data.sourceEdge geometry.otherTarget geometry.otherAnchor ∨
      edge = data.sourceEdge geometry.largestTarget geometry.largestAnchor

/-- Any sheet of a wall block names that block's quotient-source vertex. -/
theorem sourceEndpoint_eq_wallBlock (block : WallBlock data wall)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    data.sourceEndpoint wall sheet = WallBlock.sourceVertex data wall block := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hSheet.symm

/-! ### Derived from the source -/

section OfSource

variable {star : ThreeStar target wall} {input : W3SourceInput data star}

/-- **The incoming census, derived.**  No numerical diagram: the three
survivors and their exhaustiveness are the fields `surviving` of
`W3FourSourceCandidates.GrowProfile`, which comes from an arbitrary
`W3R1SourceProfile.Nd3Profile`. -/
theorem SelectedSurvival.ofGrowProfile (grown : GrowProfile input) :
    SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown) := by
  have hVertex : data.sourceEndpoint wall grown.growAnchor =
      WallBlock.sourceVertex data wall input.distinguishedBlock :=
    sourceEndpoint_eq_wallBlock input.distinguishedBlock grown.growAnchor
      grown.growAnchor_wall_rel
  have hGrow : data.sourceEdge grown.growTarget grown.growAnchor = grown.grow.1 :=
    GluingDatum.sourceEdge_self data grown.grow.1
  have hOther : data.sourceEdge grown.otherTarget grown.otherAnchor =
      grown.other.1 := GluingDatum.sourceEdge_self data grown.other.1
  have hLargest : data.sourceEdge grown.largestTarget grown.largestAnchor =
      grown.largest.1 := GluingDatum.sourceEdge_self data grown.largest.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ¬ IsDangling data (data.sourceEdge grown.growTarget grown.growAnchor)
    rw [hGrow]
    exact (mem_survivors data input.distinguishedBlock grown.grow).mp
      (by rw [grown.surviving]; simp)
  · show ¬ IsDangling data (data.sourceEdge grown.otherTarget grown.otherAnchor)
    rw [hOther]
    exact (mem_survivors data input.distinguishedBlock grown.other).mp
      (by rw [grown.surviving]; simp)
  · show ¬ IsDangling data
      (data.sourceEdge grown.largestTarget grown.largestAnchor)
    rw [hLargest]
    exact (mem_survivors data input.distinguishedBlock grown.largest).mp
      (by rw [grown.surviving]; simp)
  · show ∀ edge : data.SourceEdge,
      Incident data edge (data.sourceEndpoint wall grown.growAnchor) →
      ¬ IsDangling data edge →
        edge = data.sourceEdge grown.growTarget grown.growAnchor ∨
        edge = data.sourceEdge grown.otherTarget grown.otherAnchor ∨
        edge = data.sourceEdge grown.largestTarget grown.largestAnchor
    intro edge hIncident hSurvives
    rw [hVertex] at hIncident
    have hMem := (mem_survivors data input.distinguishedBlock
      ⟨edge, hIncident⟩).mpr hSurvives
    rw [grown.surviving] at hMem
    rcases Finset.mem_insert.mp hMem with hEq | hRest
    · rw [hGrow]
      exact Or.inl (congrArg Subtype.val hEq)
    · rcases Finset.mem_insert.mp hRest with hEq | hEq
      · rw [hOther]
        exact Or.inr (Or.inl (congrArg Subtype.val hEq))
      · rw [hLargest]
        exact Or.inr (Or.inr
          (congrArg Subtype.val (Finset.mem_singleton.mp hEq)))

end OfSource

/-! ### Transport across DV's branch swap

The one lemma the two swapped members need.  It is stated along
`W3FourDisjointness.branchSwapOfPerm` because that is the gauge Figure 28
uses, and it consumes `data.Connected` -- the single hypothesis
`SheetRelabelPruning` needs -- and nothing else. -/

section Swap

variable (geometry : FourStarGeometry data wall)
  (root : target.V) (hRoot : root ≠ wall)
  (permutation : Equiv.Perm (Fin degree))
  (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)

omit hFix in
/-- The wall lies outside the moved branch, so the swap fixes its sheets. -/
theorem branchSwap_vertexPermutation_wall
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (sheet : Fin degree) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).vertexPermutation
        wall sheet = sheet := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.vertexMoved wall root hRoot wall) permutation sheet = sheet
  rw [TargetBranchRegion.vertexMoved_wall]
  rfl

omit hFix in
/-- A target direction outside the moved branch keeps every sheet name. -/
theorem branchSwap_edgePermutation_of_fixed
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false)
    (sheet : Fin degree) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).edgePermutation
        edge sheet = sheet := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall root hRoot edge) permutation sheet = sheet
  rw [hFixed]
  rfl

omit hFix in
/-- A target direction inside the moved branch is relabelled by the chosen
permutation. -/
theorem branchSwap_edgePermutation_of_moved
    (hFix : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true)
    (sheet : Fin degree) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).edgePermutation
        edge sheet = permutation sheet := by
  change GluingDatum.SheetRelabeling.togglePermutation
    (TargetBranchRegion.edgeMoved wall root hRoot edge) permutation sheet = _
  rw [hMoved]
  rfl

/-- The swapped copy's canonical occurrence above a *fixed* direction is the
image of the original one. -/
theorem branchSwap_sourceEdge_of_fixed (edge : target.edges)
    (hFixed : TargetBranchRegion.edgeMoved wall root hRoot edge = false)
    (sheet : Fin degree) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.sourceEdge
        edge sheet =
      (branchSwapOfPerm data wall root hRoot permutation hFix).sourceEdgeEquiv
        (data.sourceEdge edge sheet) := by
  rw [SheetRelabelPruning.sourceEdgeEquiv_sourceEdge,
    branchSwap_edgePermutation_of_fixed root hRoot permutation hFix edge hFixed]

/-- The swapped copy's canonical occurrence above a *moved* direction is the
image of the original one through the permutation. -/
theorem branchSwap_sourceEdge_of_moved (edge : target.edges)
    (hMoved : TargetBranchRegion.edgeMoved wall root hRoot edge = true)
    (sheet : Fin degree) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.sourceEdge
        edge (permutation sheet) =
      (branchSwapOfPerm data wall root hRoot permutation hFix).sourceEdgeEquiv
        (data.sourceEdge edge sheet) := by
  rw [SheetRelabelPruning.sourceEdgeEquiv_sourceEdge,
    branchSwap_edgePermutation_of_moved root hRoot permutation hFix edge hMoved]

/-- The swapped copy's wall endpoints are the images of the original ones. -/
theorem branchSwap_sourceEndpoint_wall (sheet : Fin degree) :
    (branchSwapOfPerm data wall root hRoot permutation hFix).apply.sourceEndpoint
        wall sheet =
      (branchSwapOfPerm data wall root hRoot permutation hFix).sourceVertexEquiv
        (data.sourceEndpoint wall sheet) := by
  rw [SheetRelabelPruning.sourceVertexEquiv_sourceEndpoint,
    branchSwap_vertexPermutation_wall root hRoot permutation hFix]

/-- **The incoming census crosses the branch swap.**  Survival, incidence and
the exhaustiveness of the three survivors are all isomorphism invariants of
the quotient source, and a branch swap is an isomorphism of gluing data;
`SheetRelabelPruning` supplies both directions.  This is the whole cost of the
gauge for the outgoing census below. -/
theorem SelectedSurvival.swap (survival : SelectedSurvival data wall geometry)
    (hConnected : data.Connected)
    (hGrowFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.growTarget = false)
    (hLargestFixed :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.largestTarget = false)
    (hOtherMoved :
      TargetBranchRegion.edgeMoved wall root hRoot geometry.otherTarget = true) :
    SelectedSurvival
      (branchSwapOfPerm data wall root hRoot permutation hFix).apply wall
      (geometry.swap root hRoot permutation hFix hGrowFixed hLargestFixed
        hOtherMoved) := by
  set relabeling := branchSwapOfPerm data wall root hRoot permutation hFix
    with hRelabeling
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ¬ IsDangling relabeling.apply
      (relabeling.apply.sourceEdge geometry.growTarget geometry.growAnchor)
    rw [branchSwap_sourceEdge_of_fixed root hRoot permutation hFix
      geometry.growTarget hGrowFixed,
      SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff relabeling hConnected]
    exact survival.grow_survives
  · show ¬ IsDangling relabeling.apply
      (relabeling.apply.sourceEdge geometry.otherTarget
        (permutation geometry.otherAnchor))
    rw [branchSwap_sourceEdge_of_moved root hRoot permutation hFix
      geometry.otherTarget hOtherMoved,
      SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff relabeling hConnected]
    exact survival.other_survives
  · show ¬ IsDangling relabeling.apply
      (relabeling.apply.sourceEdge geometry.largestTarget geometry.largestAnchor)
    rw [branchSwap_sourceEdge_of_fixed root hRoot permutation hFix
      geometry.largestTarget hLargestFixed,
      SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff relabeling hConnected]
    exact survival.largest_survives
  · show ∀ edge : relabeling.apply.SourceEdge,
      Incident relabeling.apply edge
        (relabeling.apply.sourceEndpoint wall geometry.growAnchor) →
      ¬ IsDangling relabeling.apply edge →
        edge = relabeling.apply.sourceEdge geometry.growTarget
            geometry.growAnchor ∨
        edge = relabeling.apply.sourceEdge geometry.otherTarget
            (permutation geometry.otherAnchor) ∨
        edge = relabeling.apply.sourceEdge geometry.largestTarget
            geometry.largestAnchor
    intro edge hIncident hSurvives
    obtain ⟨edge, rfl⟩ := relabeling.sourceEdgeEquiv.surjective edge
    rw [branchSwap_sourceEndpoint_wall root hRoot permutation hFix,
      SheetRelabelPruning.incident_sourceEdgeEquiv_iff] at hIncident
    rw [SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff relabeling hConnected]
      at hSurvives
    rw [branchSwap_sourceEdge_of_fixed root hRoot permutation hFix
      geometry.growTarget hGrowFixed,
      branchSwap_sourceEdge_of_moved root hRoot permutation hFix
        geometry.otherTarget hOtherMoved,
      branchSwap_sourceEdge_of_fixed root hRoot permutation hFix
        geometry.largestTarget hLargestFixed]
    rcases survival.exhaustive edge hIncident hSurvives with hEq | hEq | hEq
    · exact Or.inl (congrArg relabeling.sourceEdgeEquiv hEq)
    · exact Or.inr (Or.inl (congrArg relabeling.sourceEdgeEquiv hEq))
    · exact Or.inr (Or.inr (congrArg relabeling.sourceEdgeEquiv hEq))

end Swap


/-! ## The shape `M⁽¹⁾` and `M⁽²⁾` share

Both remaining Figure 28 members are `FourStarGeometry.reversedCandidate` of
some refinement of `A₀`: the whole block stays at the divalent endpoint beside
`t₄`, and the refinement sits on the new edge and at the trivalent endpoint
beside `t₂` and `t₃`.  The census is proved once for an arbitrary refinement
and instantiated twice below. -/

/-- One member of Figure 28's reversed pair, packaged so the shared census is
stated once.  `PositionOne.toReversedMember` and `PositionTwo.toReversedMember`
produce `M⁽¹⁾` and `M⁽²⁾`, with `candidate` definitionally the member
`W3FourClosure` already built. -/
structure ReversedMember (data : GluingDatum target degree) (wall : target.V) where
  /-- The wall geometry of the case. -/
  geometry : FourStarGeometry data wall
  /-- The refinement of `A₀` installed on the new edge. -/
  fine : SheetPartition degree
  fine_refines : fine.Refines (data.vertexPartition wall)
  grow_refines : (data.edgePartition geometry.growTarget).Refines fine
  other_refines : (data.edgePartition geometry.otherTarget).Refines fine
  counts : ∀ sheet, (data.vertexPartition wall).Rel geometry.growAnchor sheet →
    fine.blockCountWithin fine sheet +
        (data.edgePartition geometry.growTarget).blockCountWithin fine sheet +
        (data.edgePartition geometry.otherTarget).blockCountWithin fine sheet ≥
      fine.blockCard sheet + 2

namespace ReversedMember

variable (member : ReversedMember data wall)

/-- The globally assembled member. -/
noncomputable def candidate : Candidate target degree data wall :=
  member.geometry.reversedCandidate member.fine member.fine_refines
    member.grow_refines member.other_refines member.counts

/-- Its pasted local resolution. -/
noncomputable def pasted : LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall) member.candidate.resolution
    member.candidate.contracts

theorem candidate_valid (hValid : data.Valid) : member.candidate.datum.Valid :=
  FourStarGeometry.reversedCandidate_valid _ _ _ _ _ _ hValid

theorem candidate_sourceGenus :
    genus member.candidate.datum.sourceGraph = genus data.sourceGraph :=
  FourStarGeometry.reversedCandidate_sourceGenus _ _ _ _ _ _

/-! ### Side assignment -/

theorem right_largest :
    member.candidate.right member.geometry.largestTarget = false := by
  show W3Nd2SourceCandidates.rightOf member.geometry.largestTarget
    member.geometry.largestTarget = false
  simp [W3Nd2SourceCandidates.rightOf]

theorem right_grow : member.candidate.right member.geometry.growTarget = true := by
  show W3Nd2SourceCandidates.rightOf member.geometry.largestTarget
    member.geometry.growTarget = true
  simp [W3Nd2SourceCandidates.rightOf, member.geometry.grow_ne_largest]

theorem right_other : member.candidate.right member.geometry.otherTarget = true := by
  show W3Nd2SourceCandidates.rightOf member.geometry.largestTarget
    member.geometry.otherTarget = true
  simp [W3Nd2SourceCandidates.rightOf, member.geometry.other_ne_largest]

/-! ### The pasted endpoint dictionary over the distinguished block -/

/-- Over the distinguished block the member is literally the reversed star. -/
theorem resolution_selected {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel member.geometry.growAnchor sheet) :
    member.candidate.resolution sheet =
      (fineResolution (data.vertexPartition wall) member.fine
        member.fine_refines).reverse :=
  FourStarGeometry.reversedCandidate_resolution_selected member.geometry
    member.fine member.fine_refines member.grow_refines member.other_refines
    member.counts hSheet

theorem pasted_left_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel member.geometry.growAnchor sheet) :
    member.pasted.left.block sheet = (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    member.candidate.resolution member.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [member.resolution_selected
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem pasted_right_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel member.geometry.growAnchor sheet) :
    member.pasted.right.block sheet = member.fine.block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    member.candidate.resolution member.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [member.resolution_selected
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem pasted_newEdge_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel member.geometry.growAnchor sheet) :
    member.pasted.newEdge.block sheet = member.fine.block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    member.candidate.resolution member.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [member.resolution_selected
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

/-! ### Occurrences and incidences -/

/-- The distinguished wall block, named by its anchor. -/
noncomputable def selectedBlock : WallBlock data wall :=
  WallBlock.ofSheet data wall member.geometry.growAnchor

theorem selectedBlock_rel {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel member.geometry.growAnchor sheet) :
    (data.vertexPartition wall).Rel member.selectedBlock.1 sheet :=
  ((data.vertexPartition wall).rel_repr_left member.geometry.growAnchor).trans hSheet

theorem sourceVertex_selectedBlock :
    WallBlock.sourceVertex data wall member.selectedBlock =
      data.sourceEndpoint wall member.geometry.growAnchor := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (data.vertexPartition wall).repr_idem member.geometry.growAnchor

/-- Retained occurrences keep their incoming pruning status. -/
theorem old_isDangling_iff (hValid : data.Valid) (edge : data.SourceEdge) :
    IsDangling member.candidate.datum (member.candidate.oldSourceEdge edge) ↔
      IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff member.candidate hValid
    member.candidate_sourceGenus edge

theorem new_ne_old (sheet : Fin degree) (edge : data.SourceEdge) :
    member.candidate.newSourceEdge sheet ≠ member.candidate.oldSourceEdge edge := by
  intro hEqual
  have hTargets := congrArg
    (fun item : member.candidate.datum.SourceEdge ↦ item.1.1) hEqual
  have hLabels :=
    (occurrenceEquiv target wall member.candidate.right).injective hTargets
  cases hLabels

theorem new_incident_old (sheet : Fin degree) :
    Incident member.candidate.datum (member.candidate.newSourceEdge sheet)
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    member.candidate.right member.pasted
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ member.candidate.exterior) sheet))

theorem new_incident_fresh (sheet : Fin degree) :
    Incident member.candidate.datum (member.candidate.newSourceEdge sheet)
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
    member.candidate.right member.pasted
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ member.candidate.exterior) sheet))

theorem largest_incident_old (sheet : Fin degree) :
    Incident member.candidate.datum
        (member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.largestTarget sheet))
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  W3Nd2Survival.oldSourceEdge_incident_old member.candidate
    member.geometry.largestTarget member.geometry.largestTarget_mem
    member.right_largest sheet

theorem grow_incident_fresh (sheet : Fin degree) :
    Incident member.candidate.datum
        (member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.growTarget sheet))
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  M11SplitSurvival.oldSourceEdge_incident_fresh member.candidate
    member.geometry.growTarget member.geometry.growTarget_mem
    member.right_grow sheet

theorem other_incident_fresh (sheet : Fin degree) :
    Incident member.candidate.datum
        (member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.otherTarget sheet))
      (member.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  M11SplitSurvival.oldSourceEdge_incident_fresh member.candidate
    member.geometry.otherTarget member.geometry.otherTarget_mem
    member.right_other sheet

/-! ### The endpoint dictionary -/

theorem old_endpoint_eq {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel member.geometry.growAnchor first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    member.candidate.datum.sourceEndpoint (oldVertex target wall) first =
      member.candidate.datum.sourceEndpoint (oldVertex target wall) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (member.candidate.datum.vertexPartition
        (oldVertex target wall)).repr first =
      (member.candidate.datum.vertexPartition (oldVertex target wall)).repr second
    rw [show member.candidate.datum.vertexPartition (oldVertex target wall) =
        member.pasted.left from
      GlobalResolution.expandedVertexPartition_old_wall data wall _]
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← member.pasted_left_block hFirst] at hMem
    exact (member.pasted.left.mem_block_iff first second).mp hMem

theorem fresh_endpoint_eq {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel member.geometry.growAnchor first)
    (hRel : member.fine.Rel first second) :
    member.candidate.datum.sourceEndpoint (freshVertex target) first =
      member.candidate.datum.sourceEndpoint (freshVertex target) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change member.pasted.right.repr first = member.pasted.right.repr second
    have hMem : second ∈ member.fine.block first :=
      (member.fine.mem_block_iff first second).mpr hRel
    rw [← member.pasted_right_block hFirst] at hMem
    exact (member.pasted.right.mem_block_iff first second).mp hMem

theorem newSourceEdge_eq_of_fine_rel {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel member.geometry.growAnchor first)
    (hRel : member.fine.Rel first second) :
    member.candidate.newSourceEdge second = member.candidate.newSourceEdge first := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change member.pasted.newEdge.repr second = member.pasted.newEdge.repr first
    have hMem : second ∈ member.fine.block first :=
      (member.fine.mem_block_iff first second).mpr hRel
    rw [← member.pasted_newEdge_block hFirst] at hMem
    exact ((member.pasted.newEdge.mem_block_iff first second).mp hMem).symm

/-! ### The two endpoint classifications

Everything `M⁽¹⁾` and `M⁽²⁾` share.  At the divalent endpoint only `t₄` is
present, and `e₄` is its only survivor above `A₀`; at a trivalent endpoint only
`t₂` and `t₃` are, and `e₂`, `e₃` are their only survivors.  Both statements
are identities of occurrences, and neither asks the rows of `e₂`, `e₃`, `e₄` to
be distinct. -/

/-- **The divalent endpoint.**  A surviving occurrence there is either the
retained `e₄` or one of the member's own new occurrences above `A₀`. -/
theorem incident_old_cases (survival : SelectedSurvival data wall member.geometry)
    (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel member.geometry.growAnchor sheet)
    {edge : member.candidate.datum.SourceEdge}
    (hSurvives : ¬ IsDangling member.candidate.datum edge)
    (hIncident : Incident member.candidate.datum edge
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    edge = member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.largestTarget
          member.geometry.largestAnchor) ∨
      ∃ other : Fin degree,
        (data.vertexPartition wall).Rel member.geometry.growAnchor other ∧
          edge = member.candidate.newSourceEdge other := by
  rcases ResolutionPruning.sourceEdge_cases member.candidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · left
    obtain ⟨hData, hRight⟩ :=
      W3Nd3StableGraph.old_incident_old_selected_info_local member.candidate
        member.selectedBlock sheet (member.selectedBlock_rel hSheet) old hIncident
    rw [member.sourceVertex_selectedBlock] at hData
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((member.old_isDangling_iff hValid old).mpr hDangling)
    rcases survival.exhaustive old hData hOldSurvives with rfl | rfl | rfl
    · exact Bool.noConfusion (member.right_grow.symm.trans hRight)
    · exact Bool.noConfusion (member.right_other.symm.trans hRight)
    · rfl
  · right
    refine ⟨member.pasted.newEdge.repr new, ?_, ?_⟩
    · have hRel := W3Nd3StableGraph.new_incident_old_sheet_rel_local
        member.candidate sheet new hIncident
      have hMem : member.pasted.newEdge.repr new ∈ member.pasted.left.block sheet :=
        (member.pasted.left.mem_block_iff _ _).mpr hRel
      rw [member.pasted_left_block hSheet] at hMem
      exact hSheet.trans (((data.vertexPartition wall).mem_block_iff _ _).mp hMem)
    · exact (W3Nd3StableGraph.newSourceEdge_repr_local member.candidate new).symm

/-- **A trivalent endpoint.**  A surviving occurrence there is either the
member's own new occurrence through that endpoint, or the retained `e₂`, or the
retained `e₃`; in the latter two cases the endpoint's class meets the
survivor's sheet. -/
theorem incident_fresh_cases
    (survival : SelectedSurvival data wall member.geometry)
    (hValid : data.Valid) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    {edge : member.candidate.datum.SourceEdge}
    (hSurvives : ¬ IsDangling member.candidate.datum edge)
    (hIncident : Incident member.candidate.datum edge
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    edge = member.candidate.newSourceEdge anchor ∨
      (edge = member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.growTarget
            member.geometry.growAnchor) ∧
        member.fine.Rel anchor member.geometry.growAnchor) ∨
      (edge = member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.otherTarget
            member.geometry.otherAnchor) ∧
        member.fine.Rel anchor member.geometry.otherAnchor) := by
  rcases ResolutionPruning.sourceEdge_cases member.candidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · obtain ⟨hData, hRight⟩ :=
      W3Nd2EndRows.old_incident_fresh_selected_info member.candidate
        member.selectedBlock anchor (member.selectedBlock_rel hAnchor) old hIncident
    rw [member.sourceVertex_selectedBlock] at hData
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((member.old_isDangling_iff hValid old).mpr hDangling)
    have hSheetRel := W3Nd3StableGraph.old_incident_fresh_sheet_rel_local
      member.candidate anchor old hIncident
    have hMem : old.1.2 ∈ member.pasted.right.block anchor :=
      (member.pasted.right.mem_block_iff _ _).mpr hSheetRel
    rw [member.pasted_right_block hAnchor] at hMem
    have hFineRel : member.fine.Rel anchor old.1.2 :=
      (member.fine.mem_block_iff _ _).mp hMem
    rcases survival.exhaustive old hData hOldSurvives with rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, hFineRel.trans (member.grow_refines.rel
        ((data.edgePartition member.geometry.growTarget).rel_repr_left
          member.geometry.growAnchor))⟩)
    · exact Or.inr (Or.inr ⟨rfl, hFineRel.trans (member.other_refines.rel
        ((data.edgePartition member.geometry.otherTarget).rel_repr_left
          member.geometry.otherAnchor))⟩)
    · exact Bool.noConfusion (member.right_largest.symm.trans hRight)
  · left
    have hOutgoing := (incident_iff_target_mem_and_rel member.candidate.datum
      (member.candidate.newSourceEdge new)
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)).mp
      hIncident
    change occurrenceEquiv target wall member.candidate.right none ∈
        GluingDatum.incidentEdges (freshVertex target) ∧
      member.pasted.right.Rel (member.pasted.right.repr anchor)
        (member.pasted.newEdge.repr new) at hOutgoing
    have hRightRel : member.pasted.right.Rel anchor
        (member.pasted.newEdge.repr new) :=
      (member.pasted.right.rel_repr_right anchor).trans hOutgoing.2
    have hMem : member.pasted.newEdge.repr new ∈
        member.pasted.right.block anchor :=
      (member.pasted.right.mem_block_iff _ _).mpr hRightRel
    rw [member.pasted_right_block hAnchor,
      ← member.pasted_newEdge_block hAnchor] at hMem
    have hNewRel := (member.pasted.newEdge.mem_block_iff anchor _).mp hMem
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change member.pasted.newEdge.repr new = member.pasted.newEdge.repr anchor
      exact (member.pasted.newEdge.repr_idem new).symm.trans hNewRel.symm

/-! ### Survival of the retained survivors -/

theorem grow_survives_out (survival : SelectedSurvival data wall member.geometry)
    (hValid : data.Valid) :
    ¬ IsDangling member.candidate.datum
      (member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.growTarget member.geometry.growAnchor)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge member.candidate hValid.1 _
    survival.grow_survives

theorem other_survives_out (survival : SelectedSurvival data wall member.geometry)
    (hValid : data.Valid) :
    ¬ IsDangling member.candidate.datum
      (member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.otherTarget member.geometry.otherAnchor)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge member.candidate hValid.1 _
    survival.other_survives

theorem largest_survives_out (survival : SelectedSurvival data wall member.geometry)
    (hValid : data.Valid) :
    ¬ IsDangling member.candidate.datum
      (member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.largestTarget
          member.geometry.largestAnchor)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge member.candidate hValid.1 _
    survival.largest_survives

/-- `e₄` meets the divalent endpoint above every sheet of `A₀`. -/
theorem largest_incident_old_of_wall_rel {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel member.geometry.growAnchor sheet) :
    Incident member.candidate.datum
        (member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.largestTarget
            member.geometry.largestAnchor))
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) := by
  have hIncident := member.largest_incident_old member.geometry.largestAnchor
  rwa [member.old_endpoint_eq member.geometry.largest_wall_rel
    (member.geometry.largest_wall_rel.symm.trans hSheet)] at hIncident

theorem grow_incident_fresh_anchor :
    Incident member.candidate.datum
        (member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.growTarget member.geometry.growAnchor))
      (member.candidate.datum.sourceEndpoint (freshVertex target)
        member.geometry.growAnchor) :=
  member.grow_incident_fresh member.geometry.growAnchor

theorem other_incident_fresh_anchor :
    Incident member.candidate.datum
        (member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.otherTarget member.geometry.otherAnchor))
      (member.candidate.datum.sourceEndpoint (freshVertex target)
        member.geometry.otherAnchor) :=
  member.other_incident_fresh member.geometry.otherAnchor

theorem old_grow_ne_other :
    member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.growTarget member.geometry.growAnchor) ≠
      member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.otherTarget
          member.geometry.otherAnchor) := by
  intro hEq
  exact member.geometry.grow_ne_other
    (congrArg (fun edge : data.SourceEdge ↦ edge.1.1)
      (W3Nd3StableGraph.oldSourceEdge_injective_local member.candidate hEq))

/-! ### The trivalent endpoints -/

/-- A new occurrence whose trivalent class meets neither smaller survivor
**dangles**: its endpoint would otherwise have surviving valency one. -/
theorem new_isDangling_of_fresh_separate
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hGrowSep : ¬ member.fine.Rel anchor member.geometry.growAnchor)
    (hOtherSep : ¬ member.fine.Rel anchor member.geometry.otherAnchor) :
    IsDangling member.candidate.datum (member.candidate.newSourceEdge anchor) := by
  classical
  by_contra hSurvives
  have hSubset : nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) ⊆
      {member.candidate.newSourceEdge anchor} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases member.incident_fresh_cases survival hValid hAnchor hEdgeSurvives
      hEdgeIncident with hNew | ⟨_, hRel⟩ | ⟨_, hRel⟩
    · exact Finset.mem_singleton.mpr hNew
    · exact absurd hRel hGrowSep
    · exact absurd hRel hOtherSep
  have hLe := (Finset.card_le_card hSubset).trans_eq (Finset.card_singleton _)
  have hPos : 0 < (nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨hSurvives, member.new_incident_fresh anchor⟩⟩
  have hNe : (nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one member.candidate.datum
      (member.candidate_valid hValid).1
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)
  omega

/-- **The trivalent endpoint whose class carries `e₂` but not `e₃`.**  Its
complete surviving star is the new occurrence together with the retained `e₂`;
in particular the new occurrence survives and joins `e₂`'s stable row. -/
theorem nonDanglingIncident_fresh_grow
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hGrow : member.fine.Rel anchor member.geometry.growAnchor)
    (hOtherSep : ¬ member.fine.Rel anchor member.geometry.otherAnchor) :
    nonDanglingIncident member.candidate.datum
        (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) =
      {member.candidate.newSourceEdge anchor,
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.growTarget
            member.geometry.growAnchor)} := by
  classical
  have hGrowIncident : Incident member.candidate.datum
      (member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.growTarget member.geometry.growAnchor))
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) := by
    have := member.grow_incident_fresh_anchor
    rwa [member.fresh_endpoint_eq hAnchor hGrow]
  have hSubset : nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) ⊆
      {member.candidate.newSourceEdge anchor,
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.growTarget
            member.geometry.growAnchor)} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases member.incident_fresh_cases survival hValid hAnchor hEdgeSurvives
      hEdgeIncident with hNew | ⟨hOld, _⟩ | ⟨_, hRel⟩
    · exact Finset.mem_insert.mpr (Or.inl hNew)
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hOld)
    · exact absurd hRel hOtherSep
  have hPairCard : ({member.candidate.newSourceEdge anchor,
      member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.growTarget member.geometry.growAnchor)} :
      Finset member.candidate.datum.SourceEdge).card = 2 :=
    Finset.card_pair (member.new_ne_old _ _)
  have hPos : 0 < (nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨member.grow_survives_out survival hValid, hGrowIncident⟩⟩
  have hLe := (Finset.card_le_card hSubset).trans_eq hPairCard
  have hNe : (nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one member.candidate.datum
      (member.candidate_valid hValid).1
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)
  exact Finset.eq_of_subset_of_card_le hSubset
    (le_of_eq (hPairCard.trans (by omega)))

/-- The mirror statement at a trivalent endpoint carrying `e₃` but not `e₂`. -/
theorem nonDanglingIncident_fresh_other
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOther : member.fine.Rel anchor member.geometry.otherAnchor)
    (hGrowSep : ¬ member.fine.Rel anchor member.geometry.growAnchor) :
    nonDanglingIncident member.candidate.datum
        (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) =
      {member.candidate.newSourceEdge anchor,
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.otherTarget
            member.geometry.otherAnchor)} := by
  classical
  have hOtherIncident : Incident member.candidate.datum
      (member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.otherTarget member.geometry.otherAnchor))
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) := by
    have := member.other_incident_fresh_anchor
    rwa [member.fresh_endpoint_eq hAnchor hOther]
  have hSubset : nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) ⊆
      {member.candidate.newSourceEdge anchor,
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.otherTarget
            member.geometry.otherAnchor)} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases member.incident_fresh_cases survival hValid hAnchor hEdgeSurvives
      hEdgeIncident with hNew | ⟨_, hRel⟩ | ⟨hOld, _⟩
    · exact Finset.mem_insert.mpr (Or.inl hNew)
    · exact absurd hRel hGrowSep
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hOld)
  have hPairCard : ({member.candidate.newSourceEdge anchor,
      member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.otherTarget member.geometry.otherAnchor)} :
      Finset member.candidate.datum.SourceEdge).card = 2 :=
    Finset.card_pair (member.new_ne_old _ _)
  have hPos : 0 < (nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨member.other_survives_out survival hValid, hOtherIncident⟩⟩
  have hLe := (Finset.card_le_card hSubset).trans_eq hPairCard
  have hNe : (nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one member.candidate.datum
      (member.candidate_valid hValid).1
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor)
  exact Finset.eq_of_subset_of_card_le hSubset
    (le_of_eq (hPairCard.trans (by omega)))

/-- Two new occurrences above `A₀` coincide exactly when the refinement joins
their sheets. -/
theorem newSourceEdge_eq_iff_fine_rel {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel member.geometry.growAnchor first) :
    member.candidate.newSourceEdge first = member.candidate.newSourceEdge second ↔
      member.fine.Rel first second := by
  constructor
  · intro hEq
    have hSheet := congrArg
      (fun item : member.candidate.datum.SourceEdge ↦ item.1.2) hEq
    have hRel : member.pasted.newEdge.Rel first second := hSheet
    have hMem : second ∈ member.pasted.newEdge.block first :=
      (member.pasted.newEdge.mem_block_iff _ _).mpr hRel
    rw [member.pasted_newEdge_block hFirst] at hMem
    exact (member.fine.mem_block_iff _ _).mp hMem
  · intro hRel
    exact (member.newSourceEdge_eq_of_fine_rel hFirst hRel).symm

/-! ### The divalent endpoint -/

/-- **The divalent endpoint, when one new occurrence above `A₀` carries all the
survival.**  Its complete surviving star is that occurrence together with the
retained `e₄`; in particular it survives and joins `e₄`'s stable row. -/
theorem nonDanglingIncident_old_pair
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOthers : ∀ t, (data.vertexPartition wall).Rel member.geometry.growAnchor t →
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge t) →
      member.candidate.newSourceEdge t = member.candidate.newSourceEdge anchor) :
    nonDanglingIncident member.candidate.datum
        (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor) =
      {member.candidate.newSourceEdge anchor,
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.largestTarget
            member.geometry.largestAnchor)} := by
  classical
  have hSubset : nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor) ⊆
      {member.candidate.newSourceEdge anchor,
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.largestTarget
            member.geometry.largestAnchor)} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases member.incident_old_cases survival hValid hAnchor hEdgeSurvives
      hEdgeIncident with hLargest | ⟨t, hWall, rfl⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hLargest)
    · exact Finset.mem_insert.mpr (Or.inl (hOthers t hWall hEdgeSurvives))
  have hPairCard : ({member.candidate.newSourceEdge anchor,
      member.candidate.oldSourceEdge
        (data.sourceEdge member.geometry.largestTarget
          member.geometry.largestAnchor)} :
      Finset member.candidate.datum.SourceEdge).card = 2 :=
    Finset.card_pair (member.new_ne_old _ _)
  have hPos : 0 < (nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨member.largest_survives_out survival hValid,
        member.largest_incident_old_of_wall_rel hAnchor⟩⟩
  have hLe := (Finset.card_le_card hSubset).trans_eq hPairCard
  have hNe : (nonDanglingIncident member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor)).card
        ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one member.candidate.datum
      (member.candidate_valid hValid).1
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor)
  exact Finset.eq_of_subset_of_card_le hSubset
    (le_of_eq (hPairCard.trans (by omega)))

/-- **The divalent endpoint, when two new occurrences above `A₀` survive.**  It
is a branch vertex: its complete surviving star is those two together with the
retained `e₄`. -/
theorem nonDanglingIncident_old_triple
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor other : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOther : (data.vertexPartition wall).Rel member.geometry.growAnchor other)
    (hCover : ∀ t, (data.vertexPartition wall).Rel member.geometry.growAnchor t →
      member.candidate.newSourceEdge t = member.candidate.newSourceEdge anchor ∨
        member.candidate.newSourceEdge t = member.candidate.newSourceEdge other)
    (hAnchorSurvives :
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge anchor))
    (hOtherSurvives :
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge other)) :
    nonDanglingIncident member.candidate.datum
        (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor) =
      {member.candidate.newSourceEdge anchor, member.candidate.newSourceEdge other,
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.largestTarget
            member.geometry.largestAnchor)} := by
  classical
  apply Finset.Subset.antisymm
  · intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases member.incident_old_cases survival hValid hAnchor hEdgeSurvives
      hEdgeIncident with hLargest | ⟨t, hWall, rfl⟩
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hLargest))
    · rcases hCover t hWall with hEq | hEq
      · exact Finset.mem_insert.mpr (Or.inl hEq)
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hEq))
  · intro edge hMem
    rcases Finset.mem_insert.mp hMem with rfl | hRest
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨hAnchorSurvives, member.new_incident_old anchor⟩
    · rcases Finset.mem_insert.mp hRest with rfl | hLargest
      · refine (mem_nonDanglingIncident _ _ _).mpr ⟨hOtherSurvives, ?_⟩
        have hIncident := member.new_incident_old other
        rwa [member.old_endpoint_eq hOther (hOther.symm.trans hAnchor)] at hIncident
      · rw [Finset.mem_singleton.mp hLargest]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨member.largest_survives_out survival hValid,
            member.largest_incident_old_of_wall_rel hAnchor⟩

/-! ### Survival and stable rows of the new occurrences -/

theorem fresh_grow_nonDanglingValency_eq_two
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hGrow : member.fine.Rel anchor member.geometry.growAnchor)
    (hOtherSep : ¬ member.fine.Rel anchor member.geometry.otherAnchor) :
    nonDanglingValency member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) = 2 := by
  rw [← card_nonDanglingIncident,
    member.nonDanglingIncident_fresh_grow survival hValid hAnchor hGrow hOtherSep]
  exact Finset.card_pair (member.new_ne_old _ _)

theorem fresh_other_nonDanglingValency_eq_two
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOther : member.fine.Rel anchor member.geometry.otherAnchor)
    (hGrowSep : ¬ member.fine.Rel anchor member.geometry.growAnchor) :
    nonDanglingValency member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) = 2 := by
  rw [← card_nonDanglingIncident,
    member.nonDanglingIncident_fresh_other survival hValid hAnchor hOther hGrowSep]
  exact Finset.card_pair (member.new_ne_old _ _)

theorem old_pair_nonDanglingValency_eq_two
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOthers : ∀ t, (data.vertexPartition wall).Rel member.geometry.growAnchor t →
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge t) →
      member.candidate.newSourceEdge t = member.candidate.newSourceEdge anchor) :
    nonDanglingValency member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor) = 2 := by
  rw [← card_nonDanglingIncident,
    member.nonDanglingIncident_old_pair survival hValid hAnchor hOthers]
  exact Finset.card_pair (member.new_ne_old _ _)

theorem new_survives_fresh_grow
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hGrow : member.fine.Rel anchor member.geometry.growAnchor)
    (hOtherSep : ¬ member.fine.Rel anchor member.geometry.otherAnchor) :
    ¬ IsDangling member.candidate.datum
      (member.candidate.newSourceEdge anchor) := by
  have hMem : member.candidate.newSourceEdge anchor ∈
      nonDanglingIncident member.candidate.datum
        (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) := by
    rw [member.nonDanglingIncident_fresh_grow survival hValid hAnchor hGrow hOtherSep]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

theorem new_survives_fresh_other
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOther : member.fine.Rel anchor member.geometry.otherAnchor)
    (hGrowSep : ¬ member.fine.Rel anchor member.geometry.growAnchor) :
    ¬ IsDangling member.candidate.datum
      (member.candidate.newSourceEdge anchor) := by
  have hMem : member.candidate.newSourceEdge anchor ∈
      nonDanglingIncident member.candidate.datum
        (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) := by
    rw [member.nonDanglingIncident_fresh_other survival hValid hAnchor hOther hGrowSep]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

theorem new_survives_old_pair
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOthers : ∀ t, (data.vertexPartition wall).Rel member.geometry.growAnchor t →
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge t) →
      member.candidate.newSourceEdge t = member.candidate.newSourceEdge anchor) :
    ¬ IsDangling member.candidate.datum
      (member.candidate.newSourceEdge anchor) := by
  have hMem : member.candidate.newSourceEdge anchor ∈
      nonDanglingIncident member.candidate.datum
        (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor) := by
    rw [member.nonDanglingIncident_old_pair survival hValid hAnchor hOthers]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

/-- **The new occurrence joins `e₂`'s stable row.** -/
theorem new_stablePath_eq_grow
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hGrow : member.fine.Rel anchor member.geometry.growAnchor)
    (hOtherSep : ¬ member.fine.Rel anchor member.geometry.otherAnchor) :
    NonDanglingEdge.stablePath
        (⟨member.candidate.newSourceEdge anchor,
          member.new_survives_fresh_grow survival hValid hAnchor hGrow hOtherSep⟩ :
          NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨member.candidate.oldSourceEdge
            (data.sourceEdge member.geometry.growTarget
              member.geometry.growAnchor),
          member.grow_survives_out survival hValid⟩ :
          NonDanglingEdge member.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, _, member.new_incident_fresh anchor, ?_,
    member.fresh_grow_nonDanglingValency_eq_two survival hValid hAnchor hGrow
      hOtherSep⟩
  · intro hEq
    exact member.new_ne_old anchor _ (congrArg Subtype.val hEq)
  · have := member.grow_incident_fresh_anchor
    rwa [member.fresh_endpoint_eq hAnchor hGrow]

/-- **The new occurrence joins `e₃`'s stable row.** -/
theorem new_stablePath_eq_other
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOther : member.fine.Rel anchor member.geometry.otherAnchor)
    (hGrowSep : ¬ member.fine.Rel anchor member.geometry.growAnchor) :
    NonDanglingEdge.stablePath
        (⟨member.candidate.newSourceEdge anchor,
          member.new_survives_fresh_other survival hValid hAnchor hOther hGrowSep⟩ :
          NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨member.candidate.oldSourceEdge
            (data.sourceEdge member.geometry.otherTarget
              member.geometry.otherAnchor),
          member.other_survives_out survival hValid⟩ :
          NonDanglingEdge member.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, _, member.new_incident_fresh anchor, ?_,
    member.fresh_other_nonDanglingValency_eq_two survival hValid hAnchor hOther
      hGrowSep⟩
  · intro hEq
    exact member.new_ne_old anchor _ (congrArg Subtype.val hEq)
  · have := member.other_incident_fresh_anchor
    rwa [member.fresh_endpoint_eq hAnchor hOther]

/-- **The new occurrence joins `e₄`'s stable row.** -/
theorem new_stablePath_eq_largest
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOthers : ∀ t, (data.vertexPartition wall).Rel member.geometry.growAnchor t →
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge t) →
      member.candidate.newSourceEdge t = member.candidate.newSourceEdge anchor) :
    NonDanglingEdge.stablePath
        (⟨member.candidate.newSourceEdge anchor,
          member.new_survives_old_pair survival hValid hAnchor hOthers⟩ :
          NonDanglingEdge member.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨member.candidate.oldSourceEdge
            (data.sourceEdge member.geometry.largestTarget
              member.geometry.largestAnchor),
          member.largest_survives_out survival hValid⟩ :
          NonDanglingEdge member.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, _, member.new_incident_old anchor,
    member.largest_incident_old_of_wall_rel hAnchor,
    member.old_pair_nonDanglingValency_eq_two survival hValid hAnchor hOthers⟩
  intro hEq
  exact member.new_ne_old anchor _ (congrArg Subtype.val hEq)

/-! ### Branch vertices -/

/-- **A trivalent endpoint whose class carries both smaller survivors** is a
branch vertex: its complete surviving star is the new occurrence together with
the retained `e₂` and `e₃`. -/
theorem nonDanglingIncident_fresh_triple
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hGrow : member.fine.Rel anchor member.geometry.growAnchor)
    (hOther : member.fine.Rel anchor member.geometry.otherAnchor)
    (hNewSurvives :
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge anchor)) :
    nonDanglingIncident member.candidate.datum
        (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) =
      {member.candidate.newSourceEdge anchor,
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.growTarget member.geometry.growAnchor),
        member.candidate.oldSourceEdge
          (data.sourceEdge member.geometry.otherTarget
            member.geometry.otherAnchor)} := by
  classical
  apply Finset.Subset.antisymm
  · intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases member.incident_fresh_cases survival hValid hAnchor hEdgeSurvives
      hEdgeIncident with hNew | ⟨hOld, _⟩ | ⟨hOld, _⟩
    · exact Finset.mem_insert.mpr (Or.inl hNew)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hOld))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hOld))
  · intro edge hMem
    rcases Finset.mem_insert.mp hMem with rfl | hRest
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨hNewSurvives, member.new_incident_fresh anchor⟩
    · rcases Finset.mem_insert.mp hRest with rfl | hLast
      · refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨member.grow_survives_out survival hValid, ?_⟩
        have := member.grow_incident_fresh_anchor
        rwa [member.fresh_endpoint_eq hAnchor hGrow]
      · rw [Finset.mem_singleton.mp hLast]
        refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨member.other_survives_out survival hValid, ?_⟩
        have := member.other_incident_fresh_anchor
        rwa [member.fresh_endpoint_eq hAnchor hOther]

theorem fresh_triple_nonDanglingValency_eq_three
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hGrow : member.fine.Rel anchor member.geometry.growAnchor)
    (hOther : member.fine.Rel anchor member.geometry.otherAnchor)
    (hNewSurvives :
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge anchor)) :
    nonDanglingValency member.candidate.datum
      (member.candidate.datum.sourceEndpoint (freshVertex target) anchor) = 3 := by
  classical
  rw [← card_nonDanglingIncident, member.nonDanglingIncident_fresh_triple survival
    hValid hAnchor hGrow hOther hNewSurvives]
  rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨member.new_ne_old _ _, member.new_ne_old _ _⟩),
    Finset.card_pair member.old_grow_ne_other]

theorem old_triple_nonDanglingValency_eq_three
    (survival : SelectedSurvival data wall member.geometry) (hValid : data.Valid)
    {anchor other : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel member.geometry.growAnchor anchor)
    (hOther : (data.vertexPartition wall).Rel member.geometry.growAnchor other)
    (hCover : ∀ t, (data.vertexPartition wall).Rel member.geometry.growAnchor t →
      member.candidate.newSourceEdge t = member.candidate.newSourceEdge anchor ∨
        member.candidate.newSourceEdge t = member.candidate.newSourceEdge other)
    (hAnchorSurvives :
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge anchor))
    (hOtherSurvives :
      ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge other))
    (hNewNe : member.candidate.newSourceEdge anchor ≠
      member.candidate.newSourceEdge other) :
    nonDanglingValency member.candidate.datum
      (member.candidate.datum.sourceEndpoint (oldVertex target wall) anchor) = 3 := by
  classical
  rw [← card_nonDanglingIncident, member.nonDanglingIncident_old_triple survival
    hValid hAnchor hOther hCover hAnchorSurvives hOtherSurvives]
  rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hNewNe, member.new_ne_old _ _⟩),
    Finset.card_pair (member.new_ne_old _ _)]

end ReversedMember


/-! ## Figure 28's `M⁽¹⁾`: Position I

`fine` is the two-block split of `A₀` into `e₂` and `e₃`, so **both** selected
new occurrences survive, each at its own valency-two trivalent endpoint, and
the divalent endpoint is the branch vertex.

The declarations below live in this module's own `PositionOne` namespace, so
they are written `new_grow_survives position …` rather than with dot notation
on `W3FourClosure.PositionOne`. -/

namespace PositionOne

variable (position : W3FourClosure.PositionOne data wall)

/-- `M⁽¹⁾` as a member of the reversed pair. -/
noncomputable def toReversedMember : ReversedMember data wall where
  geometry := position.toFourStarGeometry
  fine := position.fine
  fine_refines := position.fine_refines
  grow_refines := position.grow_refines_fine
  other_refines := position.other_refines_fine
  counts := position.rightCounts

/-- It is the member `W3FourClosure` already built. -/
theorem toReversedMember_candidate :
    (toReversedMember position).candidate = position.candidate := rfl

theorem fine_grow_not_other :
    ¬ position.fine.Rel position.growAnchor position.otherAnchor := fun hRel ↦
  position.grow_not_rel_otherAnchor (position.fine_rel_growAnchor_iff.mp hRel)

theorem fine_other_not_grow :
    ¬ position.fine.Rel position.otherAnchor position.growAnchor := fun hRel ↦
  fine_grow_not_other position hRel.symm

/-- The two blocks of `fine` inside `A₀` cover it. -/
theorem fine_cover {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel position.growAnchor sheet) :
    position.fine.Rel position.growAnchor sheet ∨
      position.fine.Rel position.otherAnchor sheet := by
  by_cases hGrow :
      (data.edgePartition position.growTarget).Rel position.growAnchor sheet
  · exact Or.inl (position.fine_rel_growAnchor_iff.mpr hGrow)
  · exact Or.inr (position.fine_rel_otherAnchor_iff.mpr ⟨hSheet, hGrow⟩)

theorem new_grow_ne_new_other :
    position.candidate.newSourceEdge position.growAnchor ≠
      position.candidate.newSourceEdge position.otherAnchor := fun hEq ↦
  fine_grow_not_other position
    (((toReversedMember position).newSourceEdge_eq_iff_fine_rel
      (first := position.growAnchor) (second := position.otherAnchor) rfl).mp hEq)

theorem newSourceEdge_cover {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel position.growAnchor sheet) :
    position.candidate.newSourceEdge sheet =
        position.candidate.newSourceEdge position.growAnchor ∨
      position.candidate.newSourceEdge sheet =
        position.candidate.newSourceEdge position.otherAnchor := by
  rcases fine_cover position hSheet with hRel | hRel
  · exact Or.inl ((toReversedMember position).newSourceEdge_eq_of_fine_rel rfl hRel)
  · exact Or.inr ((toReversedMember position).newSourceEdge_eq_of_fine_rel
      position.other_wall_rel hRel)

/-- **`M⁽¹⁾`'s `e'` survives.** -/
theorem new_grow_survives
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    ¬ IsDangling position.candidate.datum
      (position.candidate.newSourceEdge position.growAnchor) :=
  (toReversedMember position).new_survives_fresh_grow survival hValid rfl rfl
    (fine_grow_not_other position)

/-- **`M⁽¹⁾`'s `e''` survives.** -/
theorem new_other_survives
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    ¬ IsDangling position.candidate.datum
      (position.candidate.newSourceEdge position.otherAnchor) :=
  (toReversedMember position).new_survives_fresh_other survival hValid
    position.other_wall_rel rfl (fine_other_not_grow position)

/-- The trivalent endpoint above `e₂` carries exactly `e'` and the retained
`e₂`. -/
theorem nonDanglingIncident_fresh_grow
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingIncident position.candidate.datum
        (position.candidate.datum.sourceEndpoint (freshVertex target)
          position.growAnchor) =
      {position.candidate.newSourceEdge position.growAnchor,
        position.candidate.oldSourceEdge
          (data.sourceEdge position.growTarget position.growAnchor)} :=
  (toReversedMember position).nonDanglingIncident_fresh_grow survival hValid rfl
    rfl (fine_grow_not_other position)

theorem fresh_grow_nonDanglingValency_eq_two
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingValency position.candidate.datum
      (position.candidate.datum.sourceEndpoint (freshVertex target)
        position.growAnchor) = 2 :=
  (toReversedMember position).fresh_grow_nonDanglingValency_eq_two survival hValid
    rfl rfl (fine_grow_not_other position)

/-- The trivalent endpoint above `e₃` carries exactly `e''` and the retained
`e₃`. -/
theorem nonDanglingIncident_fresh_other
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingIncident position.candidate.datum
        (position.candidate.datum.sourceEndpoint (freshVertex target)
          position.otherAnchor) =
      {position.candidate.newSourceEdge position.otherAnchor,
        position.candidate.oldSourceEdge
          (data.sourceEdge position.otherTarget position.otherAnchor)} :=
  (toReversedMember position).nonDanglingIncident_fresh_other survival hValid
    position.other_wall_rel rfl (fine_other_not_grow position)

theorem fresh_other_nonDanglingValency_eq_two
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingValency position.candidate.datum
      (position.candidate.datum.sourceEndpoint (freshVertex target)
        position.otherAnchor) = 2 :=
  (toReversedMember position).fresh_other_nonDanglingValency_eq_two survival hValid
    position.other_wall_rel rfl (fine_other_not_grow position)

/-- **`e'` lies in `e₂`'s stable row.** -/
theorem new_grow_stablePath
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨position.candidate.newSourceEdge position.growAnchor,
          new_grow_survives position survival hValid⟩ :
          NonDanglingEdge position.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨position.candidate.oldSourceEdge
            (data.sourceEdge position.growTarget position.growAnchor),
          (toReversedMember position).grow_survives_out survival hValid⟩ :
          NonDanglingEdge position.candidate.datum) :=
  (toReversedMember position).new_stablePath_eq_grow survival hValid rfl rfl
    (fine_grow_not_other position)

/-- **`e''` lies in `e₃`'s stable row.** -/
theorem new_other_stablePath
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨position.candidate.newSourceEdge position.otherAnchor,
          new_other_survives position survival hValid⟩ :
          NonDanglingEdge position.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨position.candidate.oldSourceEdge
            (data.sourceEdge position.otherTarget position.otherAnchor),
          (toReversedMember position).other_survives_out survival hValid⟩ :
          NonDanglingEdge position.candidate.datum) :=
  (toReversedMember position).new_stablePath_eq_other survival hValid
    position.other_wall_rel rfl (fine_other_not_grow position)

/-- **The divalent endpoint of `M⁽¹⁾` is the branch vertex**: `e'`, `e''` and
the retained `e₄` all meet there. -/
theorem nonDanglingIncident_old
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingIncident position.candidate.datum
        (position.candidate.datum.sourceEndpoint (oldVertex target wall)
          position.growAnchor) =
      {position.candidate.newSourceEdge position.growAnchor,
        position.candidate.newSourceEdge position.otherAnchor,
        position.candidate.oldSourceEdge
          (data.sourceEdge position.largestTarget position.largestAnchor)} :=
  (toReversedMember position).nonDanglingIncident_old_triple survival hValid rfl
    position.other_wall_rel
    (fun _ hSheet ↦ newSourceEdge_cover position hSheet)
    (new_grow_survives position survival hValid)
    (new_other_survives position survival hValid)

theorem old_nonDanglingValency_eq_three
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingValency position.candidate.datum
      (position.candidate.datum.sourceEndpoint (oldVertex target wall)
        position.growAnchor) = 3 :=
  (toReversedMember position).old_triple_nonDanglingValency_eq_three survival
    hValid rfl position.other_wall_rel
    (fun _ hSheet ↦ newSourceEdge_cover position hSheet)
    (new_grow_survives position survival hValid)
    (new_other_survives position survival hValid)
    (new_grow_ne_new_other position)

end PositionOne

/-! ## Figure 28's `M⁽²⁾`: Position II.b

`fine` detaches one sheet of `A₀` from the rest, so the **singleton new
occurrence dangles** -- both old directions are singleton-refined there, and a
surviving new occurrence would leave that endpoint with surviving valency one.
The big new occurrence then survives at the divalent endpoint, which is
therefore *not* a branch vertex; the trivalent endpoint above `A⁽²⁾` is. -/

namespace PositionTwo

variable (position : W3FourClosure.PositionTwo data wall)

/-- `M⁽²⁾` as a member of the reversed pair. -/
noncomputable def toReversedMember : ReversedMember data wall where
  geometry := position.toFourStarGeometry
  fine := position.fine
  fine_refines := position.fine_refines
  grow_refines := position.grow_refines_fine
  other_refines := position.other_refines_fine
  counts := position.rightCounts

/-- It is the member `W3FourClosure` already built. -/
theorem toReversedMember_candidate :
    (toReversedMember position).candidate = position.candidate := rfl

theorem fine_grow_not_outside :
    ¬ position.fine.Rel position.growAnchor position.outside := fun hRel ↦
  (position.fine_rel_growAnchor_iff.mp hRel).1 rfl

theorem fine_outside_not_grow :
    ¬ position.fine.Rel position.outside position.growAnchor := fun hRel ↦
  fine_grow_not_outside position hRel.symm

theorem fine_grow_other :
    position.fine.Rel position.growAnchor position.otherAnchor :=
  position.fine_rel_growAnchor_iff.mpr
    ⟨fun hEq ↦ position.outside_ne_otherAnchor hEq.symm, position.other_wall_rel⟩

theorem fine_outside_not_other :
    ¬ position.fine.Rel position.outside position.otherAnchor := fun hRel ↦
  fine_grow_not_outside position ((fine_grow_other position).trans hRel.symm)

/-- **The detached singleton new occurrence of `M⁽²⁾` dangles.**  Position
II.b's outside sheet lies outside both `e₂` and `e₃`, so both old directions
are singleton-refined there and every old occurrence at that trivalent
endpoint is pruned. -/
theorem new_outside_dangles
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    IsDangling position.candidate.datum
      (position.candidate.newSourceEdge position.outside) :=
  (toReversedMember position).new_isDangling_of_fresh_separate survival hValid
    position.outside_wall (fine_outside_not_grow position)
    (fine_outside_not_other position)

/-- The detached trivalent endpoint is entirely pruned. -/
theorem nonDanglingIncident_fresh_outside
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingIncident position.candidate.datum
      (position.candidate.datum.sourceEndpoint (freshVertex target)
        position.outside) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro edge hMem
  obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases (toReversedMember position).incident_fresh_cases survival hValid
    position.outside_wall hSurvives hIncident with hNew | ⟨_, hRel⟩ | ⟨_, hRel⟩
  · exact hSurvives (by
      rw [hNew]; exact new_outside_dangles position survival hValid)
  · exact fine_outside_not_grow position hRel
  · exact fine_outside_not_other position hRel

theorem fresh_outside_nonDanglingValency_eq_zero
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingValency position.candidate.datum
      (position.candidate.datum.sourceEndpoint (freshVertex target)
        position.outside) = 0 := by
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_fresh_outside position survival hValid,
    Finset.card_empty]

/-- Every surviving new occurrence of `M⁽²⁾` above `A₀` is the big one. -/
theorem newSourceEdge_eq_of_survives
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel position.growAnchor sheet)
    (hSurvives : ¬ IsDangling position.candidate.datum
      (position.candidate.newSourceEdge sheet)) :
    position.candidate.newSourceEdge sheet =
      position.candidate.newSourceEdge position.growAnchor := by
  by_cases hOutside : sheet = position.outside
  · subst sheet
    exact absurd (new_outside_dangles position survival hValid) hSurvives
  · exact (toReversedMember position).newSourceEdge_eq_of_fine_rel rfl
      (position.fine_rel_growAnchor_iff.mpr ⟨hOutside, hSheet⟩)

/-- **`M⁽²⁾`'s `e'` survives.**  The divalent endpoint carries the dangling
singleton and the retained `e₄`, so surviving valency one would follow if `e'`
dangled too. -/
theorem new_grow_survives
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    ¬ IsDangling position.candidate.datum
      (position.candidate.newSourceEdge position.growAnchor) :=
  (toReversedMember position).new_survives_old_pair survival hValid rfl
    (fun sheet hSheet hSurvives ↦
      newSourceEdge_eq_of_survives position survival hValid sheet hSheet hSurvives)

/-- **The divalent endpoint of `M⁽²⁾` is not a branch vertex**: it carries
exactly `e'` and the retained `e₄`. -/
theorem nonDanglingIncident_old
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingIncident position.candidate.datum
        (position.candidate.datum.sourceEndpoint (oldVertex target wall)
          position.growAnchor) =
      {position.candidate.newSourceEdge position.growAnchor,
        position.candidate.oldSourceEdge
          (data.sourceEdge position.largestTarget position.largestAnchor)} :=
  (toReversedMember position).nonDanglingIncident_old_pair survival hValid rfl
    (fun sheet hSheet hSurvives ↦
      newSourceEdge_eq_of_survives position survival hValid sheet hSheet hSurvives)

theorem old_nonDanglingValency_eq_two
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingValency position.candidate.datum
      (position.candidate.datum.sourceEndpoint (oldVertex target wall)
        position.growAnchor) = 2 :=
  (toReversedMember position).old_pair_nonDanglingValency_eq_two survival hValid
    rfl (fun sheet hSheet hSurvives ↦
      newSourceEdge_eq_of_survives position survival hValid sheet hSheet hSurvives)

/-- **`e'` lies in `e₄`'s stable row**, which is Figure 28's `σ₀(J₀,4)` row for
`M⁽²⁾`. -/
theorem new_grow_stablePath
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨position.candidate.newSourceEdge position.growAnchor,
          new_grow_survives position survival hValid⟩ :
          NonDanglingEdge position.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨position.candidate.oldSourceEdge
            (data.sourceEdge position.largestTarget position.largestAnchor),
          (toReversedMember position).largest_survives_out survival hValid⟩ :
          NonDanglingEdge position.candidate.datum) :=
  (toReversedMember position).new_stablePath_eq_largest survival hValid rfl
    (fun sheet hSheet hSurvives ↦
      newSourceEdge_eq_of_survives position survival hValid sheet hSheet hSurvives)

/-- **The trivalent endpoint above `A⁽²⁾` is the branch vertex**: `e'` and the
retained `e₂`, `e₃` all meet there. -/
theorem nonDanglingIncident_fresh_grow
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingIncident position.candidate.datum
        (position.candidate.datum.sourceEndpoint (freshVertex target)
          position.growAnchor) =
      {position.candidate.newSourceEdge position.growAnchor,
        position.candidate.oldSourceEdge
          (data.sourceEdge position.growTarget position.growAnchor),
        position.candidate.oldSourceEdge
          (data.sourceEdge position.otherTarget position.otherAnchor)} :=
  (toReversedMember position).nonDanglingIncident_fresh_triple survival hValid rfl
    rfl (fine_grow_other position) (new_grow_survives position survival hValid)

theorem fresh_grow_nonDanglingValency_eq_three
    (survival : SelectedSurvival data wall position.toFourStarGeometry)
    (hValid : data.Valid) :
    nonDanglingValency position.candidate.datum
      (position.candidate.datum.sourceEndpoint (freshVertex target)
        position.growAnchor) = 3 :=
  (toReversedMember position).fresh_triple_nonDanglingValency_eq_three survival
    hValid rfl rfl (fine_grow_other position)
    (new_grow_survives position survival hValid)

end PositionTwo

/-- The divalent-endpoint counterpart of
`W3Nd3StableGraph.old_incident_fresh_sheet_rel_local`: an old occurrence
incident to a retained endpoint has its sheet in that endpoint's class.  Stated
here, with a `_local` suffix, rather than in `W3Nd3StableGraph` beside its
counterpart. -/
theorem old_incident_old_sheet_rel_local
    (candidate : Candidate target degree data wall)
    (anchor : Fin degree) (old : data.SourceEdge)
    (hIncident : Incident candidate.datum (candidate.oldSourceEdge old)
      (candidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
        candidate.contracts).left.Rel anchor old.1.2 := by
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.oldSourceEdge old)
    (candidate.datum.sourceEndpoint (oldVertex target wall) anchor)).mp hIncident
  simp only [BalancedGlobal.Candidate.oldSourceEdge_target,
    BalancedGlobal.Candidate.oldSourceEdge_sheet,
    BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GluingDatum.sourceEndpoint,
    GlobalResolution.datum_vertexPartition_old_wall] at hOutgoing
  change occurrenceEquiv target wall candidate.right (some old.1.1) ∈
      GluingDatum.incidentEdges (oldVertex target wall) ∧
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
      candidate.contracts).left.Rel
      ((LocalResolution.paste (data.vertexPartition wall) candidate.resolution
        candidate.contracts).left.repr anchor) old.1.2 at hOutgoing
  exact ((LocalResolution.paste (data.vertexPartition wall) candidate.resolution
    candidate.contracts).left.rel_repr_right anchor).trans hOutgoing.2

/-! ## Figure 28's `M⁽³⁾` and `M⁽⁴⁾`: the grow members

Position II.a is oriented the other way round: the refinement `growPartition`
(the class `e₂` enlarged by one transferred sheet, singletons elsewhere) sits at
the **divalent** endpoint beside `t₂`, and the whole block `A₀` sits at the
**trivalent** one beside `t₃` and `t₄`.  So the row identification happens at
the divalent endpoint and the trivalent endpoint is the branch vertex -- the
mirror image of `M⁽¹⁾`.

`M⁽⁴⁾` is `M⁽³⁾` with `grow` and `other` exchanged
(`W3FourSourceCandidates.growProfileSecond`), so everything below is stated for
an arbitrary `GrowProfile` and applies to both. -/

namespace GrowMember

variable {star : ThreeStar target wall} {input : W3SourceInput data star}
  (grown : GrowProfile input)

/-- The pasted local resolution of a grow member. -/
noncomputable def pasted : LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall) grown.growCandidate.resolution
    grown.growCandidate.contracts

theorem candidate_valid (hValid : data.Valid) :
    grown.growCandidate.datum.Valid :=
  grown.growCandidate.datum_valid hValid

/-! ### Side assignment -/

theorem right_grow : grown.growCandidate.right grown.growTarget = false := by
  show W3Nd2SourceCandidates.rightOf grown.growTarget grown.growTarget = false
  simp [W3Nd2SourceCandidates.rightOf]

theorem right_other : grown.growCandidate.right grown.otherTarget = true := by
  show W3Nd2SourceCandidates.rightOf grown.growTarget grown.otherTarget = true
  simp [W3Nd2SourceCandidates.rightOf, Ne.symm grown.grow_target_ne_other]

theorem right_largest : grown.growCandidate.right grown.largestTarget = true := by
  show W3Nd2SourceCandidates.rightOf grown.growTarget grown.largestTarget = true
  simp [W3Nd2SourceCandidates.rightOf, Ne.symm grown.grow_target_ne_largest]

/-! ### The pasted endpoint dictionary -/

theorem resolution_selected {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet) :
    grown.growCandidate.resolution sheet =
      fineResolution (data.vertexPartition wall) grown.growPartition
        grown.growPartition_refines := by
  rw [show grown.growCandidate.resolution sheet =
      LocalResolution.onBlock (data.vertexPartition wall) grown.growAnchor
        (fineResolution (data.vertexPartition wall) grown.growPartition
          grown.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition grown.growTarget) grown.growTarget_refines)
        sheet from rfl,
    LocalResolution.onBlock_of_rel _ _ _ _ _ hSheet]

theorem pasted_left_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet) :
    (pasted grown).left.block sheet = grown.growPartition.block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    grown.growCandidate.resolution grown.growCandidate.contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [resolution_selected grown
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem pasted_right_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet) :
    (pasted grown).right.block sheet = (data.vertexPartition wall).block sheet := by
  change (LocalResolution.pasteRight (data.vertexPartition wall)
    grown.growCandidate.resolution grown.growCandidate.contracts).block sheet = _
  unfold LocalResolution.pasteRight
  rw [(data.vertexPartition wall).paste_block]
  rw [resolution_selected grown
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

theorem pasted_newEdge_block {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet) :
    (pasted grown).newEdge.block sheet = grown.growPartition.block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    grown.growCandidate.resolution grown.growCandidate.contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [resolution_selected grown
    (hSheet.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

/-! ### Occurrences and incidences -/

theorem old_isDangling_iff (hValid : data.Valid) (edge : data.SourceEdge) :
    IsDangling grown.growCandidate.datum (grown.growCandidate.oldSourceEdge edge) ↔
      IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff grown.growCandidate hValid
    (GrowProfile.growCandidate_sourceGenus grown) edge

theorem new_ne_old (sheet : Fin degree) (edge : data.SourceEdge) :
    grown.growCandidate.newSourceEdge sheet ≠
      grown.growCandidate.oldSourceEdge edge := by
  intro hEqual
  have hTargets := congrArg
    (fun item : grown.growCandidate.datum.SourceEdge ↦ item.1.1) hEqual
  have hLabels :=
    (occurrenceEquiv target wall grown.growCandidate.right).injective hTargets
  cases hLabels

theorem new_incident_old (sheet : Fin degree) :
    Incident grown.growCandidate.datum (grown.growCandidate.newSourceEdge sheet)
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    grown.growCandidate.right (pasted grown)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ grown.growCandidate.exterior)
    sheet))

theorem new_incident_fresh (sheet : Fin degree) :
    Incident grown.growCandidate.datum (grown.growCandidate.newSourceEdge sheet)
      (grown.growCandidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
    grown.growCandidate.right (pasted grown)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ grown.growCandidate.exterior)
    sheet))

theorem grow_incident_old (sheet : Fin degree) :
    Incident grown.growCandidate.datum
        (grown.growCandidate.oldSourceEdge (data.sourceEdge grown.growTarget sheet))
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  W3Nd2Survival.oldSourceEdge_incident_old grown.growCandidate grown.growTarget
    grown.growTarget_mem (right_grow grown) sheet

theorem other_incident_fresh (sheet : Fin degree) :
    Incident grown.growCandidate.datum
        (grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.otherTarget sheet))
      (grown.growCandidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  M11SplitSurvival.oldSourceEdge_incident_fresh grown.growCandidate
    grown.otherTarget grown.otherTarget_mem (right_other grown) sheet

theorem largest_incident_fresh (sheet : Fin degree) :
    Incident grown.growCandidate.datum
        (grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.largestTarget sheet))
      (grown.growCandidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  M11SplitSurvival.oldSourceEdge_incident_fresh grown.growCandidate
    grown.largestTarget grown.largestTarget_mem (right_largest grown) sheet

theorem old_endpoint_eq {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel grown.growAnchor first)
    (hRel : grown.growPartition.Rel first second) :
    grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) first =
      grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (grown.growCandidate.datum.vertexPartition
        (oldVertex target wall)).repr first =
      (grown.growCandidate.datum.vertexPartition (oldVertex target wall)).repr second
    rw [show grown.growCandidate.datum.vertexPartition (oldVertex target wall) =
        (pasted grown).left from
      GlobalResolution.expandedVertexPartition_old_wall data wall _]
    have hMem : second ∈ grown.growPartition.block first :=
      (grown.growPartition.mem_block_iff first second).mpr hRel
    rw [← pasted_left_block grown hFirst] at hMem
    exact ((pasted grown).left.mem_block_iff first second).mp hMem

theorem fresh_endpoint_eq {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel grown.growAnchor first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    grown.growCandidate.datum.sourceEndpoint (freshVertex target) first =
      grown.growCandidate.datum.sourceEndpoint (freshVertex target) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (pasted grown).right.repr first = (pasted grown).right.repr second
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← pasted_right_block grown hFirst] at hMem
    exact ((pasted grown).right.mem_block_iff first second).mp hMem

theorem newSourceEdge_eq_of_rel {first second : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel grown.growAnchor first)
    (hRel : grown.growPartition.Rel first second) :
    grown.growCandidate.newSourceEdge second =
      grown.growCandidate.newSourceEdge first := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (pasted grown).newEdge.repr second = (pasted grown).newEdge.repr first
    have hMem : second ∈ grown.growPartition.block first :=
      (grown.growPartition.mem_block_iff first second).mpr hRel
    rw [← pasted_newEdge_block grown hFirst] at hMem
    exact (((pasted grown).newEdge.mem_block_iff first second).mp hMem).symm

/-! ### The two endpoint classifications -/

/-- The distinguished wall block of a grow member. -/
noncomputable def selectedBlock : WallBlock data wall :=
  WallBlock.ofSheet data wall grown.growAnchor

theorem selectedBlock_rel {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet) :
    (data.vertexPartition wall).Rel (selectedBlock grown).1 sheet :=
  ((data.vertexPartition wall).rel_repr_left grown.growAnchor).trans hSheet

theorem sourceVertex_selectedBlock :
    WallBlock.sourceVertex data wall (selectedBlock grown) =
      data.sourceEndpoint wall grown.growAnchor := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (data.vertexPartition wall).repr_idem grown.growAnchor

/-- **The divalent endpoint.**  Only `t₂` is present there, and `e₂` is its
only survivor above `A₀`. -/
theorem incident_old_cases
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel grown.growAnchor anchor)
    {edge : grown.growCandidate.datum.SourceEdge}
    (hSurvives : ¬ IsDangling grown.growCandidate.datum edge)
    (hIncident : Incident grown.growCandidate.datum edge
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    edge = grown.growCandidate.newSourceEdge anchor ∨
      (edge = grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.growTarget grown.growAnchor) ∧
        grown.growPartition.Rel anchor grown.growAnchor) := by
  rcases ResolutionPruning.sourceEdge_cases grown.growCandidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · obtain ⟨hData, hRight⟩ :=
      W3Nd3StableGraph.old_incident_old_selected_info_local grown.growCandidate
        (selectedBlock grown) anchor (selectedBlock_rel grown hAnchor) old hIncident
    rw [sourceVertex_selectedBlock grown] at hData
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((old_isDangling_iff grown hValid old).mpr hDangling)
    have hSheetRel := old_incident_old_sheet_rel_local grown.growCandidate anchor
      old hIncident
    have hMem : old.1.2 ∈ (pasted grown).left.block anchor :=
      ((pasted grown).left.mem_block_iff _ _).mpr hSheetRel
    rw [pasted_left_block grown hAnchor] at hMem
    have hGrowRel : grown.growPartition.Rel anchor old.1.2 :=
      (grown.growPartition.mem_block_iff _ _).mp hMem
    rcases survival.exhaustive old hData hOldSurvives with rfl | rfl | rfl
    · exact Or.inr ⟨rfl, hGrowRel.trans (grown.growTarget_refines_growPartition.rel
        ((data.edgePartition grown.growTarget).rel_repr_left grown.growAnchor))⟩
    · exact Bool.noConfusion ((right_other grown).symm.trans hRight)
    · exact Bool.noConfusion ((right_largest grown).symm.trans hRight)
  · left
    have hSheetRel := W3Nd3StableGraph.new_incident_old_sheet_rel_local
      grown.growCandidate anchor new hIncident
    have hMem : (pasted grown).newEdge.repr new ∈ (pasted grown).left.block anchor :=
      ((pasted grown).left.mem_block_iff _ _).mpr hSheetRel
    rw [pasted_left_block grown hAnchor, ← pasted_newEdge_block grown hAnchor]
      at hMem
    have hNewRel := ((pasted grown).newEdge.mem_block_iff anchor _).mp hMem
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (pasted grown).newEdge.repr new = (pasted grown).newEdge.repr anchor
      exact ((pasted grown).newEdge.repr_idem new).symm.trans hNewRel.symm

/-- **The trivalent endpoint.**  `t₃` and `t₄` are present there, with
survivors `e₃`, `e₄`; every other survivor is one of the member's own new
occurrences above `A₀`. -/
theorem incident_fresh_cases
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel grown.growAnchor anchor)
    {edge : grown.growCandidate.datum.SourceEdge}
    (hSurvives : ¬ IsDangling grown.growCandidate.datum edge)
    (hIncident : Incident grown.growCandidate.datum edge
      (grown.growCandidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    (∃ sheet : Fin degree,
        (data.vertexPartition wall).Rel grown.growAnchor sheet ∧
          edge = grown.growCandidate.newSourceEdge sheet) ∨
      edge = grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.otherTarget grown.otherAnchor) ∨
      edge = grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.largestTarget grown.largestAnchor) := by
  rcases ResolutionPruning.sourceEdge_cases grown.growCandidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · obtain ⟨hData, hRight⟩ :=
      W3Nd2EndRows.old_incident_fresh_selected_info grown.growCandidate
        (selectedBlock grown) anchor (selectedBlock_rel grown hAnchor) old hIncident
    rw [sourceVertex_selectedBlock grown] at hData
    have hOldSurvives : ¬ IsDangling data old := fun hDangling ↦
      hSurvives ((old_isDangling_iff grown hValid old).mpr hDangling)
    rcases survival.exhaustive old hData hOldSurvives with rfl | rfl | rfl
    · exact Bool.noConfusion ((right_grow grown).symm.trans hRight)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · left
    have hOutgoing := (incident_iff_target_mem_and_rel grown.growCandidate.datum
      (grown.growCandidate.newSourceEdge new)
      (grown.growCandidate.datum.sourceEndpoint (freshVertex target) anchor)).mp
      hIncident
    change occurrenceEquiv target wall grown.growCandidate.right none ∈
        GluingDatum.incidentEdges (freshVertex target) ∧
      (pasted grown).right.Rel ((pasted grown).right.repr anchor)
        ((pasted grown).newEdge.repr new) at hOutgoing
    have hRightRel : (pasted grown).right.Rel anchor
        ((pasted grown).newEdge.repr new) :=
      ((pasted grown).right.rel_repr_right anchor).trans hOutgoing.2
    have hMem : (pasted grown).newEdge.repr new ∈
        (pasted grown).right.block anchor :=
      ((pasted grown).right.mem_block_iff _ _).mpr hRightRel
    rw [pasted_right_block grown hAnchor] at hMem
    refine ⟨(pasted grown).newEdge.repr new,
      hAnchor.trans (((data.vertexPartition wall).mem_block_iff _ _).mp hMem), ?_⟩
    exact (W3Nd3StableGraph.newSourceEdge_repr_local grown.growCandidate new).symm

/-! ### The census of a grow member -/

theorem grow_survives_out
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    ¬ IsDangling grown.growCandidate.datum
      (grown.growCandidate.oldSourceEdge
        (data.sourceEdge grown.growTarget grown.growAnchor)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge grown.growCandidate hValid.1 _
    survival.grow_survives

theorem other_survives_out
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    ¬ IsDangling grown.growCandidate.datum
      (grown.growCandidate.oldSourceEdge
        (data.sourceEdge grown.otherTarget grown.otherAnchor)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge grown.growCandidate hValid.1 _
    survival.other_survives

theorem largest_survives_out
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    ¬ IsDangling grown.growCandidate.datum
      (grown.growCandidate.oldSourceEdge
        (data.sourceEdge grown.largestTarget grown.largestAnchor)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge grown.growCandidate hValid.1 _
    survival.largest_survives

theorem other_wall_rel :
    (data.vertexPartition wall).Rel grown.growAnchor grown.otherAnchor :=
  grown.growAnchor_wall_rel.symm.trans grown.otherAnchor_wall_rel

theorem largest_wall_rel :
    (data.vertexPartition wall).Rel grown.growAnchor grown.largestAnchor :=
  grown.growAnchor_wall_rel.symm.trans grown.largestAnchor_wall_rel

theorem old_other_ne_largest :
    grown.growCandidate.oldSourceEdge
        (data.sourceEdge grown.otherTarget grown.otherAnchor) ≠
      grown.growCandidate.oldSourceEdge
        (data.sourceEdge grown.largestTarget grown.largestAnchor) := by
  intro hEq
  have hSource : data.sourceEdge grown.otherTarget grown.otherAnchor =
      data.sourceEdge grown.largestTarget grown.largestAnchor :=
    W3Nd3StableGraph.oldSourceEdge_injective_local
      (first := data.sourceEdge grown.otherTarget grown.otherAnchor)
      (second := data.sourceEdge grown.largestTarget grown.largestAnchor)
      grown.growCandidate hEq
  have hTargetEq :
      (data.sourceEdge grown.otherTarget grown.otherAnchor).1.1 =
        (data.sourceEdge grown.largestTarget grown.largestAnchor).1.1 :=
    congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hSource
  exact grown.other_target_ne_largest hTargetEq

/-- **Every selected new occurrence of a grow member outside the enlarged
class dangles.**  Its divalent endpoint is a singleton class of
`growPartition`, and the only old occurrence there is the singleton `t₂` class
of that sheet, which is pruned. -/
theorem new_dangles_of_separate
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet)
    (hSep : ¬ grown.growPartition.Rel sheet grown.growAnchor) :
    IsDangling grown.growCandidate.datum
      (grown.growCandidate.newSourceEdge sheet) := by
  classical
  by_contra hSurvives
  have hSubset : nonDanglingIncident grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) sheet) ⊆
      {grown.growCandidate.newSourceEdge sheet} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases incident_old_cases grown survival hValid hSheet hEdgeSurvives
      hEdgeIncident with hNew | ⟨_, hRel⟩
    · exact Finset.mem_singleton.mpr hNew
    · exact absurd hRel hSep
  have hLe := (Finset.card_le_card hSubset).trans_eq (Finset.card_singleton _)
  have hPos : 0 < (nonDanglingIncident grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) sheet)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨hSurvives, new_incident_old grown sheet⟩⟩
  have hNe : (nonDanglingIncident grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) sheet)).card
        ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one grown.growCandidate.datum
      (candidate_valid grown hValid).1
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) sheet)
  omega

/-- Those divalent endpoints are entirely pruned. -/
theorem nonDanglingIncident_old_separate
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel grown.growAnchor sheet)
    (hSep : ¬ grown.growPartition.Rel sheet grown.growAnchor) :
    nonDanglingIncident grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall) sheet)
        = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro edge hMem
  obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases incident_old_cases grown survival hValid hSheet hEdgeSurvives
    hEdgeIncident with hNew | ⟨_, hRel⟩
  · exact hEdgeSurvives (by
      rw [hNew]; exact new_dangles_of_separate grown survival hValid hSheet hSep)
  · exact hSep hRel

/-- **The divalent endpoint of a grow member above `e₂`.**  Its complete
surviving star is the enlarged new occurrence together with the retained `e₂`;
in particular that new occurrence survives. -/
theorem nonDanglingIncident_old_grow
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    nonDanglingIncident grown.growCandidate.datum
        (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
          grown.growAnchor) =
      {grown.growCandidate.newSourceEdge grown.growAnchor,
        grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.growTarget grown.growAnchor)} := by
  classical
  have hSubset : nonDanglingIncident grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
        grown.growAnchor) ⊆
      {grown.growCandidate.newSourceEdge grown.growAnchor,
        grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.growTarget grown.growAnchor)} := by
    intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases incident_old_cases grown survival hValid rfl hEdgeSurvives
      hEdgeIncident with hNew | ⟨hOld, _⟩
    · exact Finset.mem_insert.mpr (Or.inl hNew)
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hOld)
  have hPairCard : ({grown.growCandidate.newSourceEdge grown.growAnchor,
      grown.growCandidate.oldSourceEdge
        (data.sourceEdge grown.growTarget grown.growAnchor)} :
      Finset grown.growCandidate.datum.SourceEdge).card = 2 :=
    Finset.card_pair (new_ne_old grown _ _)
  have hPos : 0 < (nonDanglingIncident grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
        grown.growAnchor)).card :=
    Finset.card_pos.mpr ⟨_, (mem_nonDanglingIncident _ _ _).mpr
      ⟨grow_survives_out grown survival hValid,
        grow_incident_old grown grown.growAnchor⟩⟩
  have hLe := (Finset.card_le_card hSubset).trans_eq hPairCard
  have hNe : (nonDanglingIncident grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
        grown.growAnchor)).card ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one grown.growCandidate.datum
      (candidate_valid grown hValid).1
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
        grown.growAnchor)
  exact Finset.eq_of_subset_of_card_le hSubset
    (le_of_eq (hPairCard.trans (by omega)))

theorem old_grow_nonDanglingValency_eq_two
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    nonDanglingValency grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
        grown.growAnchor) = 2 := by
  rw [← card_nonDanglingIncident,
    nonDanglingIncident_old_grow grown survival hValid]
  exact Finset.card_pair (new_ne_old grown _ _)

/-- **The enlarged new occurrence of a grow member survives.** -/
theorem new_grow_survives
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    ¬ IsDangling grown.growCandidate.datum
      (grown.growCandidate.newSourceEdge grown.growAnchor) := by
  have hMem : grown.growCandidate.newSourceEdge grown.growAnchor ∈
      nonDanglingIncident grown.growCandidate.datum
        (grown.growCandidate.datum.sourceEndpoint (oldVertex target wall)
          grown.growAnchor) := by
    rw [nonDanglingIncident_old_grow grown survival hValid]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1

/-- **It lies in `e₂`'s stable row**, which is Figure 28's `σ₀(J₀,2)` row for
`M⁽³⁾` (and `σ₀(J₀,3)` for `M⁽⁴⁾`). -/
theorem new_grow_stablePath
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    NonDanglingEdge.stablePath
        (⟨grown.growCandidate.newSourceEdge grown.growAnchor,
          new_grow_survives grown survival hValid⟩ :
          NonDanglingEdge grown.growCandidate.datum) =
      NonDanglingEdge.stablePath
        (⟨grown.growCandidate.oldSourceEdge
            (data.sourceEdge grown.growTarget grown.growAnchor),
          grow_survives_out grown survival hValid⟩ :
          NonDanglingEdge grown.growCandidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, _,
    new_incident_old grown grown.growAnchor,
    grow_incident_old grown grown.growAnchor,
    old_grow_nonDanglingValency_eq_two grown survival hValid⟩
  intro hEq
  exact new_ne_old grown grown.growAnchor _ (congrArg Subtype.val hEq)

/-- **The trivalent endpoint of a grow member is the branch vertex**: the
enlarged new occurrence and the retained `e₃`, `e₄` all meet there. -/
theorem nonDanglingIncident_fresh
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    nonDanglingIncident grown.growCandidate.datum
        (grown.growCandidate.datum.sourceEndpoint (freshVertex target)
          grown.growAnchor) =
      {grown.growCandidate.newSourceEdge grown.growAnchor,
        grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.otherTarget grown.otherAnchor),
        grown.growCandidate.oldSourceEdge
          (data.sourceEdge grown.largestTarget grown.largestAnchor)} := by
  classical
  apply Finset.Subset.antisymm
  · intro edge hMem
    obtain ⟨hEdgeSurvives, hEdgeIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases incident_fresh_cases grown survival hValid rfl hEdgeSurvives
      hEdgeIncident with ⟨sheet, hWall, rfl⟩ | hOther | hLargest
    · refine Finset.mem_insert.mpr (Or.inl ?_)
      by_cases hRel : grown.growPartition.Rel sheet grown.growAnchor
      · exact newSourceEdge_eq_of_rel grown rfl hRel.symm
      · exact absurd (new_dangles_of_separate grown survival hValid hWall hRel)
          hEdgeSurvives
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl hOther))
    · exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hLargest))
  · intro edge hMem
    rcases Finset.mem_insert.mp hMem with rfl | hRest
    · exact (mem_nonDanglingIncident _ _ _).mpr
        ⟨new_grow_survives grown survival hValid,
          new_incident_fresh grown grown.growAnchor⟩
    · rcases Finset.mem_insert.mp hRest with rfl | hLast
      · refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨other_survives_out grown survival hValid, ?_⟩
        have hIncident := other_incident_fresh grown grown.otherAnchor
        rwa [fresh_endpoint_eq grown rfl (other_wall_rel grown)]
      · rw [Finset.mem_singleton.mp hLast]
        refine (mem_nonDanglingIncident _ _ _).mpr
          ⟨largest_survives_out grown survival hValid, ?_⟩
        have hIncident := largest_incident_fresh grown grown.largestAnchor
        rwa [fresh_endpoint_eq grown rfl (largest_wall_rel grown)]

theorem fresh_nonDanglingValency_eq_three
    (survival : SelectedSurvival data wall (W3FourClosure.ofGrowProfile grown))
    (hValid : data.Valid) :
    nonDanglingValency grown.growCandidate.datum
      (grown.growCandidate.datum.sourceEndpoint (freshVertex target)
        grown.growAnchor) = 3 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_fresh grown survival hValid]
  rw [Finset.card_insert_of_notMem (by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨new_ne_old grown _ _, new_ne_old grown _ _⟩),
    Finset.card_pair (old_other_ne_largest grown)]

end GrowMember

/-! ## The background wall blocks

Above every wall block other than `A₀` all four members install one surviving
direction's **own** edge partition on the new edge and at the endpoint that
direction is assigned to.  So each background new occurrence has one old
representative -- the `t_α` occurrence through the same sheet -- and carries
its pruning status, its stable row and its index.  `t_α` is `t₄` for `M⁽¹⁾`,
`M⁽²⁾` and the grow direction for `M⁽³⁾`, `M⁽⁴⁾`, exactly as
`W3FourStableGraph.reversedCandidate_newIndex_background` and
`growCandidate_newIndex_background` record. -/

/-- What a member looks like away from the distinguished wall block. -/
structure BackgroundShape (data : GluingDatum target degree) (wall : target.V) where
  /-- The member. -/
  candidate : Candidate target degree data wall
  /-- `t_α`: the direction resolving the background. -/
  backgroundTarget : target.edges
  target_mem : backgroundTarget ∈ GluingDatum.incidentEdges wall
  /-- `t_α` sits at the retained endpoint. -/
  left : candidate.right backgroundTarget = false
  /-- and is the only wall direction there. -/
  unique : ∀ edge : target.edges, candidate.right edge = false →
    edge = backgroundTarget
  /-- The distinguished block's anchor. -/
  selected : Fin degree
  /-- Off that block the member is `t_α`'s own fine star. -/
  resolution_eq : ∀ sheet : Fin degree,
    ¬ (data.vertexPartition wall).Rel selected sheet →
      candidate.resolution sheet =
        fineResolution (data.vertexPartition wall)
          (data.edgePartition backgroundTarget)
          (refines_of_mem_incidentEdges data target_mem)
  genus_eq : genus candidate.datum.sourceGraph = genus data.sourceGraph

namespace BackgroundShape

variable (shape : BackgroundShape data wall)

/-- The pasted local resolution of the member. -/
noncomputable def pasted : LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall) shape.candidate.resolution
    shape.candidate.contracts

theorem pasted_left_block {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    shape.pasted.left.block sheet =
      (data.edgePartition shape.backgroundTarget).block sheet := by
  change (LocalResolution.pasteLeft (data.vertexPartition wall)
    shape.candidate.resolution shape.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteLeft
  rw [(data.vertexPartition wall).paste_block]
  rw [shape.resolution_eq ((data.vertexPartition wall).repr sheet) (fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem pasted_newEdge_block {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    shape.pasted.newEdge.block sheet =
      (data.edgePartition shape.backgroundTarget).block sheet := by
  change (LocalResolution.pasteNewEdge (data.vertexPartition wall)
    shape.candidate.resolution shape.candidate.contracts).block sheet = _
  unfold LocalResolution.pasteNewEdge
  rw [(data.vertexPartition wall).paste_block]
  rw [shape.resolution_eq ((data.vertexPartition wall).repr sheet) (fun hRel ↦
    hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet)))]
  rfl

theorem old_isDangling_iff (hValid : data.Valid) (edge : data.SourceEdge) :
    IsDangling shape.candidate.datum (shape.candidate.oldSourceEdge edge) ↔
      IsDangling data edge :=
  ResolutionPruning.isDangling_oldSourceEdge_iff shape.candidate hValid
    shape.genus_eq edge

theorem new_ne_old (sheet : Fin degree) (edge : data.SourceEdge) :
    shape.candidate.newSourceEdge sheet ≠
      shape.candidate.oldSourceEdge edge := by
  intro hEqual
  have hTargets := congrArg
    (fun item : shape.candidate.datum.SourceEdge ↦ item.1.1) hEqual
  have hLabels :=
    (occurrenceEquiv target wall shape.candidate.right).injective hTargets
  cases hLabels

theorem new_incident_old (sheet : Fin degree) :
    Incident shape.candidate.datum (shape.candidate.newSourceEdge sheet)
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    shape.candidate.right shape.pasted
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ shape.candidate.exterior) sheet))

theorem background_incident_old (sheet : Fin degree) :
    Incident shape.candidate.datum
        (shape.candidate.oldSourceEdge
          (data.sourceEdge shape.backgroundTarget sheet))
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  W3Nd2Survival.oldSourceEdge_incident_old shape.candidate shape.backgroundTarget
    shape.target_mem shape.left sheet

/-- **The complete literal incidence at a background retained endpoint.**
Every occurrence there is the new one through that sheet or the `t_α`
occurrence through it -- no survival hypothesis is used. -/
theorem incident_old_cases {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    {edge : shape.candidate.datum.SourceEdge}
    (hIncident : Incident shape.candidate.datum edge
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    edge = shape.candidate.newSourceEdge sheet ∨
      edge = shape.candidate.oldSourceEdge
        (data.sourceEdge shape.backgroundTarget sheet) := by
  rcases ResolutionPruning.sourceEdge_cases shape.candidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · right
    obtain ⟨_, hRight⟩ :=
      W3Nd3StableGraph.old_incident_old_selected_info_local shape.candidate
        (WallBlock.ofSheet data wall sheet) sheet
        ((data.vertexPartition wall).rel_repr_left sheet) old hIncident
    have hTarget : old.1.1 = shape.backgroundTarget := shape.unique _ hRight
    have hSheetRel := old_incident_old_sheet_rel_local shape.candidate sheet old
      hIncident
    have hMem : old.1.2 ∈ shape.pasted.left.block sheet :=
      (shape.pasted.left.mem_block_iff _ _).mpr hSheetRel
    rw [shape.pasted_left_block hSheet] at hMem
    have hEdgeRel :=
      ((data.edgePartition shape.backgroundTarget).mem_block_iff _ _).mp hMem
    refine congrArg shape.candidate.oldSourceEdge (Subtype.ext (Prod.ext ?_ ?_)).symm
    · exact hTarget.symm
    · change (data.edgePartition shape.backgroundTarget).repr sheet = old.1.2
      have hRepr : (data.edgePartition shape.backgroundTarget).repr old.1.2 =
          old.1.2 := by rw [← hTarget]; exact old.2
      exact hEdgeRel.trans hRepr
  · left
    have hSheetRel := W3Nd3StableGraph.new_incident_old_sheet_rel_local
      shape.candidate sheet new hIncident
    have hMem : shape.pasted.newEdge.repr new ∈ shape.pasted.left.block sheet :=
      (shape.pasted.left.mem_block_iff _ _).mpr hSheetRel
    rw [shape.pasted_left_block hSheet, ← shape.pasted_newEdge_block hSheet] at hMem
    have hNewRel := (shape.pasted.newEdge.mem_block_iff sheet _).mp hMem
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change shape.pasted.newEdge.repr new = shape.pasted.newEdge.repr sheet
      exact (shape.pasted.newEdge.repr_idem new).symm.trans hNewRel.symm

theorem nonDanglingIncident_old_subset {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) ⊆
      {shape.candidate.newSourceEdge sheet,
        shape.candidate.oldSourceEdge
          (data.sourceEdge shape.backgroundTarget sheet)} := by
  classical
  intro edge hMem
  obtain ⟨_, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
  rcases shape.incident_old_cases hSheet hIncident with hNew | hOld
  · exact Finset.mem_insert.mpr (Or.inl hNew)
  · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hOld)

/-- **A background new occurrence has exactly the pruning status of its old
representative.** -/
theorem new_isDangling_iff (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    IsDangling shape.candidate.datum (shape.candidate.newSourceEdge sheet) ↔
      IsDangling data (data.sourceEdge shape.backgroundTarget sheet) := by
  classical
  have hNe : (nonDanglingIncident shape.candidate.datum
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)).card
        ≠ 1 := by
    rw [card_nonDanglingIncident]
    exact NonDanglingValency.nonDanglingValency_ne_one shape.candidate.datum
      (shape.candidate.datum_valid hValid).1
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)
  constructor
  · intro hDangling
    by_contra hOldSurvives
    have hSingle : nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
        {shape.candidate.oldSourceEdge
          (data.sourceEdge shape.backgroundTarget sheet)} := by
      apply Finset.Subset.antisymm
      · intro edge hMem
        obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
        rcases shape.incident_old_cases hSheet hIncident with hNew | hOld
        · exact absurd (hNew ▸ hSurvives) (by simpa using hDangling)
        · exact Finset.mem_singleton.mpr hOld
      · intro edge hMem
        rw [Finset.mem_singleton.mp hMem]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨fun h ↦ hOldSurvives ((shape.old_isDangling_iff hValid _).mp h),
            shape.background_incident_old sheet⟩
    rw [hSingle, Finset.card_singleton] at hNe
    exact hNe rfl
  · intro hDangling
    by_contra hNewSurvives
    have hSingle : nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
        {shape.candidate.newSourceEdge sheet} := by
      apply Finset.Subset.antisymm
      · intro edge hMem
        obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
        rcases shape.incident_old_cases hSheet hIncident with hNew | hOld
        · exact Finset.mem_singleton.mpr hNew
        · exact absurd (hOld ▸ hSurvives)
            (by simpa using (shape.old_isDangling_iff hValid _).mpr hDangling)
      · intro edge hMem
        rw [Finset.mem_singleton.mp hMem]
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨hNewSurvives, shape.new_incident_old sheet⟩
    rw [hSingle, Finset.card_singleton] at hNe
    exact hNe rfl

/-- The complete surviving star at a background retained endpoint whose `t_α`
occurrence survives. -/
theorem nonDanglingIncident_old (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.backgroundTarget sheet)) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
      {shape.candidate.newSourceEdge sheet,
        shape.candidate.oldSourceEdge
          (data.sourceEdge shape.backgroundTarget sheet)} := by
  classical
  apply Finset.Subset.antisymm (shape.nonDanglingIncident_old_subset hSheet)
  intro edge hMem
  rcases Finset.mem_insert.mp hMem with rfl | hOld
  · exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨fun h ↦ hSurvives ((shape.new_isDangling_iff hValid hSheet).mp h),
        shape.new_incident_old sheet⟩
  · rw [Finset.mem_singleton.mp hOld]
    exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨fun h ↦ hSurvives ((shape.old_isDangling_iff hValid _).mp h),
        shape.background_incident_old sheet⟩

theorem old_nonDanglingValency_eq_two (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.backgroundTarget sheet)) :
    nonDanglingValency shape.candidate.datum
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    shape.nonDanglingIncident_old hValid hSheet hSurvives]
  exact Finset.card_pair (shape.new_ne_old _ _)

/-- **Every surviving background new occurrence lies in its old
representative's stable row.** -/
theorem new_stablePath_eq (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.backgroundTarget sheet)) :
    NonDanglingEdge.stablePath
        (⟨shape.candidate.newSourceEdge sheet,
          fun h ↦ hSurvives ((shape.new_isDangling_iff hValid hSheet).mp h)⟩ :
          NonDanglingEdge shape.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨shape.candidate.oldSourceEdge
            (data.sourceEdge shape.backgroundTarget sheet),
          fun h ↦ hSurvives ((shape.old_isDangling_iff hValid _).mp h)⟩ :
          NonDanglingEdge shape.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, _, shape.new_incident_old sheet,
    shape.background_incident_old sheet,
    shape.old_nonDanglingValency_eq_two hValid hSheet hSurvives⟩
  intro hEq
  exact shape.new_ne_old sheet _ (congrArg Subtype.val hEq)

/-- **And carries its index**, which is Figure 28's `σ⁽ᵠ⁾(J₀,1) = σ₀(J₀,α)`. -/
theorem newIndex_eq {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    shape.candidate.datum.sourceEdgeIndex
        (shape.candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex (data.sourceEdge shape.backgroundTarget sheet) := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    GluingDatum.sourceEdgeIndex_sourceEdge]
  change shape.pasted.newEdge.blockCard sheet =
    (data.edgePartition shape.backgroundTarget).blockCard sheet
  unfold SheetPartition.blockCard
  rw [shape.pasted_newEdge_block hSheet]

end BackgroundShape

/-! ### The four members' backgrounds

`M⁽¹⁾` and `M⁽²⁾` resolve the background with `t₄`; `M⁽³⁾` and `M⁽⁴⁾` with
their own grow direction.  These are the `α = 4, 4, 2, 3` of Figure 28, and
they are read off the two candidate constructions, not supplied. -/

/-- The background of either reversed member: `t₄`'s own fine star. -/
noncomputable def ReversedMember.toBackgroundShape (member : ReversedMember data wall) :
    BackgroundShape data wall where
  candidate := member.candidate
  backgroundTarget := member.geometry.largestTarget
  target_mem := member.geometry.largestTarget_mem
  left := member.right_largest
  unique := by
    intro edge hRight
    have hDecide : W3Nd2SourceCandidates.rightOf member.geometry.largestTarget
        edge = false := hRight
    simpa [W3Nd2SourceCandidates.rightOf] using hDecide
  selected := member.geometry.growAnchor
  resolution_eq := by
    intro sheet hSheet
    rw [show member.candidate.resolution sheet =
        LocalResolution.onBlock (data.vertexPartition wall)
          member.geometry.growAnchor
          ((fineResolution (data.vertexPartition wall) member.fine
            member.fine_refines).reverse)
          member.geometry.wallBackground.resolution sheet from rfl,
      LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSheet]
    rfl
  genus_eq := member.candidate_sourceGenus

@[simp] theorem ReversedMember.toBackgroundShape_candidate
    (member : ReversedMember data wall) :
    member.toBackgroundShape.candidate = member.candidate := rfl

@[simp] theorem ReversedMember.toBackgroundShape_target
    (member : ReversedMember data wall) :
    member.toBackgroundShape.backgroundTarget = member.geometry.largestTarget := rfl

/-- The background of a grow member: its own grow direction's fine star. -/
noncomputable def GrowMember.toBackgroundShape {star : ThreeStar target wall}
    {input : W3SourceInput data star} (grown : GrowProfile input) :
    BackgroundShape data wall where
  candidate := grown.growCandidate
  backgroundTarget := grown.growTarget
  target_mem := grown.growTarget_mem
  left := GrowMember.right_grow grown
  unique := by
    intro edge hRight
    have hDecide : W3Nd2SourceCandidates.rightOf grown.growTarget edge = false :=
      hRight
    simpa [W3Nd2SourceCandidates.rightOf] using hDecide
  selected := grown.growAnchor
  resolution_eq := by
    intro sheet hSheet
    rw [show grown.growCandidate.resolution sheet =
        LocalResolution.onBlock (data.vertexPartition wall) grown.growAnchor
          (fineResolution (data.vertexPartition wall) grown.growPartition
            grown.growPartition_refines)
          (fun _ ↦ fineResolution (data.vertexPartition wall)
            (data.edgePartition grown.growTarget) grown.growTarget_refines)
          sheet from rfl,
      LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSheet]
  genus_eq := GrowProfile.growCandidate_sourceGenus grown

@[simp] theorem GrowMember.toBackgroundShape_candidate {star : ThreeStar target wall}
    {input : W3SourceInput data star} (grown : GrowProfile input) :
    (GrowMember.toBackgroundShape grown).candidate = grown.growCandidate := rfl

@[simp] theorem GrowMember.toBackgroundShape_target {star : ThreeStar target wall}
    {input : W3SourceInput data star} (grown : GrowProfile input) :
    (GrowMember.toBackgroundShape grown).backgroundTarget = grown.growTarget := rfl

end DraismaVargas.LocalCases.W3FourSurvival
