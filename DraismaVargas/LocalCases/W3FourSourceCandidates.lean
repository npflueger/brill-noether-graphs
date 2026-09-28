import DraismaVargas.LocalCases.W3Nd2SourceCandidates

/-!
# Source-derived W3 four-candidate geometry (Figure 28, Equation (2))

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a=k4)}` (within cases
`{w3-r1-nd3}` and `{w3-r1-nd3-t2}`, with their Positions I, II.a, II.b; the
`(a = k₄)` case and its four members), Figure 28 and Equation (2).  This is
the `w3Four` tag of
`ClassifiedContinuation.SourceCase`, selected by
`W3IncomingClassification.Classification.four`: an actual `Nd3Profile` at the
unique ramified wall block whose three survivors lie above three distinct
target directions and whose largest index equals the complete block
cardinality `|A₀|`, so that the two smaller indices satisfy `k₂ + k₃ = |A₀|`.

## What is constructed

Figure 28's two **grow** members, `M⁽³⁾` and `M⁽⁴⁾`.  In the source these are
the Position II.a members: the new divalent endpoint `u` carries exactly one
of the two smaller directions `t₂`, `t₃`, its class `A'` is literally the new
edge class `e'`, and `|A'| = |e'| = k + 1` where `k` is that survivor's actual
source index; the trivalent endpoint `v` keeps the whole wall block and the
remaining two actual directions.  The classes of `A₀` above `t₂` other than
`e₂` are dangling, hence singletons by `dangling_no_glue`, so the divalent
partition is `e₂ ∪ {x}` together with singletons -- exactly the source's
picture, and exactly what makes the trivalent Riemann--Hurwitz count hold with
equality.

The fine partition is placed on the **divalent** side here deliberately: that
is where Position II.a puts `A'`.  This is the opposite of the W3 nd2 case,
where a same-side fine candidate is valid but is *not* the source's member;
see `GlobalCoarseFine` and `W3Nd2FineCandidates`.

Everything is derived from a literal `ThirdEquation.W3SourceInput` and
`W3R1SourceProfile.Nd3Profile`; no numerical diagram, refinement or induced
count is supplied by the caller.  Both members are certified valid
(`GrowProfile.growCandidate_valid`), genus preserving
(`GrowProfile.growCandidate_sourceGenus`), and carrying the displayed
new-edge index (`GrowProfile.growCandidate_newEdge_blockCard`).

## Which datum this is about

`W3SourceInput` carries `equation_c : data.targetExcess wall = 1`, so its wall
vertex is *not* change-minimal.  This module therefore lives on the limit/wall
side of the bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`: the same side
as `AuxR0SourceInput`, and never a `FullDimensionalSourcePresentation` datum.
The hypotheses are jointly satisfiable exactly when that interface is: all of
`GrowProfile`'s fields are produced from an arbitrary `Nd3Profile` plus the
two arithmetic conditions of `Classification.four` by `growProfileFirst` and
`growProfileSecond`, which are total.

## What is not constructed

Figure 28's other two members `M⁽¹⁾` (Position I) and `M⁽²⁾` (Position II.b),
and hence Equation (2)'s determinant balance, the honest stable presentations,
the common retained columns and the stable-graph incidence transport.  The
first omission is one of sheet labelling, not of mathematics:
`exists_sheet_outside_iff_not_disjoint` below shows those two members demand
opposite things of the same two source classes **for a fixed datum value**, and
`W3FourClosure` builds both on branch-swapped copies.
-/

namespace DraismaVargas.LocalCases.W3FourSourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine GlobalCoarseFine
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary M11SourceGenus
open W3Nd2SourceCandidates (OrientedStar rightOf wallEdgesAssigned_false
  wallEdgesAssigned_true external_count_eq)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

variable {input : W3SourceInput data star}

/-! ## One big block and singletons -/

/-- Inside one coarse block, a refinement all of whose induced blocks except
the one through `big` are singletons induces exactly
`coarse.blockCard anchor + 1 - fine.blockCard big` blocks.  All three exact
counts of Figure 28 have this shape. -/
theorem blockCountWithin_of_singletons_off_block
    (fine coarse : SheetPartition degree) (hFine : fine.Refines coarse)
    (anchor big : Fin degree) (hBig : coarse.Rel anchor big)
    (hOthers : ∀ sheet, coarse.Rel anchor sheet → ¬fine.Rel big sheet →
      fine.blockCard sheet = 1) :
    fine.blockCountWithin coarse anchor + fine.blockCard big =
      coarse.blockCard anchor + 1 := by
  classical
  let coarseBlock : coarse.Blocks := coarse.toBlock anchor
  let blocks := SheetPartition.blocksWithin fine coarse coarseBlock
  let bigBlock : fine.Blocks := fine.toBlock big
  have hAnchorRel : coarse.Rel coarseBlock.1 anchor := coarse.rel_repr_left anchor
  have hBigRel : fine.Rel big bigBlock.1 := fine.rel_repr_right big
  have hBigMem : bigBlock ∈ blocks := by
    apply (SheetPartition.mem_blocksWithin fine coarse coarseBlock bigBlock).mpr
    apply (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse
      bigBlock coarseBlock).mpr
    exact hAnchorRel.trans (hBig.trans (hFine.rel hBigRel))
  have hSum : (∑ block ∈ blocks, (fine.blockCard block.1 : ℤ)) =
      (coarse.blockCard coarseBlock.1 : ℤ) :=
    sum_blockCard_blocksWithin fine coarse hFine coarseBlock
  have hErase : ∀ block ∈ blocks.erase bigBlock,
      (fine.blockCard block.1 : ℤ) = 1 := by
    intro block hBlock
    have hNe : block ≠ bigBlock := (Finset.mem_erase.mp hBlock).1
    have hMem := Finset.mem_of_mem_erase hBlock
    have hCoarseRel : coarse.Rel coarseBlock.1 block.1 :=
      (SheetPartition.fineBlockToCoarseBlock_eq_iff_rel fine coarse block
        coarseBlock).mp
        ((SheetPartition.mem_blocksWithin fine coarse coarseBlock block).mp hMem)
    have hAnchorBlock : coarse.Rel anchor block.1 :=
      hAnchorRel.symm.trans hCoarseRel
    have hNotFine : ¬fine.Rel big block.1 := by
      intro hRel
      apply hNe
      apply Subtype.ext
      change block.1 = fine.repr big
      have hValue : fine.repr big = fine.repr block.1 := hRel
      exact (hValue.trans block.2).symm
    exact_mod_cast hOthers block.1 hAnchorBlock hNotFine
  have hEraseSum : (∑ block ∈ blocks.erase bigBlock,
      (fine.blockCard block.1 : ℤ)) = ((blocks.erase bigBlock).card : ℤ) := by
    rw [Finset.sum_congr rfl hErase]
    simp
  have hTotal := Finset.sum_erase_add blocks
    (fun block ↦ (fine.blockCard block.1 : ℤ)) hBigMem
  rw [hEraseSum, hSum] at hTotal
  have hBigCard : fine.blockCard bigBlock.1 = fine.blockCard big :=
    (SheetPartition.blockCard_congr fine hBigRel).symm
  have hCount : blocks.card = fine.blockCountWithin coarse anchor := by
    rw [SheetPartition.card_blocksWithin_eq_blockCountWithin fine coarse hFine
      coarseBlock]
    exact SheetPartition.blockCountWithin_congr fine coarse hAnchorRel
  have hCoarseCard : coarse.blockCard coarseBlock.1 = coarse.blockCard anchor :=
    SheetPartition.blockCard_congr coarse hAnchorRel
  have hEraseCard := Finset.card_erase_of_mem hBigMem
  have hPos : 0 < blocks.card := Finset.card_pos.mpr ⟨bigBlock, hBigMem⟩
  rw [hBigCard] at hTotal
  rw [hCoarseCard] at hTotal
  have hNat : (blocks.card - 1) + fine.blockCard big = coarse.blockCard anchor := by
    rw [← hEraseCard]
    exact_mod_cast hTotal
  omega

/-! ## The literal `w3Four` source profile -/

/-- Position II.a's transferred sheet, before a `GrowProfile` is built.  A
survivor whose class is strictly smaller than the distinguished wall block
misses a sheet of that block. -/
theorem exists_transferSheet (input : W3SourceInput data star)
    (edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hLt : data.sourceEdgeIndex edge.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    ∃ sheet, (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet ∧
      ¬(data.edgePartition edge.1.1.1).Rel edge.1.1.2 sheet := by
  classical
  have hRefines := refines_of_mem_incidentEdges data
    (((incident_wallBlock_sourceVertex_iff data input.distinguishedBlock
      edge.1).mp edge.2).1)
  have hIncident := (incident_wallBlock_sourceVertex_iff data
    input.distinguishedBlock edge.1).mp edge.2
  have hValue := congrArg Subtype.val hIncident.2
  have hAnchor : (data.vertexPartition wall).Rel input.distinguishedBlock.1
      edge.1.1.2 := by
    change (data.vertexPartition wall).repr edge.1.1.2 =
      input.distinguishedBlock.1 at hValue
    change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
      (data.vertexPartition wall).repr edge.1.1.2
    rw [input.distinguishedBlock.2, hValue]
  have hSub : (data.edgePartition edge.1.1.1).block edge.1.1.2 ⊆
      (data.vertexPartition wall).block input.distinguishedBlock.1 := by
    intro sheet hSheet
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr
      (hAnchor.trans (hRefines.rel
        (((data.edgePartition edge.1.1.1).mem_block_iff _ _).mp hSheet)))
  change (data.edgePartition edge.1.1.1).blockCard edge.1.1.2 <
    (data.vertexPartition wall).blockCard input.distinguishedBlock.1 at hLt
  unfold SheetPartition.blockCard at hLt
  have hNe : (data.edgePartition edge.1.1.1).block edge.1.1.2 ≠
      (data.vertexPartition wall).block input.distinguishedBlock.1 := by
    intro hEq
    rw [hEq] at hLt
    omega
  obtain ⟨sheet, hMem, hNotMem⟩ := (Finset.ssubset_iff_of_subset hSub).mp
    (Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hNe⟩)
  exact ⟨sheet, ((data.vertexPartition wall).mem_block_iff _ _).mp hMem,
    fun hRel ↦ hNotMem
      (((data.edgePartition edge.1.1.1).mem_block_iff _ _).mpr hRel)⟩

/-- Figure 28's actual source profile at the unique ramified wall block,
presented with one of the two smaller survivors singled out.  `grow` is the
occurrence whose direction Figure 28 places alone at the new divalent
endpoint; `other` and `largest` stay at the trivalent endpoint.  Taking
`grow` to be the profile's `first` gives Figure 28's `M⁽³⁾` and taking it to
be `second` gives `M⁽⁴⁾`. -/
structure GrowProfile (input : W3SourceInput data star) where
  grow : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall input.distinguishedBlock)
  other : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall input.distinguishedBlock)
  largest : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall input.distinguishedBlock)
  grow_ne_other : grow ≠ other
  grow_ne_largest : grow ≠ largest
  other_ne_largest : other ≠ largest
  surviving : survivors data input.distinguishedBlock = {grow, other, largest}
  grow_target_ne_other : grow.1.1.1 ≠ other.1.1.1
  grow_target_ne_largest : grow.1.1.1 ≠ largest.1.1.1
  other_target_ne_largest : other.1.1.1 ≠ largest.1.1.1
  largest_index : data.sourceEdgeIndex largest.1 =
    (data.vertexPartition wall).blockCard input.distinguishedBlock.1
  index_sum : data.sourceEdgeIndex grow.1 + data.sourceEdgeIndex other.1 =
    (data.vertexPartition wall).blockCard input.distinguishedBlock.1
  /-- Position II.a's transferred sheet, carried as actual data so an incoming
  cover can install the sheet it displays. -/
  extra : Fin degree
  /-- The transferred sheet lies in the distinguished wall block. -/
  extra_wall_rel : (data.vertexPartition wall).Rel input.distinguishedBlock.1 extra
  /-- The transferred sheet lies outside the grow survivor's class. -/
  extra_separate : ¬(data.edgePartition grow.1.1.1).Rel grow.1.1.2 extra

/-- Figure 28's `M⁽³⁾` orientation: the profile's `first` survivor grows. -/
noncomputable def growProfileFirst (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    GrowProfile input := by
  have hSum := profile.indices_of_largest_eq largest_index
  have hLt : data.sourceEdgeIndex profile.first.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 := by
    have hPos := data.sourceEdgeIndex_pos profile.second.1
    omega
  let extra := (exists_transferSheet input profile.first hLt).choose
  exact {
  grow := profile.first
  other := profile.second
  largest := profile.largest
  grow_ne_other := profile.first_ne_second
  grow_ne_largest := profile.first_ne_largest
  other_ne_largest := profile.second_ne_largest
  surviving := profile.surviving
  grow_target_ne_other := directions
  grow_target_ne_largest := profile.first_target_ne
  other_target_ne_largest := profile.second_target_ne
  largest_index := largest_index
  index_sum := profile.indices_of_largest_eq largest_index
  extra := extra
  extra_wall_rel := (exists_transferSheet input profile.first hLt).choose_spec.1
  extra_separate := (exists_transferSheet input profile.first hLt).choose_spec.2 }

/-- Figure 28's `M⁽⁴⁾` orientation: the profile's `second` survivor grows. -/
noncomputable def growProfileSecond (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    GrowProfile input := by
  have hSum := profile.indices_of_largest_eq largest_index
  have hLt : data.sourceEdgeIndex profile.second.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 := by
    have hPos := data.sourceEdgeIndex_pos profile.first.1
    omega
  let extra := (exists_transferSheet input profile.second hLt).choose
  exact {
  grow := profile.second
  other := profile.first
  largest := profile.largest
  grow_ne_other := fun h ↦ profile.first_ne_second h.symm
  grow_ne_largest := profile.second_ne_largest
  other_ne_largest := profile.first_ne_largest
  surviving := by
    rw [profile.surviving]
    ext edge
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  grow_target_ne_other := fun h ↦ directions h.symm
  grow_target_ne_largest := profile.second_target_ne
  other_target_ne_largest := profile.first_target_ne
  largest_index := largest_index
  index_sum := by
    have h := profile.indices_of_largest_eq largest_index
    omega
  extra := extra
  extra_wall_rel := (exists_transferSheet input profile.second hLt).choose_spec.1
  extra_separate := (exists_transferSheet input profile.second hLt).choose_spec.2 }

/-! ## The dangling complement of a surviving direction -/

/-- The canonical occurrence above an incident target direction through a
sheet of a wall block is incident to that block's source vertex. -/
theorem sourceEdge_incident (block : WallBlock data wall)
    (direction : target.edges)
    (hMem : direction ∈ GluingDatum.incidentEdges wall) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    Incident data (data.sourceEdge direction sheet)
      (WallBlock.sourceVertex data wall block) := by
  have hRefines := refines_of_mem_incidentEdges data hMem
  have hEdgeRel := hRefines.rel
    ((data.edgePartition direction).rel_repr_right sheet)
  apply (incident_wallBlock_sourceVertex_iff data block _).mpr
  exact ⟨hMem, Subtype.ext (hEdgeRel.symm.trans (hSheet.symm.trans block.2))⟩

/-- Every occurrence of the distinguished block above a surviving direction
other than the survivor itself is dangling, hence has a singleton class.
This is the literal `nd = 3` statement: the three survivors exhaust the
non-dangling occurrences and lie above three distinct target directions. -/
theorem blockCard_eq_one_of_not_rel (survivor : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hUnique : ∀ candidate ∈ survivors data input.distinguishedBlock,
      candidate.1.1.1 = survivor.1.1.1 → candidate = survivor)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition survivor.1.1.1).Rel survivor.1.1.2 sheet) :
    (data.edgePartition survivor.1.1.1).blockCard sheet = 1 := by
  have hMem : survivor.1.1.1 ∈ GluingDatum.incidentEdges wall :=
    ((incident_wallBlock_sourceVertex_iff data input.distinguishedBlock
      survivor.1).mp survivor.2).1
  have hIncident := sourceEdge_incident (data := data) input.distinguishedBlock
    survivor.1.1.1 hMem sheet hSheet
  have hDangling : IsDangling data (data.sourceEdge survivor.1.1.1 sheet) := by
    by_contra hSurvives
    have hIn : (⟨data.sourceEdge survivor.1.1.1 sheet, hIncident⟩ :
        IncidentSourceEdge data
          (WallBlock.sourceVertex data wall input.distinguishedBlock)) ∈
        survivors data input.distinguishedBlock :=
      (mem_survivors data input.distinguishedBlock _).mpr hSurvives
    have hEq := hUnique _ hIn rfl
    have hValue := congrArg (fun edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock) ↦
        edge.1.1.2) hEq
    apply hNe
    change (data.edgePartition survivor.1.1.1).repr survivor.1.1.2 =
      (data.edgePartition survivor.1.1.1).repr sheet
    rw [survivor.1.2]
    exact hValue.symm
  have hIndex := input.dangling_no_glue _ hDangling
  rwa [GluingDatum.sourceEdgeIndex_sourceEdge] at hIndex

/-- The `other` direction is represented by a single survivor. -/
theorem other_unique (grown : GrowProfile input)
    (candidate : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hCandidate : candidate ∈ survivors data input.distinguishedBlock)
    (hTarget : candidate.1.1.1 = grown.other.1.1.1) :
    candidate = grown.other := by
  rw [grown.surviving] at hCandidate
  simp only [Finset.mem_insert, Finset.mem_singleton] at hCandidate
  rcases hCandidate with hGrow | hOther | hLargest
  · exact (grown.grow_target_ne_other (hGrow ▸ hTarget)).elim
  · exact hOther
  · exact (grown.other_target_ne_largest ((hLargest ▸ hTarget)).symm).elim

/-- The `largest` direction is represented by a single survivor. -/
theorem largest_unique (grown : GrowProfile input)
    (candidate : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hCandidate : candidate ∈ survivors data input.distinguishedBlock)
    (hTarget : candidate.1.1.1 = grown.largest.1.1.1) :
    candidate = grown.largest := by
  rw [grown.surviving] at hCandidate
  simp only [Finset.mem_insert, Finset.mem_singleton] at hCandidate
  rcases hCandidate with hGrow | hOther | hLargest
  · exact (grown.grow_target_ne_largest (hGrow ▸ hTarget)).elim
  · exact (grown.other_target_ne_largest (hOther ▸ hTarget)).elim
  · exact hLargest

/-- The `grow` direction is represented by a single survivor. -/
theorem grow_unique (grown : GrowProfile input)
    (candidate : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hCandidate : candidate ∈ survivors data input.distinguishedBlock)
    (hTarget : candidate.1.1.1 = grown.grow.1.1.1) :
    candidate = grown.grow := by
  rw [grown.surviving] at hCandidate
  simp only [Finset.mem_insert, Finset.mem_singleton] at hCandidate
  rcases hCandidate with hGrow | hOther | hLargest
  · exact hGrow
  · exact (grown.grow_target_ne_other ((hOther ▸ hTarget)).symm).elim
  · exact (grown.grow_target_ne_largest ((hLargest ▸ hTarget)).symm).elim

/-! ## The three actual target directions -/

/-- The canonical sheet of an incident occurrence lies in its wall block. -/
theorem incident_anchor_wall_rel (block : WallBlock data wall)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (data.vertexPartition wall).Rel block.1 edge.1.1.2 := by
  have hBlock := (incident_wallBlock_sourceVertex_iff data block edge.1).mp edge.2 |>.2
  have hValue := congrArg Subtype.val hBlock
  change (data.vertexPartition wall).repr edge.1.1.2 = block.1 at hValue
  change (data.vertexPartition wall).repr block.1 =
    (data.vertexPartition wall).repr edge.1.1.2
  rw [block.2, hValue]

/-- The target direction of an incident occurrence is a wall direction. -/
theorem incident_target_mem (block : WallBlock data wall)
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    edge.1.1.1 ∈ GluingDatum.incidentEdges wall :=
  ((incident_wallBlock_sourceVertex_iff data block edge.1).mp edge.2).1

namespace GrowProfile

/-- The direction Figure 28 places alone at the new divalent endpoint. -/
abbrev growTarget (grown : GrowProfile input) : target.edges := grown.grow.1.1.1

/-- The canonical sheet of the grow survivor. -/
abbrev growAnchor (grown : GrowProfile input) : Fin degree := grown.grow.1.1.2

/-- The second smaller survivor's direction, at the trivalent endpoint. -/
abbrev otherTarget (grown : GrowProfile input) : target.edges := grown.other.1.1.1

/-- The canonical sheet of the second smaller survivor. -/
abbrev otherAnchor (grown : GrowProfile input) : Fin degree := grown.other.1.1.2

/-- The full-degree survivor's direction, at the trivalent endpoint. -/
abbrev largestTarget (grown : GrowProfile input) : target.edges :=
  grown.largest.1.1.1

/-- The canonical sheet of the full-degree survivor. -/
abbrev largestAnchor (grown : GrowProfile input) : Fin degree :=
  grown.largest.1.1.2

theorem growTarget_mem (grown : GrowProfile input) :
    grown.growTarget ∈ GluingDatum.incidentEdges wall :=
  incident_target_mem input.distinguishedBlock grown.grow

theorem otherTarget_mem (grown : GrowProfile input) :
    grown.otherTarget ∈ GluingDatum.incidentEdges wall :=
  incident_target_mem input.distinguishedBlock grown.other

theorem largestTarget_mem (grown : GrowProfile input) :
    grown.largestTarget ∈ GluingDatum.incidentEdges wall :=
  incident_target_mem input.distinguishedBlock grown.largest

theorem growAnchor_wall_rel (grown : GrowProfile input) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 grown.growAnchor :=
  incident_anchor_wall_rel input.distinguishedBlock grown.grow

theorem otherAnchor_wall_rel (grown : GrowProfile input) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 grown.otherAnchor :=
  incident_anchor_wall_rel input.distinguishedBlock grown.other

theorem largestAnchor_wall_rel (grown : GrowProfile input) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 grown.largestAnchor :=
  incident_anchor_wall_rel input.distinguishedBlock grown.largest

theorem growTarget_refines (grown : GrowProfile input) :
    (data.edgePartition grown.growTarget).Refines (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data grown.growTarget_mem

/-- The trivalent star is exactly the three actual surviving directions. -/
theorem incidentEdges_eq (grown : GrowProfile input) :
    GluingDatum.incidentEdges wall =
      {grown.growTarget, grown.otherTarget, grown.largestTarget} := by
  classical
  have hSubset : ({grown.growTarget, grown.otherTarget, grown.largestTarget} :
      Finset target.edges) ⊆ GluingDatum.incidentEdges wall := by
    intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact grown.growTarget_mem
    · exact grown.otherTarget_mem
    · exact grown.largestTarget_mem
  have hCard : ({grown.growTarget, grown.otherTarget, grown.largestTarget} :
      Finset target.edges).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨grown.grow_target_ne_other, grown.grow_target_ne_largest⟩),
      Finset.card_insert_of_notMem (by
        simpa using grown.other_target_ne_largest), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hSubset
    (by rw [hCard, star.card_incidentEdges])).symm

/-- Figure 28's orientation for a grow member: the grow direction alone at
the divalent endpoint, the other two at the trivalent endpoint. -/
noncomputable def orientation (grown : GrowProfile input) :
    OrientedStar target wall grown.growTarget where
  rightFirst := grown.otherTarget
  rightSecond := grown.largestTarget
  left_mem := grown.growTarget_mem
  rightFirst_ne_left := grown.grow_target_ne_other.symm
  rightSecond_ne_left := grown.grow_target_ne_largest.symm
  right_ne := grown.other_target_ne_largest
  incidentEdges_eq := grown.incidentEdges_eq

end GrowProfile

/-! ## The transferred sheet and the grow partition -/

/-- Every occurrence above the grow direction other than the grow survivor
is a singleton class. -/
theorem grow_blockCard_eq_one (grown : GrowProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition grown.growTarget).Rel grown.growAnchor sheet) :
    (data.edgePartition grown.growTarget).blockCard sheet = 1 :=
  blockCard_eq_one_of_not_rel grown.grow (grow_unique grown) sheet hSheet hNe

/-- Every occurrence above the second smaller direction other than its
survivor is a singleton class. -/
theorem other_blockCard_eq_one (grown : GrowProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition grown.otherTarget).Rel grown.otherAnchor sheet) :
    (data.edgePartition grown.otherTarget).blockCard sheet = 1 :=
  blockCard_eq_one_of_not_rel grown.other (other_unique grown) sheet hSheet hNe

/-- Every occurrence above the full-degree direction other than its survivor
is a singleton class. -/
theorem largest_blockCard_eq_one (grown : GrowProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition grown.largestTarget).Rel grown.largestAnchor sheet) :
    (data.edgePartition grown.largestTarget).blockCard sheet = 1 :=
  blockCard_eq_one_of_not_rel grown.largest (largest_unique grown) sheet hSheet hNe

namespace GrowProfile

/-- The grow survivor does not fill the distinguished wall block: the other
smaller survivor has positive index. -/
theorem growCard_lt (grown : GrowProfile input) :
    (data.edgePartition grown.growTarget).blockCard grown.growAnchor <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 := by
  have hIndex : (data.edgePartition grown.growTarget).blockCard grown.growAnchor =
      data.sourceEdgeIndex grown.grow.1 := rfl
  have hOtherPos := data.sourceEdgeIndex_pos grown.other.1
  have hSum := grown.index_sum
  omega

/-- Figure 28 transfers one sheet of the distinguished wall block outside the
grow survivor's own class into the new divalent block. -/
theorem exists_extraSheet (grown : GrowProfile input) :
    ∃ sheet, (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet ∧
      ¬(data.edgePartition grown.growTarget).Rel grown.growAnchor sheet :=
  ⟨grown.extra, grown.extra_wall_rel, grown.extra_separate⟩

/-- The transferred sheet carried by the profile. -/
def extraSheet (grown : GrowProfile input) : Fin degree := grown.extra

theorem extraSheet_wall_rel (grown : GrowProfile input) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 grown.extraSheet :=
  grown.extra_wall_rel

theorem extraSheet_separate (grown : GrowProfile input) :
    ¬(data.edgePartition grown.growTarget).Rel grown.growAnchor grown.extraSheet :=
  grown.extra_separate

/-- Install the transferred sheet displayed by an incoming Position II.a
cover, leaving the three source occurrences and all arithmetic unchanged. -/
def withExtra (grown : GrowProfile input) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSep : ¬(data.edgePartition grown.growTarget).Rel grown.growAnchor sheet) :
    GrowProfile input :=
  { grown with extra := sheet, extra_wall_rel := hWall, extra_separate := hSep }

@[simp] theorem withExtra_extraSheet (grown : GrowProfile input) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSep : ¬(data.edgePartition grown.growTarget).Rel grown.growAnchor sheet) :
    (grown.withExtra sheet hWall hSep).extraSheet = sheet := rfl

@[simp] theorem withExtra_self (grown : GrowProfile input) :
    grown.withExtra grown.extraSheet grown.extraSheet_wall_rel
      grown.extraSheet_separate = grown := by
  cases grown
  rfl

/-- Field-projection form of `withExtra_self`, useful when dependent structure
construction preserves the original proof fields literally. -/
@[simp] theorem withExtra_self_fields (grown : GrowProfile input) :
    grown.withExtra grown.extraSheet grown.extra_wall_rel grown.extra_separate = grown := by
  cases grown
  rfl

/-- Proof-irrelevant form: reinstalling the carried sheet is the identity for
any witnesses of its two defining propositions. -/
@[simp] theorem withExtra_self_any (grown : GrowProfile input)
    (hWall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 grown.extraSheet)
    (hSep : ¬(data.edgePartition grown.growTarget).Rel
      grown.growAnchor grown.extraSheet) :
    grown.withExtra grown.extraSheet hWall hSep = grown := by
  cases grown
  rfl

/-- The new divalent endpoint's partition: the grow direction's actual edge
partition with the transferred sheet joined to the grow survivor's class.
Only two classes inside the distinguished wall block are touched, so this is
already local: away from that block it is literally the edge partition. -/
noncomputable def growPartition (grown : GrowProfile input) : SheetPartition degree :=
  (data.edgePartition grown.growTarget).mergeBlocks grown.growAnchor
    grown.extraSheet grown.extraSheet_separate

theorem growPartition_rel_growAnchor_iff (grown : GrowProfile input)
    (sheet : Fin degree) :
    grown.growPartition.Rel grown.growAnchor sheet ↔
      (data.edgePartition grown.growTarget).Rel grown.growAnchor sheet ∨
        (data.edgePartition grown.growTarget).Rel grown.extraSheet sheet :=
  SheetPartition.mergeBlocks_rel_first_iff _ _ _ _ _

theorem growTarget_refines_growPartition (grown : GrowProfile input) :
    (data.edgePartition grown.growTarget).Refines grown.growPartition :=
  SheetPartition.refines_mergeBlocks _ _ _ _

theorem growPartition_refines (grown : GrowProfile input) :
    grown.growPartition.Refines (data.vertexPartition wall) :=
  SheetPartition.mergeBlocks_refines_coarse _ _ _ _ _ grown.growTarget_refines
    (grown.growAnchor_wall_rel.symm.trans grown.extraSheet_wall_rel)

theorem growPartition_blockCard_growAnchor (grown : GrowProfile input) :
    grown.growPartition.blockCard grown.growAnchor =
      data.sourceEdgeIndex grown.grow.1 + 1 := by
  have hSingleton : (data.edgePartition grown.growTarget).block grown.extraSheet =
      {grown.extraSheet} :=
    SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
      (grow_blockCard_eq_one grown grown.extraSheet grown.extraSheet_wall_rel
        grown.extraSheet_separate)
  exact SheetPartition.mergeBlocks_blockCard_first_of_singleton _ _ _ _ hSingleton

theorem growPartition_blockCard_of_not_rel (grown : GrowProfile input)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬grown.growPartition.Rel grown.growAnchor sheet) :
    grown.growPartition.blockCard sheet = 1 := by
  rw [grown.growPartition_rel_growAnchor_iff sheet, not_or] at hNe
  obtain ⟨hGrow, hExtra⟩ := hNe
  have hBlock := SheetPartition.mergeBlocks_block_of_separate
    (data.edgePartition grown.growTarget) grown.growAnchor grown.extraSheet sheet
    grown.extraSheet_separate (fun h ↦ hGrow h.symm) (fun h ↦ hExtra h.symm)
  change ((data.edgePartition grown.growTarget).mergeBlocks grown.growAnchor
    grown.extraSheet grown.extraSheet_separate).blockCard sheet = 1
  unfold SheetPartition.blockCard
  rw [hBlock]
  exact grow_blockCard_eq_one grown sheet hSheet hGrow

/-! ## The three exact induced-block counts on the distinguished block -/

theorem growPartition_blockCountWithin (grown : GrowProfile input)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    grown.growPartition.blockCountWithin (data.vertexPartition wall) sheet +
        (data.sourceEdgeIndex grown.grow.1 + 1) =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 + 1 := by
  have hCount := blockCountWithin_of_singletons_off_block grown.growPartition
    (data.vertexPartition wall) grown.growPartition_refines sheet grown.growAnchor
    (hSheet.symm.trans grown.growAnchor_wall_rel)
    (fun other hOther hNe ↦ grown.growPartition_blockCard_of_not_rel other
      (hSheet.trans hOther) hNe)
  rw [grown.growPartition_blockCard_growAnchor,
    ← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet] at hCount
  exact hCount

theorem other_blockCountWithin (grown : GrowProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition grown.otherTarget).blockCountWithin
          (data.vertexPartition wall) sheet +
        data.sourceEdgeIndex grown.other.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 + 1 := by
  have hCount := blockCountWithin_of_singletons_off_block
    (data.edgePartition grown.otherTarget) (data.vertexPartition wall)
    (refines_of_mem_incidentEdges data grown.otherTarget_mem) sheet
    grown.otherAnchor (hSheet.symm.trans grown.otherAnchor_wall_rel)
    (fun other hOther hNe ↦ other_blockCard_eq_one grown other
      (hSheet.trans hOther) hNe)
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet] at hCount
  exact hCount

theorem largest_blockCountWithin (grown : GrowProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition grown.largestTarget).blockCountWithin
        (data.vertexPartition wall) sheet = 1 := by
  have hCount := blockCountWithin_of_singletons_off_block
    (data.edgePartition grown.largestTarget) (data.vertexPartition wall)
    (refines_of_mem_incidentEdges data grown.largestTarget_mem) sheet
    grown.largestAnchor (hSheet.symm.trans grown.largestAnchor_wall_rel)
    (fun other hOther hNe ↦ largest_blockCard_eq_one grown other
      (hSheet.trans hOther) hNe)
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet] at hCount
  have hLargest : (data.edgePartition grown.largestTarget).blockCard
      grown.largestAnchor =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
    grown.largest_index
  omega

/-- The selected trivalent endpoint's Riemann--Hurwitz count.  The grow
direction contributes `|A₀| - k_grow` induced blocks, the other smaller
direction `k_grow + 1` and the full-degree direction exactly one, so the
three exact counts add to `|A₀| + 2` and the inequality below is an
equality. -/
theorem selected_rightCounts (grown : GrowProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    grown.growPartition.blockCountWithin (data.vertexPartition wall) sheet +
        (data.edgePartition grown.otherTarget).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition grown.largestTarget).blockCountWithin
          (data.vertexPartition wall) sheet ≥
      (data.vertexPartition wall).blockCard sheet + 2 := by
  have hGrow := grown.growPartition_blockCountWithin sheet hSheet
  have hOther := grown.other_blockCountWithin sheet hSheet
  have hLargest := grown.largest_blockCountWithin sheet hSheet
  have hSum := grown.index_sum
  have hCard : (data.vertexPartition wall).blockCard sheet =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
    (SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet).symm
  omega

/-! ## The arbitrary-degree background and the grow member -/

/-- Every unramified wall block is resolved with the grow direction's own
edge partition on the new edge and at the divalent endpoint.  The original
`r = 0` ramification equation is exactly the trivalent endpoint count there,
so no background receipt is assumed. -/
noncomputable def background (grown : GrowProfile input) :
    Background data wall grown.growAnchor := by
  let orientation := grown.orientation
  let fine := data.edgePartition grown.growTarget
  have hFine := grown.growTarget_refines
  let localResolution : LocalResolution degree :=
    fineResolution (data.vertexPartition wall) fine hFine
  refine {
    right := rightOf grown.growTarget
    resolution := fun _ ↦ localResolution
    contracts := ?_
    exterior := ?_
    leftEdges := [grown.growTarget]
    rightEdges := [orientation.rightFirst, orientation.rightSecond]
    leftEdges_eq := ?_
    rightEdges_eq := ?_
    left_riemannHurwitz := ?_
    right_riemannHurwitz := ?_ }
  · intro _ _
    exact fineResolution_contracts _ fine hFine
  · intro edge hIncident _ _
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hEq : edge = grown.growTarget
    · subst edge
      change fine.Refines
        (if rightOf grown.growTarget grown.growTarget then
          localResolution.right else localResolution.left)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false,
        localResolution, fineResolution]
      exact SheetPartition.Refines.refl fine
    · have hRight : rightOf grown.growTarget edge = true := by
        simp [rightOf, hEq]
      rw [hRight, if_pos rfl]
      change (data.edgePartition edge).Refines (data.vertexPartition wall)
      exact refines_of_mem_incidentEdges data hAt
  · rw [wallEdgesAssigned_false orientation]
    rfl
  · rw [wallEdgesAssigned_true orientation]
    rw [Finset.insert_val_of_notMem (by simpa using orientation.right_ne)]
    rfl
  · intro anchor _ _
    exact fineResolution_left_riemannHurwitzAtBlock
      (data.vertexPartition wall) fine (data.edgePartition grown.growTarget)
      hFine anchor
  · intro anchor _ hOther
    apply riemannHurwitzAtBlock_trivalent_of_counts
      (data.vertexPartition wall) (data.vertexPartition wall) fine
      (data.edgePartition orientation.rightFirst)
      (data.edgePartition orientation.rightSecond) anchor
    intro sheet hSheet
    have hSheetOther : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet := fun h ↦ hOther
      (grown.growAnchor_wall_rel.symm.trans h |>.trans hSheet.symm)
    have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
        input.distinguishedBlock := by
      intro hEq
      apply hSheetOther
      have hValue := congrArg Subtype.val hEq
      change (data.vertexPartition wall).repr sheet =
        input.distinguishedBlock.1 at hValue
      change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
        (data.vertexPartition wall).repr sheet
      rw [input.distinguishedBlock.2, hValue]
    have hZero := input.localRamification_eq_zero_of_ne hBlockNe
    have hTotal := external_count_eq (data := data) star orientation sheet
    rw [hZero] at hTotal
    have hTotalNat' :
        (data.edgePartition grown.growTarget).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          0 + 2 + (data.vertexPartition wall).blockCard sheet := by
      exact_mod_cast hTotal
    have hTotalNat :
        fine.blockCountWithin (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          (data.vertexPartition wall).blockCard sheet + 2 := by
      simpa [fine, Nat.add_comm] using hTotalNat'
    change fine.blockCountWithin (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightFirst).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightSecond).blockCountWithin
          (data.vertexPartition wall) sheet ≥
      (data.vertexPartition wall).blockCard sheet + 2
    exact hTotalNat.ge

/-- Figure 28's grow member: the grow direction's class absorbs one further
sheet of the distinguished wall block at the new divalent endpoint, and the
other two actual directions stay at the trivalent endpoint. -/
noncomputable def growPattern (grown : GrowProfile input) :
    TrivalentPattern (data := data) (wall := wall) grown.growAnchor
      (fineResolution (data.vertexPartition wall) grown.growPartition
        grown.growPartition_refines) := by
  refine {
    background := grown.background
    leftExternal := grown.growTarget
    rightExternalFirst := grown.orientation.rightFirst
    rightExternalSecond := grown.orientation.rightSecond
    leftEdges := rfl
    rightEdges := rfl
    exterior := ?_
    rightCounts := ?_ }
  · intro edge hIncident
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hEq : edge = grown.growTarget
    · subst edge
      change (data.edgePartition grown.growTarget).Refines
        (if rightOf grown.growTarget grown.growTarget then
          (data.vertexPartition wall) else grown.growPartition)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false]
      exact grown.growTarget_refines_growPartition
    · have hRight : rightOf grown.growTarget edge = true := by
        simp [rightOf, hEq]
      change (data.edgePartition edge).Refines
        (if rightOf grown.growTarget edge then
          (data.vertexPartition wall) else grown.growPartition)
      rw [hRight, if_pos rfl]
      exact refines_of_mem_incidentEdges data hAt
  · intro anchor hAnchor sheet hSheet
    have hDistSheet : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet :=
      grown.growAnchor_wall_rel.trans hAnchor |>.trans hSheet
    exact grown.selected_rightCounts sheet hDistSheet

/-- The actual globally assembled Figure 28 grow member. -/
noncomputable def growCandidate (grown : GrowProfile input) :
    BalancedGlobal.Candidate target degree data wall :=
  grown.growPattern.candidate
    (fineResolution_contracts (data.vertexPartition wall) grown.growPartition
      grown.growPartition_refines)

/-- The source-derived grow member is valid whenever the incoming datum is. -/
theorem growCandidate_valid (grown : GrowProfile input) :
    grown.growCandidate.datum.Valid :=
  grown.growCandidate.datum_valid input.valid

/-- The grow member preserves the complete quotient-source genus.  Selected
and background blocks are both pasted stars, so the Euler identity is
pointwise and does not assume a separate genus receipt. -/
theorem growCandidate_sourceGenus (grown : GrowProfile input) :
    genus grown.growCandidate.datum.sourceGraph = genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : grown.growCandidate.resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) grown.growAnchor
        (fineResolution (data.vertexPartition wall) grown.growPartition
          grown.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition grown.growTarget) grown.growTarget_refines)
        anchor := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel grown.growAnchor anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩

/-- The displayed Figure 28 index of a grow member: over the distinguished
wall block the new edge carries one class of cardinality `k + 1`, where `k`
is the grow survivor's actual source index. -/
theorem growCandidate_newEdge_blockCard (grown : GrowProfile input) :
    (grown.growCandidate.resolution grown.growAnchor).newEdge.blockCard
        grown.growAnchor = data.sourceEdgeIndex grown.grow.1 + 1 := by
  have hResolution : grown.growCandidate.resolution grown.growAnchor =
      LocalResolution.onBlock (data.vertexPartition wall) grown.growAnchor
        (fineResolution (data.vertexPartition wall) grown.growPartition
          grown.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition grown.growTarget) grown.growTarget_refines)
        grown.growAnchor := rfl
  rw [hResolution, LocalResolution.onBlock_of_rel _ _ _ _ _
    (show (data.vertexPartition wall).Rel grown.growAnchor grown.growAnchor from rfl)]
  exact grown.growPartition_blockCard_growAnchor

end GrowProfile

/-! ## Figure 28's two grow members on the actual source profile -/

/-- Figure 28's `M⁽³⁾`: the profile's `first` survivor's direction grows. -/
noncomputable def thirdCandidate
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    BalancedGlobal.Candidate target degree data wall :=
  (growProfileFirst profile directions largest_index).growCandidate

/-- Figure 28's `M⁽⁴⁾`: the profile's `second` survivor's direction grows. -/
noncomputable def fourthCandidate
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    BalancedGlobal.Candidate target degree data wall :=
  (growProfileSecond profile directions largest_index).growCandidate

/-- **The two Figure 28 grow members of the actual `w3Four` source profile
are valid, preserve the source genus, and carry the displayed new-edge
indices `k₂ + 1` and `k₃ + 1`.**  The hypotheses are exactly the payload of
`W3IncomingClassification.Classification.four`, so this applies to every
literal trivalent-wall source input routed to Equation (2). -/
theorem grow_members_valid_genus_index
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_index : data.sourceEdgeIndex profile.largest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    (thirdCandidate profile directions largest_index).datum.Valid ∧
      genus (thirdCandidate profile directions largest_index).datum.sourceGraph =
        genus data.sourceGraph ∧
      ((thirdCandidate profile directions largest_index).resolution
          profile.first.1.1.2).newEdge.blockCard profile.first.1.1.2 =
        data.sourceEdgeIndex profile.first.1 + 1 ∧
      (fourthCandidate profile directions largest_index).datum.Valid ∧
      genus (fourthCandidate profile directions largest_index).datum.sourceGraph =
        genus data.sourceGraph ∧
      ((fourthCandidate profile directions largest_index).resolution
          profile.second.1.1.2).newEdge.blockCard profile.second.1.1.2 =
        data.sourceEdgeIndex profile.second.1 + 1 :=
  ⟨(growProfileFirst profile directions largest_index).growCandidate_valid,
    (growProfileFirst profile directions largest_index).growCandidate_sourceGenus,
    (growProfileFirst profile directions largest_index).growCandidate_newEdge_blockCard,
    (growProfileSecond profile directions largest_index).growCandidate_valid,
    (growProfileSecond profile directions largest_index).growCandidate_sourceGenus,
    (growProfileSecond profile directions largest_index).growCandidate_newEdge_blockCard⟩

/-! ## Figure 28's `M⁽¹⁾` and `M⁽²⁾` over one fixed datum -/

/-- **`M⁽¹⁾` and `M⁽²⁾` cannot share one datum value.**  Part I displays four
members of the `(a = k₄)` case, and its Position analysis puts opposite
demands on the two smaller survivors `e₂`, `e₃`, whose indices already sum to
`|A₀|`.

* `M⁽¹⁾` is Position I: its `nd = 3` vertex lies over the divalent endpoint,
  and the paper identifies the two new-edge classes `e'`, `e''` with `e₂`,
  `e₃` as subsets of `[d]`.  Being distinct classes of one partition they are
  disjoint, so `e₂` and `e₃` must *tile* `A₀`.
* `M⁽²⁾` is Position II.b: its `nd = 3` vertex `A⁽²⁾` lies over the trivalent
  endpoint, has cardinality `|A₀| - 1`, and is incident to both `e₂` and
  `e₃`.  So one sheet of `A₀` lies outside both classes, and then `e₂` and
  `e₃` must *meet*.

The theorem is the exact arithmetic of that dichotomy: a sheet of the
distinguished block outside both smaller classes exists precisely when the
two classes are not disjoint, that is precisely when Position I's tiling
fails.  The two bullet points are readings of the source's own Position
analysis rather than Lean theorems; the Lean content is the dichotomy itself.
Read together they say that at most one of `M⁽¹⁾`, `M⁽²⁾` is available on any
one fixed **datum value**.  The constructions above are unaffected: `M⁽³⁾` and
`M⁽⁴⁾` need neither condition.

This is no obstruction to Figure 28, because `Disjoint` is a gauge condition:
Part I's branch swap, with its gluing-datum isomorphism (`definition-gd-iso`,
in the subsection on isomorphism classes of gluing datums), moves one class
while fixing the others, and `𝒞*(M₀)` is a set of isomorphism *classes*.  So
Figure 28 keeps all four members, and `W3FourClosure` builds `M⁽¹⁾` and
`M⁽²⁾` on branch-swapped copies of one datum, rebasing them onto the original
by `BranchGauge.valid`.

Equation (2) needs all four terms: `W3FourClosure.equationTwo_residuals`
computes what dropping each one leaves --
`σ₀(J₀,2)+σ₀(J₀,3)−σ₀(J₀,4)`, `σ₀(J₀,4)`, `−σ₀(J₀,2)`, `−σ₀(J₀,3)` respectively --
so a three-member reading would break Equation (2). -/
theorem exists_sheet_outside_iff_not_disjoint (grown : GrowProfile input) :
    (∃ sheet, (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet ∧
        ¬(data.edgePartition grown.growTarget).Rel grown.growAnchor sheet ∧
        ¬(data.edgePartition grown.otherTarget).Rel grown.otherAnchor sheet) ↔
      ¬Disjoint ((data.edgePartition grown.growTarget).block grown.growAnchor)
        ((data.edgePartition grown.otherTarget).block grown.otherAnchor) := by
  classical
  set growBlock := (data.edgePartition grown.growTarget).block grown.growAnchor
    with hGrowBlock
  set otherBlock := (data.edgePartition grown.otherTarget).block grown.otherAnchor
    with hOtherBlock
  set wallBlock := (data.vertexPartition wall).block input.distinguishedBlock.1
    with hWallBlock
  have hGrowSub : growBlock ⊆ wallBlock := by
    intro sheet hMem
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr
      (grown.growAnchor_wall_rel.trans (grown.growTarget_refines.rel
        (((data.edgePartition grown.growTarget).mem_block_iff _ _).mp hMem)))
  have hOtherSub : otherBlock ⊆ wallBlock := by
    intro sheet hMem
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr
      (grown.otherAnchor_wall_rel.trans
        ((refines_of_mem_incidentEdges data grown.otherTarget_mem).rel
          (((data.edgePartition grown.otherTarget).mem_block_iff _ _).mp hMem)))
  have hUnionSub : growBlock ∪ otherBlock ⊆ wallBlock :=
    Finset.union_subset hGrowSub hOtherSub
  have hCards : growBlock.card + otherBlock.card = wallBlock.card := grown.index_sum
  have hInter := Finset.card_union_add_card_inter growBlock otherBlock
  constructor
  · rintro ⟨sheet, hSheet, hGrow, hOther⟩
    have hMem : sheet ∈ wallBlock :=
      ((data.vertexPartition wall).mem_block_iff _ _).mpr hSheet
    have hNotMem : sheet ∉ growBlock ∪ otherBlock := by
      simp only [Finset.mem_union, not_or]
      exact ⟨fun h ↦ hGrow
          (((data.edgePartition grown.growTarget).mem_block_iff _ _).mp h),
        fun h ↦ hOther
          (((data.edgePartition grown.otherTarget).mem_block_iff _ _).mp h)⟩
    have hLt : (growBlock ∪ otherBlock).card < wallBlock.card :=
      Finset.card_lt_card ((Finset.ssubset_iff_of_subset hUnionSub).mpr
        ⟨sheet, hMem, hNotMem⟩)
    intro hDisjoint
    rw [Finset.disjoint_iff_inter_eq_empty] at hDisjoint
    rw [hDisjoint, Finset.card_empty] at hInter
    omega
  · intro hNotDisjoint
    obtain ⟨witness, hWitnessGrow, hWitnessOther⟩ :=
      Finset.not_disjoint_iff.mp hNotDisjoint
    have hInterPos : 0 < (growBlock ∩ otherBlock).card :=
      Finset.card_pos.mpr ⟨witness, Finset.mem_inter.mpr ⟨hWitnessGrow, hWitnessOther⟩⟩
    have hLt : (growBlock ∪ otherBlock).card < wallBlock.card := by omega
    have hNe : growBlock ∪ otherBlock ≠ wallBlock := by
      intro hEq
      rw [hEq] at hLt
      omega
    obtain ⟨sheet, hMem, hNotMem⟩ := (Finset.ssubset_iff_of_subset hUnionSub).mp
      (Finset.ssubset_iff_subset_ne.mpr ⟨hUnionSub, hNe⟩)
    simp only [Finset.mem_union, not_or] at hNotMem
    exact ⟨sheet, ((data.vertexPartition wall).mem_block_iff _ _).mp hMem,
      fun h ↦ hNotMem.1
        (((data.edgePartition grown.growTarget).mem_block_iff _ _).mpr h),
      fun h ↦ hNotMem.2
        (((data.edgePartition grown.otherTarget).mem_block_iff _ _).mpr h)⟩

end DraismaVargas.LocalCases.W3FourSourceCandidates
