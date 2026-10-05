module

public import DraismaVargas.LocalCases.M11IncomingOuterPartitions
public import DraismaVargas.LocalCases.M11IncomingPartitions
public import DraismaVargas.LocalCases.W4IncomingClassUnion
public import DraismaVargas.LocalCases.W4IncomingCensus
public import DraismaVargas.LocalCases.W4IncomingPrunedFibre
public import DraismaVargas.LocalCases.TargetPartitionNormalization

@[expose] public section

/-!
# The per-member core of an incoming-member identification

Every incoming-member identification -- `W3Nd2Incoming*`, `W3Nd3Incoming*`,
`M11Incoming*`, `W4Incoming*` -- repeats the same three steps once per member of
its candidate family:

1. read the actual incoming target as the member's outgoing target, through
   the member's own side assignment (`memberTargetIso`), and record the
   literal `Option` column dictionary (`memberTargetIso_occurrence`);
2. compare the three partitions that live at the contracted wall -- the two
   restored endpoints and the contracted occurrence -- against the member's
   pasted local resolution (`wall_blocks_of_dictionary`);
3. package the family's dichotomy, the per-member placements and the
   per-member normalization receipts into one indexed exit
   (`exists_member_normalization_of_family`).

This module states those three steps once, **with no star, no profile, no
figure and no member index in any statement**, so that a case with `n`
members writes step 2 once per member as an application rather than as a
fresh eighty-line proof, and writes step 3 once rather than as a hand-built
`n`-fold disjunction.

Section H' (`block_eq_of_anchored_dictionary`) widens step 2's single
distinguished class to a finite set of anchors, each with its own named
partition; section H and the one-anchor variants of the valency-two and
shift cases are its one-element-anchor instances.

## What is deliberately *not* here

The partition algebra
(`W3Nd2IncomingMemberMatching.sameBlocks_of_block_eq_local` and friends), the
candidate-datum dictionary (`candidate_vertexPartition_old_wall`, ...), the
whole-cover exhaustion (`sameBlocks_of_wall_blocks`), the normalization
receipt (`NormalizedAgainst` / `normalizedAgainst`) and the `r = 0` background
census are not restated here: they live in the modules where they are proved,
and any module that can import those can use them.

## The limit-matrix chain does not enter

`wall_blocks_of_dictionary` takes its **six block-dictionary facts as
hypotheses** -- three on the distinguished class and three off it.  In the
`w3Nd2` and `w3Nd3` cases those six are supplied by the limit-matrix/stable-graph modules
(`W3Nd2Background`, `W3Nd2StableLift`, `W3Nd2Survival`, `W3Nd2FineCandidates`;
`W3Nd3LimitMatrix`, `W3Nd3StableGraph`, `W3Nd3SourceCandidates`), each of which
is above this module.  Taking them as hypotheses is what keeps this module's
import closure free of that chain, so that an extraction on the limit-matrix
side and this one stay independent.

## Placement

This module sits below every matching layer: its imports are
`M11IncomingOuterPartitions`, `M11IncomingPartitions`, `W4IncomingClassUnion`,
`W4IncomingCensus`, `W4IncomingPrunedFibre` and `TargetPartitionNormalization`,
none of which imports any matching module.  In particular a W2-side case can
use it without acquiring any dependency on the W3 chain.
-/

namespace DraismaVargas.LocalCases.IncomingMatchingCore

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open TargetExpansion FullDimensionalSource ResolutionM11
open M11IncomingPartitions M11IncomingCoordinates M11IncomingTargetNormalization

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

/-! ## E. Target placement and the member isomorphism -/

/-- Agreement, up to exchanging the two restored endpoints, with a prescribed
side predicate on the contracted wall star.

This is the hypothesis `M11IncomingTargetNormalization.incomingIso` consumes,
given a name.  It is definitionally `W3Nd2IncomingDirection.Placement`, which
is stated at the nd2 level and is therefore unavailable to a W2-side case. -/
def Placement
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (side : (contract target hab hOne).edges → Bool) : Prop :=
  (∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
    IncomingTargetExpansion.right hc hab hOne edge = side edge) ∨
  (∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
    IncomingTargetExpansion.right hc hab hOne edge = !(side edge))

/-- **The member's target isomorphism.**  The actual incoming target, read as
the outgoing target of an arbitrary assembled candidate at the contracted
wall, through that candidate's own side assignment.

Every case writes this wrapper once per member:
`W3Nd2IncomingDirection.coarseTargetIso` / `fineTargetIso`,
`W3Nd3IncomingMatching`'s pair, `M11IncomingTargetNormalization.splitIso` /
`joinedIso`, `W4IncomingTargetNormalization.targetIso`. -/
noncomputable def memberTargetIso
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hPlacement : Placement hc hab hOne C.right) :
    Utilities.CFGraphIso target
      (graph (contract target hab hOne) ⟨a, hab⟩ C.right) :=
  incomingIso hc hab hOne C.right hPlacement

/-- **The member's literal column dictionary.**  Every incoming `Option`
occurrence, the restored contracted occurrence `none` included, is carried to
the corresponding column of the member's outgoing target. -/
theorem memberTargetIso_occurrence
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hPlacement : Placement hc hab hOne C.right)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (column : Option (contract target hab hOne).edges) :
    GluingTransport.edgeEquiv (memberTargetIso data hc hab hOne C hPlacement)
        (incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ C.right column :=
  incomingIso_occurrence hc hab hOne C.right hPlacement hConnected hGenus column

/-! ## H. The three wall-position comparison -/

/-- The pasted local resolution of a candidate at the contracted incoming
wall.  This is `W3Nd2IncomingMemberMatching.pasted` with the wall datum
instantiated at `contractDatum`; being a reducible abbreviation, the two are
interchangeable wherever both are in scope. -/
noncomputable abbrev memberResolution
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩) :
    LocalResolution degree :=
  LocalResolution.paste ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩)
    C.resolution C.contracts

/-- **The three wall comparisons of one member, from a block dictionary.**

`u` is the original endpoint at which the flag occurrence and the contracted
occurrence both sit; `v` is the other one.  `root` names the distinguished
merged class, `flag` the occurrence whose partition the member's background
blocks are read off, and `flagPartition`, `selectedRight`, `selectedNew` the
three sheet partitions the case's dictionary produces.

The source side supplies: the flag occurrence's partition (`hFlagEq`), its two
incidences (`hFlagAt`, `hContractedAt`), the background transfer at `u`
(`hBgEdge`) and at `v` (`hBgTri`), the refinement and join at `u`
(`hURefines`, `hUJoined`), and the two selected-class identities at `v` and at
the contracted occurrence (`hVSelected`, `hNewSelected`).

The member side supplies six block-dictionary facts, three on the
distinguished class and three off it.  **They are hypotheses**: the cases
prove them in the limit-matrix and stable-graph modules, and taking them
here rather than importing them is what keeps this module independent of that
chain.

This is `W3Nd2IncomingMemberMatching.coarse_wall_blocks` / `fine_wall_blocks`
and `W3Nd3IncomingMatching`'s character-for-character copies of them, stated
once.  Neither a star, nor a profile, nor a figure, nor a member index
occurs. -/
theorem wall_blocks_of_dictionary
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (root : Fin degree) (u v : target.V) (flag : target.edges)
    (flagPartition selectedRight selectedNew : SheetPartition degree)
    (hFlagEq : ∀ sheet, (data.edgePartition flag).block sheet = flagPartition.block sheet)
    (hFlagAt : flag ∈ GluingDatum.incidentEdges u)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges u)
    (hBgEdge : ∀ edge ∈ GluingDatum.incidentEdges u, ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel root sheet →
      (data.edgePartition edge).block sheet = (data.vertexPartition u).block sheet)
    (hBgTri : ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet)
    (hURefines : (data.vertexPartition u).Refines (mergedPartition data a b))
    (hUJoined : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b) root)
    (hVSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition v).block sheet = selectedRight.block sheet)
    (hNewSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (data.edgePartition contracted).block sheet = selectedNew.block sheet)
    (hLeftSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).left.block sheet =
        (mergedPartition data a b).block sheet)
    (hRightSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).right.block sheet = selectedRight.block sheet)
    (hNewMember : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).newEdge.block sheet = selectedNew.block sheet)
    (hLeftBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).left.block sheet = flagPartition.block sheet)
    (hRightBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).right.block sheet =
        (mergedPartition data a b).block sheet)
    (hNewBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).newEdge.block sheet = flagPartition.block sheet) :
    (∀ sheet, (data.vertexPartition u).block sheet =
        (memberResolution data hc hab hOne C).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition v).block sheet =
        (memberResolution data hc hab hOne C).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (memberResolution data hc hab hOne C).newEdge.block sheet) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · refine Eq.trans ?_ (hLeftSelected sheet hSel).symm
      ext other
      rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
      exact ⟨fun h ↦ hURefines.rel h, fun h ↦ hUJoined sheet other hSel (hSel.trans h)⟩
    · exact ((hBgEdge _ hFlagAt sheet hSel).symm.trans (hFlagEq sheet)).trans
        (hLeftBackground sheet hSel).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · exact (hVSelected sheet hSel).trans (hRightSelected sheet hSel).symm
    · exact (hBgTri sheet hSel).trans (hRightBackground sheet hSel).symm
  · intro sheet
    by_cases hSel : (mergedPartition data a b).Rel root sheet
    · exact (hNewSelected sheet hSel).trans (hNewMember sheet hSel).symm
    · exact ((hBgEdge _ hContractedAt sheet hSel).trans
        ((hBgEdge _ hFlagAt sheet hSel).symm.trans (hFlagEq sheet))).trans
        (hNewBackground sheet hSel).symm

/-- **`wall_blocks_of_dictionary` in the shape a fully joined member supplies
it.**  When the member carries the whole distinguished class at both restored
endpoints and at the contracted occurrence -- the `M^{(1)}`-style orientation --
the two selected-class identities `hVSelected` and `hNewSelected` are not
separate inputs: they follow from the refinement and join data, exactly as
`W3Nd2IncomingMemberMatching.coarse_wall_blocks` derives them. -/
theorem wall_blocks_of_dictionary_of_joined
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (C : BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (root : Fin degree) (u v : target.V) (flag : target.edges)
    (flagPartition : SheetPartition degree)
    (hFlagEq : ∀ sheet, (data.edgePartition flag).block sheet = flagPartition.block sheet)
    (hFlagAt : flag ∈ GluingDatum.incidentEdges u)
    (hContractedAt : contracted ∈ GluingDatum.incidentEdges u)
    (hBgEdge : ∀ edge ∈ GluingDatum.incidentEdges u, ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel root sheet →
      (data.edgePartition edge).block sheet = (data.vertexPartition u).block sheet)
    (hBgTri : ∀ sheet : Fin degree,
      ¬ (mergedPartition data a b).Rel root sheet →
      (data.vertexPartition v).block sheet = (mergedPartition data a b).block sheet)
    (hURefines : (data.vertexPartition u).Refines (mergedPartition data a b))
    (hVRefines : (data.vertexPartition v).Refines (mergedPartition data a b))
    (hUJoined : JoinedOnBlock (data.vertexPartition u) (mergedPartition data a b) root)
    (hVJoined : JoinedOnBlock (data.vertexPartition v) (mergedPartition data a b) root)
    (hNewJoined : JoinedOnBlock (data.edgePartition contracted)
      (mergedPartition data a b) root)
    (hLeftSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).left.block sheet =
        (mergedPartition data a b).block sheet)
    (hRightSelected : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).right.block sheet =
        (mergedPartition data a b).block sheet)
    (hNewMember : ∀ sheet, (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).newEdge.block sheet =
        (mergedPartition data a b).block sheet)
    (hLeftBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).left.block sheet = flagPartition.block sheet)
    (hRightBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).right.block sheet =
        (mergedPartition data a b).block sheet)
    (hNewBackground : ∀ sheet, ¬ (mergedPartition data a b).Rel root sheet →
      (memberResolution data hc hab hOne C).newEdge.block sheet = flagPartition.block sheet) :
    (∀ sheet, (data.vertexPartition u).block sheet =
        (memberResolution data hc hab hOne C).left.block sheet) ∧
      (∀ sheet, (data.vertexPartition v).block sheet =
        (memberResolution data hc hab hOne C).right.block sheet) ∧
      (∀ sheet, (data.edgePartition contracted).block sheet =
        (memberResolution data hc hab hOne C).newEdge.block sheet) := by
  refine wall_blocks_of_dictionary data hc hab hOne C root u v flag flagPartition
    (mergedPartition data a b) (mergedPartition data a b) hFlagEq hFlagAt hContractedAt
    hBgEdge hBgTri hURefines hUJoined ?_ ?_ hLeftSelected hRightSelected hNewMember
    hLeftBackground hRightBackground hNewBackground
  · intro sheet hSel
    ext other
    rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
    exact ⟨fun h ↦ hVRefines.rel h, fun h ↦ hVJoined sheet other hSel (hSel.trans h)⟩
  · intro sheet hSel
    ext other
    rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
    exact ⟨fun h ↦ (edgePartition_refines_mergedPartition data hc).rel h,
      fun h ↦ hNewJoined sheet other hSel (hSel.trans h)⟩

/-! ## H'. One wall position over a finite anchor set

Item H compares the three wall positions against **one** distinguished class
and puts everything else in a single background bucket.  A case whose member is
not constant off one class -- `{w2-r1}`, whose pasted resolution takes one
value above `A₀`, another above `B₀` and the whole wall block elsewhere -- needs
the same comparison over a finite set of anchors.  That is the statement below,
and item H together with the three one-anchor variants
(`W2PIncomingMatching.block_eq_of_split_dictionary`,
`W2MkkIncomingMatching.wall_blocks_of_split_dictionary`,
`W3ShiftIncomingMatching.wall_blocks_of_free_dictionary`) are its one-element
anchor instances.  Neither a star, nor a profile, nor a figure, nor a member
index occurs. -/

section Anchors

/-- **One wall position compared over a finite anchor set, with every half
named.**  Two partitions that agree with one named partition on each anchor's
class and with a common named partition off all of them are equal. -/
theorem block_eq_of_anchored_dictionary {ι : Type*} (wall : SheetPartition degree)
    (root : ι → Fin degree) (anchored : ι → Prop) [DecidablePred anchored]
    (selected : ι → SheetPartition degree) (backgroundPart first second : SheetPartition degree)
    (hFirstSelected : ∀ i, anchored i → ∀ sheet, wall.Rel (root i) sheet →
      first.block sheet = (selected i).block sheet)
    (hSecondSelected : ∀ i, anchored i → ∀ sheet, wall.Rel (root i) sheet →
      second.block sheet = (selected i).block sheet)
    (hFirstBackground : ∀ sheet, (∀ i, anchored i → ¬ wall.Rel (root i) sheet) →
      first.block sheet = backgroundPart.block sheet)
    (hSecondBackground : ∀ sheet, (∀ i, anchored i → ¬ wall.Rel (root i) sheet) →
      second.block sheet = backgroundPart.block sheet)
    (sheet : Fin degree) : first.block sheet = second.block sheet := by
  classical
  by_cases hSheet : ∃ i, anchored i ∧ wall.Rel (root i) sheet
  · obtain ⟨i, hi, hRel⟩ := hSheet
    exact (hFirstSelected i hi sheet hRel).trans (hSecondSelected i hi sheet hRel).symm
  · have hOff : ∀ i, anchored i → ¬ wall.Rel (root i) sheet :=
      fun i hi hRel ↦ hSheet ⟨i, hi, hRel⟩
    exact (hFirstBackground sheet hOff).trans (hSecondBackground sheet hOff).symm

/-- **The two-anchor instance**, in the shape `{w2-r1}`'s two ramification-one
blocks need it: one named partition above `A₀`, another above `B₀`, and one
named background partition off both. -/
theorem block_eq_of_two_block_dictionary (wall : SheetPartition degree)
    (rootFirst rootSecond : Fin degree)
    (selectedFirst selectedSecond backgroundPart first second : SheetPartition degree)
    (hFirstA : ∀ sheet, wall.Rel rootFirst sheet →
      first.block sheet = selectedFirst.block sheet)
    (hSecondA : ∀ sheet, wall.Rel rootFirst sheet →
      second.block sheet = selectedFirst.block sheet)
    (hFirstB : ∀ sheet, wall.Rel rootSecond sheet →
      first.block sheet = selectedSecond.block sheet)
    (hSecondB : ∀ sheet, wall.Rel rootSecond sheet →
      second.block sheet = selectedSecond.block sheet)
    (hFirstBackground : ∀ sheet, ¬ wall.Rel rootFirst sheet → ¬ wall.Rel rootSecond sheet →
      first.block sheet = backgroundPart.block sheet)
    (hSecondBackground : ∀ sheet, ¬ wall.Rel rootFirst sheet → ¬ wall.Rel rootSecond sheet →
      second.block sheet = backgroundPart.block sheet)
    (sheet : Fin degree) : first.block sheet = second.block sheet := by
  by_cases hFirstRel : wall.Rel rootFirst sheet
  · exact (hFirstA sheet hFirstRel).trans (hSecondA sheet hFirstRel).symm
  · by_cases hSecondRel : wall.Rel rootSecond sheet
    · exact (hFirstB sheet hSecondRel).trans (hSecondB sheet hSecondRel).symm
    · exact (hFirstBackground sheet hFirstRel hSecondRel).trans
        (hSecondBackground sheet hFirstRel hSecondRel).symm

end Anchors

/-! ## J. The member-exit combinator -/

/-- **The certified exit of an `n`-member family.**

`selector` is whatever datum the case's dichotomy decides -- an isolated
target direction, a leaf side, a pairing index -- and `value index` is the
value it takes on the `index`-th member.  Given

* a dichotomy `∃ index, selector = value index`,
* a placement for each member that the dichotomy can select,
* a normalization receipt `Receipt index h` for each such member,

the actual incoming datum *is* one of the members, together with its literal
`Option` column dictionary.

The receipt is a parameter rather than a fixed proposition, so that the case
supplies `W3Nd2IncomingMemberMatching.NormalizedAgainst data fullDim
(memberTargetIso ...) (C index).datum ...` and discharges it in one line by
`W3Nd2IncomingMemberMatching.normalizedAgainst`; the receipt lives at the nd2
level and is deliberately not restated here.

It generalizes the hand-written `n`-fold disjunctions
`W3Nd2IncomingMemberMatching.exists_member_normalization` (n = 2),
`W3Nd3IncomingMatching.exists_member_normalization` (n = 2) and
`M11IncomingMatching.exists_matching` (n = 3), which do not scale to families
with three and four members. -/
theorem exists_member_normalization_of_family
    {n : ℕ} {α : Type*}
    (data : GluingDatum target degree)
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (C : Fin n → BalancedGlobal.Candidate (contract target hab hOne) degree
      (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (selector : α) (value : Fin n → α)
    (hDichotomy : ∃ index, selector = value index)
    (hPlacement : ∀ index, selector = value index → Placement hc hab hOne (C index).right)
    (Receipt : ∀ index : Fin n, selector = value index → Prop)
    (hReceipt : ∀ index, ∀ h : selector = value index, Receipt index h) :
    ∃ index : Fin n, ∃ h : selector = value index,
      (∀ column : Option (contract target hab hOne).edges,
          GluingTransport.edgeEquiv
              (memberTargetIso data hc hab hOne (C index) (hPlacement index h))
              (incomingColumnEquiv hc hab hOne column) =
            occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (C index).right column) ∧
        Receipt index h := by
  obtain ⟨index, h⟩ := hDichotomy
  exact ⟨index, h,
    memberTargetIso_occurrence data hc hab hOne (C index) (hPlacement index h)
      hConnected hGenus,
    hReceipt index h⟩

end DraismaVargas.LocalCases.IncomingMatchingCore
