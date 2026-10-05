module

public import DraismaVargasCount.BallotMultiplicity
public import DraismaVargasCount.BallotSlopeDiagonalBridge

@[expose] public section

/-!
# The ballot core identification

**Source.**  Vargas, Part II (arXiv:2609.09109): the lemma describing the combinatorial
structure of a full-dimensional morphism from a caterpillar of loops
(`lm:combinatorial-structure-caterpillar-of-loops`), and part (2) of the proposition on
caterpillar slopes and ballot sequences (`prop-caterpillar-ballot`): every ballot slope
sequence determines a tropical morphism.  This module builds the branch-vertex and incidence
dictionary `CoreIdentification (catCore m) (ballotDatum m s)`, for **every** `m` and **every**
slope sequence `s`, and with it the fibre member of every slope sequence.

## What the dictionary is for

`BallotMultiplicity.ballotMemberOf`, `ballotMember`, `ballotCoords` and `ballotRealizes` all
take `ident : CoreIdentification (catCore m) (ballotDatum m s)` as an explicit argument.
`FibreCaterpillar.catIdent` supplies one for `caterpillarDatum m`, which is
`ballotDatum m (zig m)` by `BallotDatum.ballotDatum_zig`; that transport reaches the zig-zag
sequence only.

## The route

Not a transport.  `ballotDatum_zig` is an equality of *data* at one sequence and says nothing
about a general `s`; the dictionary is built directly, from the inputs in `BallotValency`.  The
valency census of the ballot source is **numerically independent of the slope sequence** -- a
spine block of `s_i` sheets is still a single source occurrence -- so the census that
`FibreCaterpillar` ran for the zig-zag caterpillar runs verbatim for every `s`:

* `bNonDanglingValency_core_root/stem/junction/lastStem` give surviving valency
  three at the `2g - 2` non-leaf target vertices, and
  `bNonDanglingValency_core_leaf/lastLeaf` give two at the `g` folded tips;
* `bSourceVertex_eq_core_or_other` and `bNonDanglingValency_other_eq_zero` say
  every other source vertex is inert;
* `bNonDanglingIncident_core_eq_visible` is the exact surviving star.

So the branch vertices of the stable source of `ballotDatum m s` are the same
`Fin (4m+2)` for every `s`, indexed by the same `FibreCaterpillar.branchIdx`,
and the incidence census is the same one `FibreCaterpillar.coreIncidence_catCore`
already matched against `catCore m`.

## What is proved

* `bNonDanglingValency_branch`, `bNonDanglingValency_not_branch`,
  `bEq_bCore_of_branch` -- the branch classification at a general slope
  sequence: a source vertex of surviving valency at least three is the
  spine-sheet vertex `bCore m s v` over a non-leaf target vertex `v`.
* `bBranchEquiv m s : BranchVertex (ballotDatum m s) ≃ Fin (4 * m + 2)`.
* `row_bMainND`, `row_symm_eq_bMainND` -- the row equivalence of the labelling
  `ballotLabelling m s` is the "stable row is the target occurrence beneath it" map, so
  `(ballotLabelling m s).row.symm slot` is the stable path of the spine-sheet
  occurrence over `slot`, definitionally.
* `bIncidenceCount_bCore` -- the incidence census at a general slope sequence.
* **`ballotIdent m s : CoreIdentification (catCore m) (ballotDatum m s)`** -- the
  headline, for every `m` and every `s`.  Its `row` field is
  `(ballotLabelling m s).row` itself.
* `ballotIdent_row`, `ballotIdent_vertex` -- the two fields, read back by `rfl`.
* `ballotIdent_vertex_val` and `catIdent_vertex_val` -- consistency with
  `FibreCaterpillar.catIdent`, stated as the agreement of the two
  dictionaries' *values* (both index a branch by `branchIdx` of its target
  vertex) rather than as a transport: the two are terms of different,
  defeq-after-`ballotDatum_zig`, types.
* `ballotFamilyMember m request s` -- **the member for every slope sequence**,
  with `ballotFamilyMember_open`, `ballotFamilyMember_hasOddMult`,
  `ballotFamilyMember_absMult`, `ballotFamilyMember_matrix` and
  `ballotFamilyMember_slotMap`.
* **`ballotFamily`** -- `Count.CaterpillarBallot.BallotFamily m request` is
  inhabited for every `m` and every positive request.
* **`catalan_le_openOddCount`** -- hence the lower bound of the base count:
  `catalan (m + 1) ≤ GeometricFibre.openOddCount (catCore m) request (m + 2)`
  for every positive request.  `five_le_openOddCount_genusSix` is the genus-six
  instance; `two_le_openOddCount_genusFour` is genus four.

## What is not proved here

* **No exhaustion.**  The matching upper bound needs every open member of odd
  multiplicity to be one of these members up to isomorphism over the core, and nothing
  below supplies it.  In genus six it is `CaterpillarAllMembers.cls_eq_ballot_genusSix`,
  which compares every member with `ballotFamilyMember` and feeds the base count
  `Assembly.baseCount_genusSix` (step 1 of the assembly).
* **No genericity hypothesis is used.**  Part II's count (`prop-divisors-on-chain`)
  assumes that the edge lengths of the metric caterpillar are pairwise distinct; that
  belongs to the exhaustion half.  `catalan_le_openOddCount` below assumes only
  `0 < request slot` at every slot, which is strictly weaker, and is what the open cone
  needs.
* **The identification is not claimed unique.**  Nothing below says that
  `ballotIdent m s` is the only `CoreIdentification (catCore m) (ballotDatum m s)`,
  nor that `FibreMember.ident` is determined by the datum.  The fibre is
  labelled precisely because it is not.
* **Nothing about subdivision specifications.**  `catCore m` is the caterpillar
  **of loops** and is not a `SubdivisionGraph.Spec.core` (`Spec` demands
  `core_loopless`); no statement below mentions `Spec` or a pencil.
* **No `Aut`-triviality, no descent.**  `GeometricFibre.cls` enters only through
  `BallotSlopes.ballotFamilyOfBallotMatrix`, whose injectivity obligation is
  discharged there by the separation of the ballot diagonals; nothing new about the
  quotient is proved here.
-/

namespace DraismaVargas.Count.BallotCoreIdentification

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount incidentEdges mem_incidentEdges)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.Count
open DraismaVargas.Count.BallotDatum
open DraismaVargas.Count.BallotFullDimensional
open DraismaVargas.Count.BallotPruning
open DraismaVargas.Count.BallotValency
open DraismaVargas.Count.BallotMultiplicity
open DraismaVargas.Count.FibreCaterpillar
open Utilities.Certificate.ExplicitPotential (Core)

variable {m : ℕ}

/-! ## 1.  The branch vertices of the ballot source -/

/-- **Branches have surviving valency three**, at every slope sequence. -/
theorem bNonDanglingValency_branch (s : Slopes (2 * (m + 1)))
    {vertex : (catTree m).V} (hBranch : IsBranchIndex m vertex) :
    nonDanglingValency (ballotDatum m s) (bCore m s vertex) = 3 := by
  rcases vertexClass m vertex with hRoot | hLeaf | hStem | hLastLeaf |
      hJunction | hLastStem
  · rw [bNonDanglingValency_core_root s vertex hRoot]
  · exact absurd hLeaf hBranch.1
  · rw [bNonDanglingValency_core_stem s vertex hStem.1 hStem.2.1 hStem.2.2]
  · exact absurd hLastLeaf hBranch.2
  · rw [bNonDanglingValency_core_junction s vertex hJunction.1 hJunction.2]
  · rw [bNonDanglingValency_core_lastStem s vertex hLastStem]

/-- **The folded tips have surviving valency two**, at every slope sequence. -/
theorem bNonDanglingValency_not_branch (s : Slopes (2 * (m + 1)))
    {vertex : (catTree m).V} (hBranch : ¬ IsBranchIndex m vertex) :
    nonDanglingValency (ballotDatum m s) (bCore m s vertex) = 2 := by
  unfold IsBranchIndex at hBranch
  rw [not_and_or, not_ne_iff, not_ne_iff] at hBranch
  rcases hBranch with hLeaf | hLastLeaf
  · exact bNonDanglingValency_core_leaf s vertex hLeaf
  · exact bNonDanglingValency_core_lastLeaf s vertex hLastLeaf

/-- **Every branch vertex of the stable ballot source is the spine-sheet vertex
over a non-leaf target vertex**, at every slope sequence. -/
theorem bEq_bCore_of_branch (s : Slopes (2 * (m + 1)))
    {x : (ballotDatum m s).SourceVertex}
    (hValency : 3 ≤ nonDanglingValency (ballotDatum m s) x) :
    x = bCore m s x.1.1 ∧ IsBranchIndex m x.1.1 := by
  have hCore : x = bCore m s x.1.1 := by
    rcases bSourceVertex_eq_core_or_other s x with hCore | hOther
    · exact hCore
    · exfalso
      have hSelf := (ballotDatum m s).sourceEndpoint_self x
      rw [← hSelf, bNonDanglingValency_other_eq_zero s x.1.1 hOther] at hValency
      omega
  refine ⟨hCore, ?_⟩
  by_contra hBranch
  rw [hCore, bNonDanglingValency_not_branch s hBranch] at hValency
  omega

/-- The core index of a branch vertex of the ballot source. -/
noncomputable def bBranchIndexOf (m : ℕ) (s : Slopes (2 * (m + 1)))
    (branch : BranchVertex (ballotDatum m s)) : Fin (4 * m + 2) :=
  ⟨branchIdx branch.1.1.1.val,
    branchIdx_lt (isBranchIndex_le (bEq_bCore_of_branch s branch.2).2)⟩

/-- **The branch vertices of the stable ballot source, indexed by `Fin (2g-2)`**,
for every slope sequence.  The indexing is the same `branchIdx v = 2v/3` as for
the zig-zag caterpillar: the valency census of `BallotValency` does not see the
slope sequence. -/
noncomputable def bBranchEquiv (m : ℕ) (s : Slopes (2 * (m + 1))) :
    BranchVertex (ballotDatum m s) ≃ Fin (4 * m + 2) where
  toFun := bBranchIndexOf m s
  invFun index := ⟨bCore m s (branchVertexOf m index),
    (bNonDanglingValency_branch s (isBranchIndex_branchVertexOf m index)).ge⟩
  left_inv branch := by
    obtain ⟨hCore, hBranch⟩ := bEq_bCore_of_branch s branch.2
    have hvertex : branchVertexOf m (bBranchIndexOf m s branch) = branch.1.1.1 :=
      Fin.ext (branchVal_branchIdx hBranch.1)
    refine Subtype.ext ?_
    show bCore m s (branchVertexOf m (bBranchIndexOf m s branch)) = branch.1
    rw [hvertex]
    exact hCore.symm
  right_inv index := Fin.ext (branchIdx_branchVal index.val)

@[simp] theorem bBranchEquiv_apply (m : ℕ) (s : Slopes (2 * (m + 1)))
    (branch : BranchVertex (ballotDatum m s)) :
    (bBranchEquiv m s branch).val = branchIdx branch.1.1.1.val := rfl

@[simp] theorem bBranchEquiv_symm_apply (m : ℕ) (s : Slopes (2 * (m + 1)))
    (index : Fin (4 * m + 2)) :
    ((bBranchEquiv m s).symm index).1 = bCore m s (branchVertexOf m index) := rfl

/-! ## 2.  The stable rows are the target occurrences -/

/-- The row equivalence of `ballotLabelling m s` reads a stable row as the target
occurrence beneath it, so the spine-sheet occurrence over `i` is labelled `i`. -/
theorem row_bMainND (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    (ballotLabelling m s).row (bMainND m s i).stablePath = i :=
  (catEdgeEquiv m).symm_apply_apply i

/-- Hence the inverse of the row equivalence names the spine-sheet occurrence's
stable row. -/
theorem row_symm_eq_bMainND (s : Slopes (2 * (m + 1))) (i : Fin (6 * m + 3)) :
    (ballotLabelling m s).row.symm i = (bMainND m s i).stablePath :=
  (ballotLabelling m s).row.symm_apply_eq.mpr (row_bMainND s i).symm

/-! ## 3.  The incidence census of the stable ballot source -/

/-- **The complete incidence census of the stable ballot source.**  At a
spine-sheet vertex the surviving occurrences of the stable row `slot` are the
visible occurrences over the target occurrence `slot`: two folded loop flags
over a leaf edge, one stem or spine occurrence otherwise, and none at all when
the target occurrence is not incident.  Identical for every slope sequence. -/
theorem bIncidenceCount_bCore (s : Slopes (2 * (m + 1))) (vertex : (catTree m).V)
    (slot : Fin (6 * m + 3)) :
    incidenceCount (ballotDatum m s) (bCore m s vertex)
        ((ballotLabelling m s).row.symm slot) =
      if slot ∈ incidentIndices m vertex then
        (if IsLeafEdge m slot then 2 else 1) else 0 := by
  classical
  have hStar := bNonDanglingIncident_core_eq_visible s vertex
  have hCard : ((incidentEdges (ballotDatum m s) (bCore m s vertex)).filter
      fun edge ↦ edge.stablePath = (bMainND m s slot).stablePath).card =
      (if slot ∈ incidentIndices m vertex then bVisible m s slot
        else (∅ : Finset ((ballotDatum m s).SourceEdge))).card := by
    refine Finset.card_bij (fun edge _ ↦ edge.1) ?_ ?_ ?_
    · intro edge hEdge
      rw [Finset.mem_filter, mem_incidentEdges] at hEdge
      have hMem : edge.1 ∈ nonDanglingIncident (ballotDatum m s) (bCore m s vertex) :=
        (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hEdge.1⟩
      rw [hStar] at hMem
      obtain ⟨index, hIndex, hVisible⟩ := Finset.mem_biUnion.mp hMem
      have hTarget := bVisible_target s hVisible
      have hSymm : (catEdgeEquiv m).symm (occ m index) = index :=
        (catEdgeEquiv m).symm_apply_eq.mpr rfl
      have hRow : edge.stablePath = (bMainND m s index).stablePath := by
        rw [bEdge_stablePath_eq_main s edge, hTarget, hSymm]
      have hEq : index = slot := by
        have hPath := hRow.symm.trans hEdge.2
        have hIndexEq := congrArg (ballotLabelling m s).row hPath
        rwa [row_bMainND, row_bMainND] at hIndexEq
      subst hEq
      rw [ite_eq_left hIndex]
      exact hVisible
    · intro first _ second _ hEq
      exact Subtype.ext hEq
    · intro occurrence hOccurrence
      by_cases hIndex : slot ∈ incidentIndices m vertex
      · rw [ite_eq_left hIndex] at hOccurrence
        have hMem : occurrence ∈ nonDanglingIncident (ballotDatum m s)
            (bCore m s vertex) := by
          rw [hStar]
          exact Finset.mem_biUnion.mpr ⟨slot, hIndex, hOccurrence⟩
        obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
        have hSymm : (catEdgeEquiv m).symm (occ m slot) = slot :=
          (catEdgeEquiv m).symm_apply_eq.mpr rfl
        refine ⟨⟨occurrence, hSurvives⟩, Finset.mem_filter.mpr
          ⟨(mem_incidentEdges _ _ _).mpr hIncident, ?_⟩, rfl⟩
        rw [bEdge_stablePath_eq_main s ⟨occurrence, hSurvives⟩,
          show ((⟨occurrence, hSurvives⟩ :
            NonDanglingEdge (ballotDatum m s)) : (ballotDatum m s).SourceEdge).1.1
              = occ m slot from bVisible_target s hOccurrence,
          hSymm]
      · rw [ite_eq_right hIndex] at hOccurrence
        exact absurd hOccurrence (by simp)
  rw [incidenceCount, row_symm_eq_bMainND, hCard]
  by_cases hIndex : slot ∈ incidentIndices m vertex
  · rw [ite_eq_left hIndex, ite_eq_left hIndex, card_bVisible]
  · rw [ite_eq_right hIndex, ite_eq_right hIndex, Finset.card_empty]

/-! ## 4.  The identification, for every slope sequence -/

/-- **The core identification.**  The stable graph of the ballot gluing datum *is*
the caterpillar of loops `catCore m`, for **every** slope sequence `s` -- with
the stable rows numbered by the target occurrences they lie over, which is the
row equivalence of `ballotLabelling m s`. -/
noncomputable def ballotIdent (m : ℕ) (s : Slopes (2 * (m + 1))) :
    CoreIdentification (catCore m) (ballotDatum m s) where
  vertex := bBranchEquiv m s
  row := (ballotLabelling m s).row
  incidence branch slot := by
    obtain ⟨hCore, hBranch⟩ := bEq_bCore_of_branch s branch.2
    rw [show branch.1 = bCore m s branch.1.1.1 from hCore,
      bIncidenceCount_bCore s branch.1.1.1 slot,
      coreIncidence_catCore m hBranch (bBranchEquiv m s branch) rfl slot]

@[simp] theorem ballotIdent_row (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (ballotIdent m s).row = (ballotLabelling m s).row := rfl

@[simp] theorem ballotIdent_vertex (m : ℕ) (s : Slopes (2 * (m + 1))) :
    (ballotIdent m s).vertex = bBranchEquiv m s := rfl

/-- Consistency with `FibreCaterpillar.catIdent` at the zig-zag: both
dictionaries index a branch vertex by `branchIdx` of its target vertex.  The two
are terms of different (defeq-after-`ballotDatum_zig`) types, so this is the
agreement of their values, not a transport. -/
theorem ballotIdent_vertex_val (m : ℕ) (s : Slopes (2 * (m + 1)))
    (branch : BranchVertex (ballotDatum m s)) :
    ((ballotIdent m s).vertex branch).val = branchIdx branch.1.1.1.val := rfl

theorem catIdent_vertex_val (m : ℕ) (branch : BranchVertex (caterpillarDatum m)) :
    ((catIdent m).vertex branch).val = branchIdx branch.1.1.1.val := rfl

/-! ## 5.  The members, for every slope sequence -/

/-- **The ballot member at a slope sequence.**  This is
`BallotMultiplicity.ballotMember` with its one remaining argument, the core
identification `ballotIdent m s`, supplied. -/
noncomputable def ballotFamilyMember (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1))) : FibreMember (catCore m) request (m + 2) :=
  ballotMember m s request (ballotIdent m s)

theorem ballotFamilyMember_open (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) (s : Slopes (2 * (m + 1))) :
    (ballotFamilyMember m request s).Open :=
  ballotMember_open (ballotIdent m s) hRequest

theorem ballotFamilyMember_absMult (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1))) : (ballotFamilyMember m request s).absMult = 1 :=
  ballotMember_absMult m s request (ballotIdent m s)

theorem ballotFamilyMember_hasOddMult (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1))) : (ballotFamilyMember m request s).HasOddMult :=
  ballotMember_hasOddMult m s request (ballotIdent m s)

/-- The member carries the ballot length matrix on the nose: its `fullDim` field
is pinned to `ballotFullDim m s` by `ballotMemberOf`. -/
theorem ballotFamilyMember_matrix (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1))) :
    (ballotFamilyMember m request s).matrix =
      GluingDatum.LengthMatrixPresentation.matrix (ballotLabelling m s).presentation :=
  rfl

/-- **The member labels its stable rows by the core's own slots.**  This is the
`hslot` normalisation hypothesis of `BallotSlopes.ballotFamilyOfBallotMatrix`,
and it holds because `ballotIdent`'s row field *is* the row equivalence of
`ballotLabelling m s`.  (It is `Equiv.apply_symm_apply`, not `rfl`.) -/
theorem ballotFamilyMember_slotMap (m : ℕ) (request : Fin (6 * m + 3) → ℚ)
    (s : Slopes (2 * (m + 1))) (r : Fin (6 * m + 3)) :
    (ballotFamilyMember m request s).slotMap r = r :=
  (ballotLabelling m s).row.apply_symm_apply r

/-- **`Count.CaterpillarBallot.BallotFamily` is inhabited**, for every `m` and
every positive request. -/
noncomputable def ballotFamily (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    CaterpillarBallot.BallotFamily m request :=
  BallotSlopes.ballotFamilyOfBallotMatrix (ballotFamilyMember m request)
    (ballotFamilyMember_open m hRequest) (ballotFamilyMember_hasOddMult m request)
    (ballotFamilyMember_matrix m request) (ballotFamilyMember_slotMap m request)
    fun slot ↦ (hRequest slot).ne'

/-- **The Catalan lower bound.**  Over the metric caterpillar of loops of genus
`g = 2m + 2` with any positive edge lengths, the labelled fibre has at least
`catalan (m + 1)` open classes of odd multiplicity. -/
theorem catalan_le_openOddCount (m : ℕ) {request : Fin (6 * m + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    catalan (m + 1) ≤ GeometricFibre.openOddCount (catCore m) request (m + 2) :=
  CaterpillarBallot.catalan_le_openOddCount (ballotFamily m hRequest)

/-- **Genus six**: five open classes of odd multiplicity. -/
theorem five_le_openOddCount_genusSix {request : Fin (6 * 2 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    5 ≤ GeometricFibre.openOddCount (catCore 2) request (2 + 2) :=
  CaterpillarBallot.five_le_openOddCount_genusSix (ballotFamily 2 hRequest)

/-- **Genus four**: two open classes of odd multiplicity. -/
theorem two_le_openOddCount_genusFour {request : Fin (6 * 1 + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    2 ≤ GeometricFibre.openOddCount (catCore 1) request (1 + 2) := by
  have h := catalan_le_openOddCount 1 hRequest
  have hcat : catalan (1 + 1) = 2 := catalan_two
  rwa [hcat] at h

end DraismaVargas.Count.BallotCoreIdentification
