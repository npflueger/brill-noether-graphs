module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquiv

@[expose] public section

/-!
# The descent at a non-anchor wall block of the `K = 0` candidate

Source: Vargas, Part II (arXiv:2609.09109), §5.1: the combinatorial setup at
a non-trivalent wall and the lemma on rigidity above `w_0` (`lemma-above-w0`).

`NonTrivalentValencyFourRowEquiv` proves the local picture at a
non-anchor wall block: the block-local reduction of the guarded background, the
star (`retSide`, `retSide_endpoint`, `retSide_other`), the two counting engines
(`newSourceEdge_dangling_of_no_fine_survivor`,
`newSourceEdge_survives_of_unique_fine_survivor`, `stablePath_newSourceEdge_eq`)
and the retaining-side census (`nonDanglingIncident_ret_dichotomy`).  This
module adds the bookkeeping layer over them.

## What is proved

* **Counting helpers.** `nonDanglingValency_eq_two_of_pair` (a surviving star
  squeezed between two distinct members and a two-element superset has valency
  two) and `isDangling_of_subset_singleton` (a surviving star inside a singleton
  is empty, because surviving valency one is impossible), the two shapes every
  case of the descent ends with.

* **The wall-block vertex, in occurrence form.** `incident_sourceEndpoint_iff`
  restates incidence at `G.sourceEndpoint wall x` as "the target occurrence is
  incident to the wall and the sheet is in the block", and
  `endpointVertex_ret_eq` is the retaining-side analogue of
  `NonTrivalentValencyFourRowEquiv.endpointVertex_fine_eq`: two sheets of one
  block name the same retaining endpoint. `blockRes_newEdge_refines` is the
  refinement the engines' side conditions are checked against.

* **The fine-side census, factored out.** `nonDanglingIncident_fine_cases` --
  a surviving incidence at a fine-side endpoint is the new occurrence of that
  sheet, or a retained survivor of the block assigned to the other side and
  lying in the same new-edge class.

* **The small set lemma.** `eq_of_survivor`: at a wall block of surviving
  valency two, *every* surviving occurrence incident to it is one of the two
  named survivors.  The wall-block vertex is replaced by
  `G.sourceEndpoint wall vertex.1.2` through
  `GluingDatum.sourceEndpoint_eq_iff`, which is what avoids rewriting under
  `vertex.2` (that rewrite is motive-incorrect, because `star`'s type mentions
  `wall`).

* **The first of the four descent cases.** `descent_of_both_retaining`: when
  both survivors of the block are assigned to the retaining side, every new
  occurrence of the block is dangling, the retaining endpoint carries exactly
  the two retained survivors, and they are consecutive there -- so they lie on
  one stable row of the candidate.

## What is not proved here

`NonTrivalentValencyFourDictionary.OrdinaryBlockDescent` itself, and therefore
`rowEquiv` and the unconditional labelling.  `NonTrivalentValencyFourRowDictionary`
proves the other three descent cases, each a short assembly over the lemmas
above:

2. **One survivor on each side.**  `newSourceEdge_survives_of_unique_fine_survivor`
   at the fine survivor's sheet (its uniqueness in that class follows from
   `eq_of_survivor`, since the other survivor is on the retaining side) gives a
   surviving new occurrence, absorbed into the fine survivor's row by
   `stablePath_newSourceEdge_eq`; `nonDanglingIncident_ret_dichotomy` then bounds
   the retaining endpoint by that new occurrence and the retaining survivor, and
   `nonDanglingValency_eq_two_of_pair` closes it.
3. **Both on the fine side, one new-edge class.**  The dichotomy bounds the
   retaining endpoint by the single new occurrence of that class, so
   `isDangling_of_subset_singleton` makes it dangling; the common fine endpoint
   then carries exactly the two retained survivors by
   `nonDanglingIncident_fine_cases`.
4. **Both on the fine side, two new-edge classes.**  Two surviving new
   occurrences, each absorbed into its survivor's row, and they are the only two
   objects at the retaining endpoint.

The one technical step shared by 2--4 is transporting the engines, which are
stated at a sheet `y` in terms of `coarse.repr y`, to the block's chosen sheet:
`coarse.Rel vertex.1.2 y` *is* `coarse.repr vertex.1.2 = coarse.repr y`, so it
rewrites the side and class conditions directly.

Nothing here touches the incoming-cover-to-wall-datum transport; in
particular `StablePathFacetContraction.wallLabelling` is exactly the
`labelling₀` that `NonTrivalentValencyFourDictionary.labelling` takes, and the
re-indexing of the candidate's `Option coordinate` labelling onto the incoming
`coordinate` (the `none` column against the contracted column) belongs with
`rowEquiv`.

## Consumers

`NonTrivalentValencyFourDictionary.retainedRow` (through
`OrdinaryBlockDescent`), and the boundary dispatcher for Part II case
`{v4-nd4}` (`NonTrivalentValencyFourDispatcher`).
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourDescent

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero.PrescribedPairing
open DraismaVargas.LocalCases.NonTrivalentValencyFourBackground
open DraismaVargas.LocalCases.NonTrivalentValencyFourRows
open DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary
open DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquiv

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : WallBlock data wall}
  (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)
  (profile : OrdinaryBlockProfile data star anchor.1)
  (hConnected : graph_connected target) (hGenus : genus target = 0)
  (hValid : data.Valid)

local notation "cand" =>
  (NonTrivalentValencyFourBackground.candidate source pairing hNoGlue
    hRamification profile hConnected hGenus hValid)
local notation "gauged" => (gaugedData source pairing hNoGlue hRamification)
local notation "coarse" =>
  (GluingDatum.vertexPartition
    (gaugedData source pairing hNoGlue hRamification) wall)
local notation "blockRes" =>
  (W4Assembly.blockwiseResolution
    (gaugedData source pairing hNoGlue hRamification) star profile.pattern
    pairing)

/-! ## Small counting helpers -/

theorem nonDanglingValency_eq_two_of_pair {v : (cand).datum.SourceVertex}
    {a b : (cand).datum.SourceEdge} (hNe : a ≠ b)
    (hSubset : nonDanglingIncident (cand).datum v ⊆ {a, b})
    (ha : a ∈ nonDanglingIncident (cand).datum v)
    (hb : b ∈ nonDanglingIncident (cand).datum v) :
    nonDanglingValency (cand).datum v = 2 := by
  classical
  have hEq : nonDanglingIncident (cand).datum v = {a, b} := by
    refine Finset.Subset.antisymm hSubset ?_
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ha
    · exact hb
  rw [← card_nonDanglingIncident, hEq,
    Finset.card_insert_of_notMem (by simpa using hNe), Finset.card_singleton]

theorem isDangling_of_subset_singleton {v : (cand).datum.SourceVertex}
    {a : (cand).datum.SourceEdge}
    (hSubset : nonDanglingIncident (cand).datum v ⊆ {a})
    (hIncident : Incident (cand).datum a v) : IsDangling (cand).datum a := by
  classical
  by_contra hSurv
  have hCard := Finset.card_le_card hSubset
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    ((cand).datum_valid
      (gaugedData_valid source pairing hNoGlue hRamification hValid)).1 v
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    (cand).datum hSurv hIncident
  omega

/-! ## The incidence form of a wall-block vertex -/

theorem incident_sourceEndpoint_iff (x : Fin degree) (z : (gauged).SourceEdge) :
    Incident (gauged) z ((gauged).sourceEndpoint wall x) ↔
      z.1.1 ∈ GluingDatum.incidentEdges wall ∧ (coarse).Rel x z.1.2 := by
  rw [incident_iff_target_mem_and_rel]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, ((coarse).rel_repr_right x).trans h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (((coarse).rel_repr_right x).symm).trans h2⟩

theorem blockRes_newEdge_refines (b : Fin degree) :
    (blockRes b).newEdge.Refines (coarse) :=
  (blockRes b).edge_refines_left.trans
    (W4Assembly.blockwiseResolution_contracts (gauged) star profile.pattern
      pairing b).left_refines

theorem endpointVertex_ret_eq {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) {y : Fin degree}
    (hRel : (coarse).Rel x y) :
    endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) y =
      endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) x := by
  have hPart := (candidate_endpoint_rel_block source pairing hNoGlue
    hRamification profile hConnected hGenus hValid
    (retSide source pairing hNoGlue hRamification profile
      ((coarse).repr x)) hb y).mpr (by rw [retSide_endpoint]; exact hRel)
  refine (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl, ?_⟩
  exact hPart.symm.trans
    (((cand).datum.vertexPartition
      (if retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x) then freshVertex target else oldVertex target wall)).rel_repr_right x)

/-- The fine-side endpoint census of a non-anchor block. -/
theorem nonDanglingIncident_fine_cases {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) {f : (cand).datum.SourceEdge}
    (hSurv : ¬ IsDangling (cand).datum f)
    (hIncident : Incident (cand).datum f
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((coarse).repr x)) x)) :
    f = (cand).newSourceEdge x ∨
      ∃ old : (gauged).SourceEdge, ¬ IsDangling (gauged) old ∧
        old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing old.1.1 =
          !retSide source pairing hNoGlue hRamification profile
            ((coarse).repr x) ∧
        (blockRes ((coarse).repr x)).newEdge.Rel x old.1.2 ∧
        f = (cand).oldSourceEdge old := by
  rcases ResolutionPruning.sourceEdge_cases (cand) f with ⟨old, rfl⟩ | ⟨s', rfl⟩
  · right
    obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old source pairing hNoGlue
      hRamification profile hConnected hGenus hValid _ hIncident
    exact ⟨old,
      (fun h ↦ hSurv
        ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
          (gaugedData_valid source pairing hNoGlue hRamification hValid)
          (candidate_sourceGenus source pairing hNoGlue hRamification profile
            hConnected hGenus hValid) old).mpr h)),
      hAt, hSide,
      fine_rel_of_incident source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb hIncident, rfl⟩
  · left
    exact newSourceEdge_eq_of_incident_fine source pairing hNoGlue hRamification
      profile hConnected hGenus hValid hb hIncident


/-! ## The descent at a non-anchor wall block -/

section Descent

/-- **The two survivors of a divalent non-anchor wall block exhaust its
surviving star.**  This is the small set lemma the four descent cases share;
the wall-block vertex is replaced by `sourceEndpoint wall vertex.1.2` to avoid
rewriting under `vertex.2`. -/
theorem eq_of_survivor (first second : NonDanglingEdge (gaugedData source pairing hNoGlue hRamification))
    (vertex : (gaugedData source pairing hNoGlue hRamification).SourceVertex) (hAt : vertex.1.1 = wall)
    (hNe : first ≠ second)
    (hFirst : Incident (gaugedData source pairing hNoGlue hRamification) first.1 vertex)
    (hSecond : Incident (gaugedData source pairing hNoGlue hRamification) second.1 vertex)
    (hValency : nonDanglingValency (gaugedData source pairing hNoGlue hRamification) vertex = 2)
    (z : (gauged).SourceEdge)
    (hzS : ¬ IsDangling (gauged) z)
    (hzAt : z.1.1 ∈ GluingDatum.incidentEdges wall)
    (hzRel : (coarse).Rel vertex.1.2 z.1.2) : z = first.1 ∨ z = second.1 := by
  classical
  have hV : (gauged).sourceEndpoint wall vertex.1.2 = vertex :=
    (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
  rw [← hV] at hFirst hSecond hValency
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  have hSub : ({first.1, second.1} : Finset (gauged).SourceEdge) ⊆
      nonDanglingIncident (gauged)
        ((gauged).sourceEndpoint wall vertex.1.2) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨first.2, hFirst⟩
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨second.2, hSecond⟩
  have hCardPair : ({first.1, second.1} :
      Finset (gauged).SourceEdge).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hNeVal),
      Finset.card_singleton]
  have hEq := Finset.eq_of_subset_of_card_le hSub (by
    rw [card_nonDanglingIncident, hValency, hCardPair])
  have hzMem : z ∈ nonDanglingIncident (gauged)
      ((gauged).sourceEndpoint wall vertex.1.2) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hzS,
      (incident_sourceEndpoint_iff source pairing hNoGlue hRamification _ z).mpr
        ⟨hzAt, hzRel⟩⟩
  rw [← hEq] at hzMem
  simpa using hzMem

/-- **The descent when both survivors are assigned to the retaining side.**
Every new occurrence of the block is then dangling, so the retaining endpoint
carries exactly the two retained survivors and they are consecutive there. -/
theorem descent_of_both_retaining (first second : NonDanglingEdge (gaugedData source pairing hNoGlue hRamification))
    (vertex : (gaugedData source pairing hNoGlue hRamification).SourceVertex) (hAt : vertex.1.1 = wall)
    (hNe : first ≠ second)
    (hFirst : Incident (gaugedData source pairing hNoGlue hRamification) first.1 vertex)
    (hSecond : Incident (gaugedData source pairing hNoGlue hRamification) second.1 vertex)
    (hValency : nonDanglingValency (gaugedData source pairing hNoGlue hRamification) vertex = 2)
    (hbAnchor : ¬ (GluingDatum.vertexPartition (gaugedData source pairing hNoGlue hRamification) wall).Rel anchor.1
      vertex.1.2)
    (hsE : star.right pairing first.1.1.1 =
      retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2))
    (hsF : star.right pairing second.1.1.1 =
      retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2)) :
    (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        first).stablePath =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        second).stablePath := by
  classical
  have hNeVal : first.1 ≠ second.1 := fun h ↦ hNe (Subtype.ext h)
  obtain ⟨hAtE, hRelE⟩ := (incident_sourceEndpoint_iff source pairing hNoGlue
    hRamification _ first.1).mp
      (by
        have hV : (gauged).sourceEndpoint wall vertex.1.2 = vertex :=
          (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
        rw [hV]; exact hFirst)
  obtain ⟨hAtF, hRelF⟩ := (incident_sourceEndpoint_iff source pairing hNoGlue
    hRamification _ second.1).mp
      (by
        have hV : (gauged).sourceEndpoint wall vertex.1.2 = vertex :=
          (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
        rw [hV]; exact hSecond)
  have hRetIncid : ∀ z : (gauged).SourceEdge,
      z.1.1 ∈ GluingDatum.incidentEdges wall →
      (coarse).Rel vertex.1.2 z.1.2 →
      star.right pairing z.1.1 =
        retSide source pairing hNoGlue hRamification profile
          ((coarse).repr vertex.1.2) →
      Incident (cand).datum ((cand).oldSourceEdge z)
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid
          (retSide source pairing hNoGlue hRamification profile
            ((coarse).repr vertex.1.2)) vertex.1.2) := by
    intro z hzAt hzRel hzSide
    have h := retainedEdge_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid z.1.1 hzAt _ hzSide z.1.2
    rw [GluingDatum.sourceEdge_self,
      endpointVertex_ret_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hbAnchor hzRel] at h
    exact h
  have hSurvE : ¬ IsDangling (cand).datum ((cand).oldSourceEdge first.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ first.2
  have hSurvF : ¬ IsDangling (cand).datum ((cand).oldSourceEdge second.1) :=
    ResolutionSurvival.not_isDangling_oldSourceEdge _
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _ second.2
  refine stablePath_eq_of_consecutive ⟨fun h ↦ hNeVal
    (ResolutionCut.oldSourceEdge_injective (cand) (congrArg Subtype.val h)),
    endpointVertex source pairing hNoGlue hRamification profile hConnected
      hGenus hValid
      (retSide source pairing hNoGlue hRamification profile
        ((coarse).repr vertex.1.2)) vertex.1.2,
    hRetIncid first.1 hAtE hRelE hsE, hRetIncid second.1 hAtF hRelF hsF, ?_⟩
  refine nonDanglingValency_eq_two_of_pair source pairing hNoGlue hRamification
    profile hConnected hGenus hValid
    (fun h ↦ hNeVal (ResolutionCut.oldSourceEdge_injective (cand) h)) ?_
    ((mem_nonDanglingIncident _ _ _).mpr
      ⟨hSurvE, hRetIncid first.1 hAtE hRelE hsE⟩)
    ((mem_nonDanglingIncident _ _ _).mpr
      ⟨hSurvF, hRetIncid second.1 hAtF hRelF hsF⟩)
  intro f hf
  obtain ⟨hfS, hfI⟩ := (mem_nonDanglingIncident _ _ _).mp hf
  rcases nonDanglingIncident_ret_dichotomy source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hbAnchor hfS hfI with
    ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩ | ⟨old, hoS, hoAt, hoSide, hoRel, rfl⟩
  · rcases eq_of_survivor source pairing hNoGlue hRamification first second
      vertex hAt hNe hFirst hSecond hValency old hoS hoAt hoRel with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  · exfalso
    rcases eq_of_survivor source pairing hNoGlue hRamification first second
      vertex hAt hNe hFirst hSecond hValency old hoS hoAt hoRel with rfl | rfl
    · exact absurd (hsE.symm.trans hoSide) (by simp)
    · exact absurd (hsF.symm.trans hoSide) (by simp)

end Descent

end DraismaVargas.LocalCases.NonTrivalentValencyFourDescent
