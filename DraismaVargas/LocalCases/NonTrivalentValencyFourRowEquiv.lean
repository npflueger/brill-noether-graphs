module

public import DraismaVargas.LocalCases.NonTrivalentValencyFourDictionary

@[expose] public section

/-!
# The local picture at a non-anchor wall block of the `K = 0` candidate

Source: Vargas, Part II (arXiv:2609.09109), Section 5.1, Lemma `lemma-above-w0`
("rigidity above `w_0`"): the wall-crossing deformation is localized entirely at
the four-valent vertex `A`, and all other vertices in the fibre above `w_0`
remain rigid.  This module is the occurrence-level form of that rigidity for the
outgoing `K = 0` candidate.

`NonTrivalentValencyFourRows` and `NonTrivalentValencyFourDictionary` treat the
*anchor* block: source-genus preservation, the gauged four-branch classifier,
trivalence of the two new endpoints, the bridge as a stable row of its own, and
the retained-row descent away from the wall and at the anchor.  The *non-anchor*
wall blocks are isolated there in the named hypothesis
`NonTrivalentValencyFourDictionary.OrdinaryBlockDescent`.  This module builds
the machinery that hypothesis needs.

## What is proved

* **The candidate's endpoint partitions, block by block.**  `endpoint_rel_iff`
  and `newEdge_rel_iff` reduce the pasted global partitions to the per-block
  resolution with *no* hypothesis on the sheet (this is the general form of
  `NonTrivalentValencyFourDictionary.candidate_vertexPartition_rel_iff`, which
  is stated only at the anchor).  `resolution_rel_of_not_anchor` then unfolds
  the localized guarded
  background: away from the anchor the candidate's resolution is, block by
  block, the canonical W4 pattern `W4Assembly.blockwiseResolution` of the
  guarded census.  `candidate_endpoint_rel_block` and
  `candidate_newEdge_rel_block` are the two statements the rest of the file
  uses.

* **The star picture.**  Every canonical W4 block pattern is a star
  (`NonTrivalentValencyFourRows.isStar_blockwiseResolution`): one endpoint keeps
  the wall partition and the new edge repeats the other endpoint.  `retSide`
  names the side that keeps it, `retSide_endpoint` and `retSide_other` are its
  two defining equations, and `ret_rel_of_incident` / `fine_rel_of_incident`
  read them off an actual incidence.  `newSourceEdge_eq_of_incident_fine` shows
  a new occurrence incident to a fine-side endpoint is *the* new occurrence of
  that sheet, and `endpointVertex_fine_eq` identifies fine-side endpoint
  vertices with a new-edge relation.

* **The two counting engines at a non-anchor block.**
  - `newSourceEdge_dangling_of_no_fine_survivor`: a new occurrence whose fine
    class carries no surviving old occurrence is dangling -- its fine-side
    endpoint would otherwise have surviving valency one, which
    `NonDanglingValency.nonDanglingValency_ne_one` forbids.  This is the
    non-anchor form of
    `NonTrivalentValencyFourDictionary.newSourceEdge_isDangling_of_singleton`.
  - `newSourceEdge_survives_of_unique_fine_survivor`: a new occurrence whose
    fine class carries exactly one surviving old occurrence **survives**, and
    its fine-side endpoint is divalent.  `stablePath_newSourceEdge_eq` is the
    stable-row form: that new occurrence lies on the same stable row of the
    candidate as the old survivor it meets.

  These two are exactly the same-side/opposite-side dichotomy of the paper's
  rigidity statement, occurrence by occurrence.

* **The retaining-side census.**  `nonDanglingIncident_ret_cases` splits a
  surviving incidence at the retaining endpoint into a retained old occurrence
  or a new occurrence of the block, and `nonDanglingIncident_ret_dichotomy`
  refines the second alternative using the first engine: such a new occurrence
  is the new occurrence of a fine class that *carries a survivor assigned to
  the other side*.  So the retaining endpoint of a non-anchor block sees
  exactly one object per survivor of that block: the survivor itself when it is
  assigned to the retaining side, and the new occurrence of its fine class
  otherwise.

## What is not proved here

`OrdinaryBlockDescent` itself, and hence the row equivalence and the
unconditional labelling, are proved in `NonTrivalentValencyFourRowDictionary`
(`ordinaryBlockDescent`) by *bookkeeping with the two engines above*, in four
cases.  Fix a non-anchor block `b` of surviving valency two with survivors
`e, f`, write `T` for `retSide b`:

1. **Both survivors on side `T`.**  No fine class carries a survivor, so every
   new occurrence of `b` is dangling by
   `newSourceEdge_dangling_of_no_fine_survivor`; the retaining endpoint's
   surviving star is then `{e, f}` and they are consecutive there.  The step
   needed is the retaining-endpoint census, the exact analogue of the two
   `hSubset` blocks inside the two engines, with `ret_rel_of_incident` in place
   of `fine_rel_of_incident`.
2. **One on each side.**  `newSourceEdge_survives_of_unique_fine_survivor` at
   the fine survivor's sheet gives a surviving new occurrence joined to it
   (`stablePath_newSourceEdge_eq`); the retaining endpoint then carries exactly
   that new occurrence and the retaining survivor, so they are consecutive.
3. **Both on side `!T`, same fine class.**  The retaining endpoint would carry
   only the one new occurrence, so surviving valency one -- impossible; hence
   that new occurrence is dangling and the two survivors are consecutive at
   their common fine endpoint.
4. **Both on side `!T`, different fine classes.**  Two surviving new
   occurrences by `newSourceEdge_survives_of_unique_fine_survivor`, each joined
   to its survivor, and they are consecutive at the retaining endpoint.

The retaining-endpoint census is `nonDanglingIncident_ret_dichotomy`; the
descent is exactly the four bookkeeping cases above, run against it and against
the two engines.  Nothing in this file assumes a row dictionary, a
stable type, an outgoing full-dimensional presentation, or any receipt about
the candidate, and nothing here touches the incoming-cover-to-wall-datum
transport.

## Consumers

`NonTrivalentValencyFourDictionary.retainedRow` (through
`OrdinaryBlockDescent`), and the boundary dispatcher for Part II Case
`{v4-nd4}`.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquiv

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

theorem pasteLeft_rel_iff (P : SheetPartition degree)
    (res : Fin degree → LocalResolution degree)
    (hC : ∀ a, (res a).ContractsTo P) (x y : Fin degree) :
    (LocalResolution.paste P res hC).left.Rel x y ↔ (res (P.repr x)).left.Rel x y :=
  SheetPartition.paste_rel_iff P (fun blk ↦ (res blk).left)
    (fun blk ↦ (hC blk).left_refines) x y

theorem pasteRight_rel_iff (P : SheetPartition degree)
    (res : Fin degree → LocalResolution degree)
    (hC : ∀ a, (res a).ContractsTo P) (x y : Fin degree) :
    (LocalResolution.paste P res hC).right.Rel x y ↔
      (res (P.repr x)).right.Rel x y :=
  SheetPartition.paste_rel_iff P (fun blk ↦ (res blk).right)
    (fun blk ↦ (hC blk).right_refines) x y

theorem pasteNewEdge_rel_iff (P : SheetPartition degree)
    (res : Fin degree → LocalResolution degree)
    (hC : ∀ a, (res a).ContractsTo P) (x y : Fin degree) :
    (LocalResolution.paste P res hC).newEdge.Rel x y ↔
      (res (P.repr x)).newEdge.Rel x y :=
  SheetPartition.paste_rel_iff P (fun blk ↦ (res blk).newEdge)
    (fun blk ↦ (res blk).edge_refines_left.trans (hC blk).left_refines) x y

/-- The endpoint partitions of the candidate, block by block, with no
hypothesis on the sheet. -/
theorem endpoint_rel_iff (sideValue : Bool) (x y : Fin degree) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel
        x y ↔
      (if sideValue then ((cand).resolution ((coarse).repr x)).right
        else ((cand).resolution ((coarse).repr x)).left).Rel x y := by
  cases sideValue
  · show (((cand).datum.vertexPartition (oldVertex target wall)).Rel x y) ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
    exact pasteLeft_rel_iff (coarse) (cand).resolution (cand).contracts x y
  · show (((cand).datum.vertexPartition (freshVertex target)).Rel x y) ↔ _
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]
    exact pasteRight_rel_iff (coarse) (cand).resolution (cand).contracts x y

theorem newEdge_rel_iff (x y : Fin degree) :
    (LocalResolution.paste (coarse) (cand).resolution (cand).contracts).newEdge.Rel
        x y ↔
      ((cand).resolution ((coarse).repr x)).newEdge.Rel x y :=
  pasteNewEdge_rel_iff (coarse) (cand).resolution (cand).contracts x y

/-- Away from the anchor block the candidate's resolution is, block by block,
the canonical W4 pattern of the guarded census. -/
theorem resolution_rel_of_not_anchor {x : Fin degree}
    (hb : ¬ (coarse).Rel anchor.1 x) (y : Fin degree) :
    ((((cand).resolution ((coarse).repr x)).left.Rel x y ↔
        (blockwiseResolution (gauged) star profile.pattern pairing
          ((coarse).repr x)).left.Rel x y) ∧
      (((cand).resolution ((coarse).repr x)).right.Rel x y ↔
        (blockwiseResolution (gauged) star profile.pattern pairing
          ((coarse).repr x)).right.Rel x y)) ∧
      (((cand).resolution ((coarse).repr x)).newEdge.Rel x y ↔
        (blockwiseResolution (gauged) star profile.pattern pairing
          ((coarse).repr x)).newEdge.Rel x y) := by
  have hReprNe : ¬ (coarse).Rel anchor.1 ((coarse).repr x) := by
    intro h
    exact hb (h.trans ((coarse).rel_repr_right x).symm)
  have hRes := candidate_resolution_of_not_wall_rel source pairing hNoGlue
    hRamification profile hConnected hGenus hValid ((coarse).repr x) hReprNe
  have hLocal :
      (pairingBackground source pairing hNoGlue hRamification profile hConnected
        hGenus hValid).resolution ((coarse).repr x) =
        BlockLocalBackground.localizedResolution source pairing hNoGlue
          hRamification
          (blockLocalBackground source pairing hNoGlue hRamification profile
            hConnected hGenus hValid) ((coarse).repr x) hReprNe := dite_eq_right hReprNe
  have hOnBlock : LocalResolution.onBlock (coarse) ((coarse).repr x)
      ((blockLocalBackground source pairing hNoGlue hRamification profile
        hConnected hGenus hValid).resolution ((coarse).repr x))
      (fun _ ↦ joinedResolutionAt (coarse)) ((coarse).repr x) =
        (blockLocalBackground source pairing hNoGlue hRamification profile
          hConnected hGenus hValid).resolution ((coarse).repr x) :=
    LocalResolution.onBlock_of_rel _ _ _ _ _ rfl
  rw [hRes, hLocal]
  unfold BlockLocalBackground.localizedResolution
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [pasteLeft_rel_iff, hOnBlock]
    exact Iff.rfl
  · rw [pasteRight_rel_iff, hOnBlock]
    exact Iff.rfl
  · rw [pasteNewEdge_rel_iff, hOnBlock]
    exact Iff.rfl


/-! ## The star picture at a non-anchor wall block -/

local notation "blockRes" =>
  (W4Assembly.blockwiseResolution
    (gaugedData source pairing hNoGlue hRamification) star profile.pattern
    pairing)

/-- Block by block away from the anchor, the candidate's endpoint partitions
are the canonical W4 pattern's. -/
theorem candidate_endpoint_rel_block (sideValue : Bool) {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    (y : Fin degree) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel
        x y ↔
      (if sideValue then
          (blockRes ((GluingDatum.vertexPartition (gauged) wall).repr x)).right
        else
          (blockRes
            ((GluingDatum.vertexPartition (gauged) wall).repr x)).left).Rel
        x y := by
  rw [endpoint_rel_iff]
  rcases resolution_rel_of_not_anchor source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hb y with ⟨⟨hl, hr⟩, _⟩
  cases sideValue
  · exact hl
  · exact hr

theorem candidate_newEdge_rel_block {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    (y : Fin degree) :
    (LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
        (cand).resolution (cand).contracts).newEdge.Rel x y ↔
      (blockRes
        ((GluingDatum.vertexPartition (gauged) wall).repr x)).newEdge.Rel x y := by
  rw [newEdge_rel_iff]
  exact (resolution_rel_of_not_anchor source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hb y).2

/-- The side of a non-anchor block whose endpoint retains the whole wall
block.  Every canonical W4 block pattern is a star: one endpoint keeps the wall
partition and the new edge repeats the other endpoint. -/
noncomputable def retSide (b : Fin degree) : Bool := by
  classical
  exact if (blockRes b).left = GluingDatum.vertexPartition (gauged) wall then
    false else true

theorem retSide_endpoint (b : Fin degree) :
    (if retSide source pairing hNoGlue hRamification profile b then
        (blockRes b).right else (blockRes b).left) =
      GluingDatum.vertexPartition (gauged) wall := by
  classical
  by_cases hLeft :
      (blockRes b).left = GluingDatum.vertexPartition (gauged) wall
  · have hR : retSide source pairing hNoGlue hRamification profile b = false := by
      unfold retSide
      rw [ite_eq_left hLeft]
    rw [hR]
    exact hLeft
  · have hR : retSide source pairing hNoGlue hRamification profile b = true := by
      unfold retSide
      rw [ite_eq_right hLeft]
    rw [hR]
    rcases isStar_blockwiseResolution (data :=
      gaugedData source pairing hNoGlue hRamification) (star := star) pairing
      profile.pattern b with ⟨hl, _⟩ | ⟨hr, _⟩
    · exact absurd hl hLeft
    · exact hr

theorem retSide_other (b : Fin degree) :
    (if !retSide source pairing hNoGlue hRamification profile b then
        (blockRes b).right else (blockRes b).left) = (blockRes b).newEdge := by
  classical
  by_cases hLeft :
      (blockRes b).left = GluingDatum.vertexPartition (gauged) wall
  · have hR : retSide source pairing hNoGlue hRamification profile b = false := by
      unfold retSide
      rw [ite_eq_left hLeft]
    rw [hR]
    rcases isStar_blockwiseResolution (data :=
      gaugedData source pairing hNoGlue hRamification) (star := star) pairing
      profile.pattern b with ⟨_, hn⟩ | ⟨hr, hn⟩
    · exact hn.symm
    · rw [hn, hLeft]
      exact hr
  · have hR : retSide source pairing hNoGlue hRamification profile b = true := by
      unfold retSide
      rw [ite_eq_right hLeft]
    rw [hR]
    rcases isStar_blockwiseResolution (data :=
      gaugedData source pairing hNoGlue hRamification) (star := star) pairing
      profile.pattern b with ⟨hl, _⟩ | ⟨_, hn⟩
    · exact absurd hl hLeft
    · exact hn.symm


/-! ## The surviving star at a non-anchor block's two endpoint kinds -/

theorem endpointPartition_rel_of_incident (sideValue : Bool) {t : Fin degree}
    {e : (cand).datum.SourceEdge}
    (hIncident : Incident (cand).datum e
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid sideValue t)) :
    ((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).Rel t
      e.1.2 := by
  rw [incident_iff_target_mem_and_rel] at hIncident
  exact Eq.trans
    (((cand).datum.vertexPartition
      (if sideValue then freshVertex target else oldVertex target wall)).rel_repr_right t)
    hIncident.2

theorem datum_vertexPartition_eq (sideValue : Bool) :
    (cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall) =
      (if sideValue then
          (LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
            (cand).resolution (cand).contracts).right
        else (LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
          (cand).resolution (cand).contracts).left) := by
  cases sideValue
  · show (cand).datum.vertexPartition (oldVertex target wall) =
      (LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
        (cand).resolution (cand).contracts).left
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
  · show (cand).datum.vertexPartition (freshVertex target) =
      (LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
        (cand).resolution (cand).contracts).right
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]

theorem newEdge_rel_repr (sideValue : Bool) (s' : Fin degree) :
    ((cand).datum.vertexPartition
        (if sideValue then freshVertex target else oldVertex target wall)).Rel s'
      ((LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
        (cand).resolution (cand).contracts).newEdge.repr s') := by
  rw [datum_vertexPartition_eq source pairing hNoGlue hRamification profile
    hConnected hGenus hValid sideValue]
  cases sideValue
  · exact (LocalResolution.pasteNewEdge_refines_left
      (GluingDatum.vertexPartition (gauged) wall) (cand).resolution
      (cand).contracts).rel
      ((LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
        (cand).resolution (cand).contracts).newEdge.rel_repr_right s')
  · exact (LocalResolution.pasteNewEdge_refines_right
      (GluingDatum.vertexPartition (gauged) wall) (cand).resolution
      (cand).contracts).rel
      ((LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
        (cand).resolution (cand).contracts).newEdge.rel_repr_right s')


theorem fine_rel_of_incident {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    {e : (cand).datum.SourceEdge}
    (hIncident : Incident (cand).datum e
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) x)) :
    (blockRes
      ((GluingDatum.vertexPartition (gauged) wall).repr x)).newEdge.Rel x
      e.1.2 := by
  have h1 := endpointPartition_rel_of_incident source pairing hNoGlue
    hRamification profile hConnected hGenus hValid _ hIncident
  rw [candidate_endpoint_rel_block source pairing hNoGlue hRamification profile
    hConnected hGenus hValid _ hb, retSide_other] at h1
  exact h1

theorem ret_rel_of_incident {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    {e : (cand).datum.SourceEdge}
    (hIncident : Incident (cand).datum e
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) x)) :
    (GluingDatum.vertexPartition (gauged) wall).Rel x e.1.2 := by
  have h1 := endpointPartition_rel_of_incident source pairing hNoGlue
    hRamification profile hConnected hGenus hValid _ hIncident
  rw [candidate_endpoint_rel_block source pairing hNoGlue hRamification profile
    hConnected hGenus hValid _ hb, retSide_endpoint] at h1
  exact h1

/-- A new occurrence incident to the fine-side endpoint of a non-anchor block
is *the* new occurrence of that block's sheet. -/
theorem newSourceEdge_eq_of_incident_fine {x s' : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    (hIncident : Incident (cand).datum ((cand).newSourceEdge s')
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) x)) :
    (cand).newSourceEdge s' = (cand).newSourceEdge x := by
  have hX := endpointPartition_rel_of_incident source pairing hNoGlue
    hRamification profile hConnected hGenus hValid _ hIncident
  have hS := newEdge_rel_repr source pairing hNoGlue hRamification profile
    hConnected hGenus hValid
    (!retSide source pairing hNoGlue hRamification profile
      ((GluingDatum.vertexPartition (gauged) wall).repr x)) s'
  have hSX : ((cand).datum.vertexPartition
      (if !retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x) then
        freshVertex target else oldVertex target wall)).Rel s' x :=
    hS.trans hX.symm
  have hCoarse : (GluingDatum.vertexPartition (gauged) wall).Rel s' x :=
    (candidate_endpointPartition_refines source pairing hNoGlue hRamification
      profile hConnected hGenus hValid _).rel hSX
  have hbS : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 s' :=
    fun h ↦ hb (h.trans hCoarse)
  have hRepr : (GluingDatum.vertexPartition (gauged) wall).repr s' =
      (GluingDatum.vertexPartition (gauged) wall).repr x := hCoarse
  apply newSourceEdge_eq_of_rel source pairing hNoGlue hRamification profile
    hConnected hGenus hValid
  rw [candidate_newEdge_rel_block source pairing hNoGlue hRamification profile
    hConnected hGenus hValid hbS, hRepr]
  have := (candidate_endpoint_rel_block source pairing hNoGlue hRamification
    profile hConnected hGenus hValid
    (!retSide source pairing hNoGlue hRamification profile
      ((GluingDatum.vertexPartition (gauged) wall).repr x)) hbS x).mp hSX
  rw [hRepr, retSide_other] at this
  exact this


/-- **A new occurrence with no surviving old occurrence on its own fine class
is dangling.**  Its fine-side endpoint would otherwise have surviving valency
one.  This is the non-anchor form of
`NonTrivalentValencyFourDictionary.newSourceEdge_isDangling_of_singleton`. -/
theorem newSourceEdge_dangling_of_no_fine_survivor {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    (hNone : ∀ old : (gauged).SourceEdge, ¬ IsDangling (gauged) old →
      old.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing old.1.1 =
        !retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x) →
      ¬ (blockRes
        ((GluingDatum.vertexPartition (gauged) wall).repr x)).newEdge.Rel x
          old.1.2) :
    IsDangling (cand).datum ((cand).newSourceEdge x) := by
  classical
  have hSubset :
      nonDanglingIncident (cand).datum
          (endpointVertex source pairing hNoGlue hRamification profile
            hConnected hGenus hValid
            (!retSide source pairing hNoGlue hRamification profile
              ((GluingDatum.vertexPartition (gauged) wall).repr x)) x) ⊆
        {(cand).newSourceEdge x} := by
    intro f hf
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    rcases ResolutionPruning.sourceEdge_cases (cand) f with ⟨old, rfl⟩ | ⟨s', rfl⟩
    · exfalso
      obtain ⟨hAt, hSide⟩ := right_eq_of_incident_old source pairing hNoGlue
        hRamification profile hConnected hGenus hValid _ hIncident
      exact hNone old
        (fun h ↦ hSurvives
          ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
            (gaugedData_valid source pairing hNoGlue hRamification hValid)
            (candidate_sourceGenus source pairing hNoGlue hRamification profile
              hConnected hGenus hValid) old).mpr h))
        hAt hSide
        (fine_rel_of_incident source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hb hIncident)
    · rw [newSourceEdge_eq_of_incident_fine source pairing hNoGlue hRamification
        profile hConnected hGenus hValid hb hIncident]
      exact Finset.mem_singleton_self _
  by_contra hSurvives
  have hIncident := bridgeEdge_incident source pairing hNoGlue hRamification
    profile hConnected hGenus hValid
    (!retSide source pairing hNoGlue hRamification profile
      ((GluingDatum.vertexPartition (gauged) wall).repr x)) x
  have hCard := Finset.card_le_card hSubset
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    ((cand).datum_valid
      (gaugedData_valid source pairing hNoGlue hRamification hValid)).1
    (endpointVertex source pairing hNoGlue hRamification profile hConnected
      hGenus hValid
      (!retSide source pairing hNoGlue hRamification profile
        ((GluingDatum.vertexPartition (gauged) wall).repr x)) x)
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    (cand).datum hSurvives hIncident
  omega


theorem endpointVertex_fine_eq {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    {y : Fin degree}
    (hRel : (blockRes
      ((GluingDatum.vertexPartition (gauged) wall).repr x)).newEdge.Rel x y) :
    endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) y =
      endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) x := by
  have hPart := (candidate_endpoint_rel_block source pairing hNoGlue
    hRamification profile hConnected hGenus hValid
    (!retSide source pairing hNoGlue hRamification profile
      ((GluingDatum.vertexPartition (gauged) wall).repr x)) hb y).mpr
      (by rw [retSide_other]; exact hRel)
  refine (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨rfl, ?_⟩
  exact hPart.symm.trans
    (((cand).datum.vertexPartition
      (if !retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x) then
        freshVertex target else oldVertex target wall)).rel_repr_right x)

/-- **A new occurrence whose fine class carries exactly one surviving old
occurrence survives, and joins it.**  Together with
`newSourceEdge_dangling_of_no_fine_survivor` this is the whole local picture at
a non-anchor wall block. -/
theorem newSourceEdge_survives_of_unique_fine_survivor {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    {old : (gauged).SourceEdge} (hOldSurv : ¬ IsDangling (gauged) old)
    (hAt : old.1.1 ∈ GluingDatum.incidentEdges wall)
    (hSide : star.right pairing old.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((GluingDatum.vertexPartition (gauged) wall).repr x))
    (hRel : (blockRes
      ((GluingDatum.vertexPartition (gauged) wall).repr x)).newEdge.Rel x
        old.1.2)
    (hUnique : ∀ other : (gauged).SourceEdge, ¬ IsDangling (gauged) other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 =
        !retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x) →
      (blockRes
        ((GluingDatum.vertexPartition (gauged) wall).repr x)).newEdge.Rel x
          other.1.2 → other = old) :
    ¬ IsDangling (cand).datum ((cand).newSourceEdge x) ∧
      nonDanglingValency (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid
          (!retSide source pairing hNoGlue hRamification profile
            ((GluingDatum.vertexPartition (gauged) wall).repr x)) x) = 2 := by
  classical
  have hOldIncident : Incident (cand).datum ((cand).oldSourceEdge old)
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) x) := by
    have h := retainedEdge_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid old.1.1 hAt _ hSide old.1.2
    rw [GluingDatum.sourceEdge_self,
      endpointVertex_fine_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb hRel] at h
    exact h
  have hOldMem : (cand).oldSourceEdge old ∈
      nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid
          (!retSide source pairing hNoGlue hRamification profile
            ((GluingDatum.vertexPartition (gauged) wall).repr x)) x) :=
    (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _
        hOldSurv, hOldIncident⟩
  have hNeNewOld : (cand).newSourceEdge x ≠ (cand).oldSourceEdge old := by
    intro hEq
    have h := (occurrenceEquiv target wall (cand).right).injective
      (congrArg (fun e : (cand).datum.SourceEdge ↦ e.1.1) hEq)
    cases h
  have hSubset :
      nonDanglingIncident (cand).datum
          (endpointVertex source pairing hNoGlue hRamification profile
            hConnected hGenus hValid
            (!retSide source pairing hNoGlue hRamification profile
              ((GluingDatum.vertexPartition (gauged) wall).repr x)) x) ⊆
        {(cand).newSourceEdge x, (cand).oldSourceEdge old} := by
    intro f hf
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hf
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases ResolutionPruning.sourceEdge_cases (cand) f with ⟨other, rfl⟩ | ⟨s', rfl⟩
    · right
      obtain ⟨hAt', hSide'⟩ := right_eq_of_incident_old source pairing hNoGlue
        hRamification profile hConnected hGenus hValid _ hIncident
      exact congrArg (cand).oldSourceEdge (hUnique other
        (fun h ↦ hSurvives
          ((ResolutionPruning.isDangling_oldSourceEdge_iff (cand)
            (gaugedData_valid source pairing hNoGlue hRamification hValid)
            (candidate_sourceGenus source pairing hNoGlue hRamification profile
              hConnected hGenus hValid) other).mpr h))
        hAt' hSide'
        (fine_rel_of_incident source pairing hNoGlue hRamification profile
          hConnected hGenus hValid hb hIncident))
    · left
      exact newSourceEdge_eq_of_incident_fine source pairing hNoGlue
        hRamification profile hConnected hGenus hValid hb hIncident
  have hCardLe := Finset.card_le_card hSubset
  rw [card_nonDanglingIncident, Finset.card_insert_of_notMem (by
    simpa using hNeNewOld), Finset.card_singleton] at hCardLe
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    (cand).datum
    (ResolutionSurvival.not_isDangling_oldSourceEdge _
      (gaugedData_valid source pairing hNoGlue hRamification hValid).1 _
      hOldSurv) hOldIncident
  have hNe := NonDanglingValency.nonDanglingValency_ne_one (cand).datum
    ((cand).datum_valid
      (gaugedData_valid source pairing hNoGlue hRamification hValid)).1
    (endpointVertex source pairing hNoGlue hRamification profile hConnected
      hGenus hValid
      (!retSide source pairing hNoGlue hRamification profile
        ((GluingDatum.vertexPartition (gauged) wall).repr x)) x)
  have hCard : nonDanglingValency (cand).datum
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (!retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) x) = 2 := by
    omega
  refine ⟨?_, hCard⟩
  have hEqSet :
      nonDanglingIncident (cand).datum
          (endpointVertex source pairing hNoGlue hRamification profile
            hConnected hGenus hValid
            (!retSide source pairing hNoGlue hRamification profile
              ((GluingDatum.vertexPartition (gauged) wall).repr x)) x) =
        {(cand).newSourceEdge x, (cand).oldSourceEdge old} := by
    refine Finset.eq_of_subset_of_card_le hSubset ?_
    rw [card_nonDanglingIncident, hCard,
      Finset.card_insert_of_notMem (by simpa using hNeNewOld),
      Finset.card_singleton]
  have hMem : (cand).newSourceEdge x ∈
      nonDanglingIncident (cand).datum
        (endpointVertex source pairing hNoGlue hRamification profile hConnected
          hGenus hValid
          (!retSide source pairing hNoGlue hRamification profile
            ((GluingDatum.vertexPartition (gauged) wall).repr x)) x) := by
    rw [hEqSet]
    exact Finset.mem_insert_self _ _
  exact ((mem_nonDanglingIncident _ _ _).mp hMem).1


/-- The stable-row form of the previous theorem: the new occurrence of a
non-anchor block lies on the same stable row of the candidate as the unique
surviving old occurrence of its fine class. -/
theorem stablePath_newSourceEdge_eq {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    {old : (gauged).SourceEdge} (hOldSurv : ¬ IsDangling (gauged) old)
    (hAt : old.1.1 ∈ GluingDatum.incidentEdges wall)
    (hSide : star.right pairing old.1.1 =
      !retSide source pairing hNoGlue hRamification profile
        ((GluingDatum.vertexPartition (gauged) wall).repr x))
    (hRel : (blockRes
      ((GluingDatum.vertexPartition (gauged) wall).repr x)).newEdge.Rel x
        old.1.2)
    (hUnique : ∀ other : (gauged).SourceEdge, ¬ IsDangling (gauged) other →
      other.1.1 ∈ GluingDatum.incidentEdges wall →
      star.right pairing other.1.1 =
        !retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x) →
      (blockRes
        ((GluingDatum.vertexPartition (gauged) wall).repr x)).newEdge.Rel x
          other.1.2 → other = old) :
    NonDanglingEdge.stablePath
        (⟨(cand).newSourceEdge x,
          (newSourceEdge_survives_of_unique_fine_survivor source pairing hNoGlue
            hRamification profile hConnected hGenus hValid hb hOldSurv hAt hSide
            hRel hUnique).1⟩ : NonDanglingEdge (cand).datum) =
      (ResolutionAwayFromWall.retainedEdge (cand)
        (gaugedData_valid source pairing hNoGlue hRamification hValid).1
        ⟨old, hOldSurv⟩).stablePath := by
  obtain ⟨hNewSurv, hCard⟩ := newSourceEdge_survives_of_unique_fine_survivor
    source pairing hNoGlue hRamification profile hConnected hGenus hValid hb
    hOldSurv hAt hSide hRel hUnique
  apply stablePath_eq_of_consecutive
  refine ⟨?_, endpointVertex source pairing hNoGlue hRamification profile
    hConnected hGenus hValid
    (!retSide source pairing hNoGlue hRamification profile
      ((GluingDatum.vertexPartition (gauged) wall).repr x)) x, ?_, ?_, hCard⟩
  · intro hEq
    have h := (occurrenceEquiv target wall (cand).right).injective
      (congrArg (fun e : NonDanglingEdge (cand).datum ↦ e.1.1.1) hEq)
    cases h
  · exact bridgeEdge_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid _ x
  · have h := retainedEdge_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid old.1.1 hAt _ hSide old.1.2
    rw [GluingDatum.sourceEdge_self,
      endpointVertex_fine_eq source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb hRel] at h
    exact h


/-- The retaining-side endpoint census of a non-anchor block: a surviving
incidence there is either a new occurrence of the block, or a retained
surviving old occurrence of the block assigned to the retaining side. -/
theorem nonDanglingIncident_ret_cases {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    {f : (cand).datum.SourceEdge}
    (hSurv : ¬ IsDangling (cand).datum f)
    (hIncident : Incident (cand).datum f
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) x)) :
    (∃ s' : Fin degree,
        (GluingDatum.vertexPartition (gauged) wall).Rel x s' ∧
        f = (cand).newSourceEdge s') ∨
      (∃ old : (gauged).SourceEdge, ¬ IsDangling (gauged) old ∧
        old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing old.1.1 =
          retSide source pairing hNoGlue hRamification profile
            ((GluingDatum.vertexPartition (gauged) wall).repr x) ∧
        (GluingDatum.vertexPartition (gauged) wall).Rel x old.1.2 ∧
        f = (cand).oldSourceEdge old) := by
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
      ret_rel_of_incident source pairing hNoGlue hRamification profile
        hConnected hGenus hValid hb hIncident, rfl⟩
  · left
    refine ⟨s', ?_, rfl⟩
    have h1 := ret_rel_of_incident source pairing hNoGlue hRamification profile
      hConnected hGenus hValid hb hIncident
    have h2 := newEdge_rel_repr source pairing hNoGlue hRamification profile
      hConnected hGenus hValid
      (retSide source pairing hNoGlue hRamification profile
        ((GluingDatum.vertexPartition (gauged) wall).repr x)) s'
    have h3 : (GluingDatum.vertexPartition (gauged) wall).Rel s'
        ((LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
          (cand).resolution (cand).contracts).newEdge.repr s') :=
      (candidate_endpointPartition_refines source pairing hNoGlue hRamification
        profile hConnected hGenus hValid _).rel h2
    exact h1.trans h3.symm


/-- **The retaining-side dichotomy.**  A surviving occurrence at the retaining
endpoint of a non-anchor block is either a retained survivor of that block
assigned to the retaining side, or the new occurrence of a fine class that
carries a survivor assigned to the other side. -/
theorem nonDanglingIncident_ret_dichotomy {x : Fin degree}
    (hb : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 x)
    {f : (cand).datum.SourceEdge}
    (hSurv : ¬ IsDangling (cand).datum f)
    (hIncident : Incident (cand).datum f
      (endpointVertex source pairing hNoGlue hRamification profile hConnected
        hGenus hValid
        (retSide source pairing hNoGlue hRamification profile
          ((GluingDatum.vertexPartition (gauged) wall).repr x)) x)) :
    (∃ old : (gauged).SourceEdge, ¬ IsDangling (gauged) old ∧
        old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing old.1.1 =
          retSide source pairing hNoGlue hRamification profile
            ((GluingDatum.vertexPartition (gauged) wall).repr x) ∧
        (GluingDatum.vertexPartition (gauged) wall).Rel x old.1.2 ∧
        f = (cand).oldSourceEdge old) ∨
      (∃ old : (gauged).SourceEdge, ¬ IsDangling (gauged) old ∧
        old.1.1 ∈ GluingDatum.incidentEdges wall ∧
        star.right pairing old.1.1 =
          !retSide source pairing hNoGlue hRamification profile
            ((GluingDatum.vertexPartition (gauged) wall).repr x) ∧
        (GluingDatum.vertexPartition (gauged) wall).Rel x old.1.2 ∧
        f = (cand).newSourceEdge old.1.2) := by
  rcases nonDanglingIncident_ret_cases source pairing hNoGlue hRamification
    profile hConnected hGenus hValid hb hSurv hIncident with
    ⟨s', hRelS, rfl⟩ | hOld
  · right
    have hbS : ¬ (GluingDatum.vertexPartition (gauged) wall).Rel anchor.1 s' :=
      fun h ↦ hb (h.trans hRelS.symm)
    have hReprS : (GluingDatum.vertexPartition (gauged) wall).repr s' =
        (GluingDatum.vertexPartition (gauged) wall).repr x := hRelS.symm
    by_contra hNo
    push Not at hNo
    apply hSurv
    apply newSourceEdge_dangling_of_no_fine_survivor source pairing hNoGlue
      hRamification profile hConnected hGenus hValid hbS
    intro old hOldSurv hAt hSide hRelNew
    rw [hReprS] at hSide hRelNew
    have hCoarse : (GluingDatum.vertexPartition (gauged) wall).Rel x old.1.2 := by
      refine hRelS.trans ?_
      have hPaste : (LocalResolution.paste
          (GluingDatum.vertexPartition (gauged) wall) (cand).resolution
          (cand).contracts).newEdge.Rel s' old.1.2 := by
        rw [candidate_newEdge_rel_block source pairing hNoGlue hRamification
          profile hConnected hGenus hValid hbS, hReprS]
        exact hRelNew
      have hLeft :
          ((cand).datum.vertexPartition (oldVertex target wall)).Rel s'
            old.1.2 := by
        have hRefines :
            (LocalResolution.paste (GluingDatum.vertexPartition (gauged) wall)
                (cand).resolution (cand).contracts).newEdge.Refines
              ((cand).datum.vertexPartition (oldVertex target wall)) := by
          have hEq : (cand).datum.vertexPartition (oldVertex target wall) =
              (LocalResolution.paste
                (GluingDatum.vertexPartition (gauged) wall) (cand).resolution
                (cand).contracts).left := by
            simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
              GlobalResolution.datum_vertexPartition_old_wall]
          rw [hEq]
          exact LocalResolution.pasteNewEdge_refines_left
            (GluingDatum.vertexPartition (gauged) wall) (cand).resolution
            (cand).contracts
        exact hRefines.rel hPaste
      exact (candidate_endpointPartition_refines source pairing hNoGlue
        hRamification profile hConnected hGenus hValid false).rel hLeft
    exact hNo old hOldSurv hAt hSide hCoarse
      (newSourceEdge_eq_of_rel source pairing hNoGlue hRamification profile
        hConnected hGenus hValid
        (by
          rw [candidate_newEdge_rel_block source pairing hNoGlue hRamification
            profile hConnected hGenus hValid hbS, hReprS]
          exact hRelNew))
  · exact Or.inl hOld

end DraismaVargas.LocalCases.NonTrivalentValencyFourRowEquiv
