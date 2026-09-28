import DraismaVargasCount.GeneralKExitSetup

/-!
# A generic row dictionary for a wall resolution with star-shaped ordinary blocks

The datum-generic part of the general-`K` row dictionary at a four-valent wall.

Vargas, Part II (arXiv:2609.09109), the rigidity above `w_0` (`lemma-above-w0`) in the
combinatorial setup of the section on changing combinatorial type, and
`lm:change-comb-type`.

This file works over an **arbitrary** globally assembled candidate
`C : BalancedGlobal.Candidate target degree G wall` over a valid datum `G`,
with no reference to the `K = 0` gauge.  Part I's `K = 0` row dictionary
(`NonTrivalentValencyFourRowEquiv`, `…Descent`, `…RowDictionary`,
`…RowEquivFinal`, `…RetainedInjective`) is stated for the specific `K = 0`
candidate over the specific `K = 0` gauged datum, so none of it applies to the
general-`K` candidate `GeneralKExitSetup.candK`.  Its *arguments*, however, only
ever used two things about the non-anchor wall blocks:

* the candidate's resolution there is a *star*
  (`NonTrivalentValencyFourRows.IsStar`): one endpoint keeps the wall block and
  the new edge repeats the other endpoint;
* the datum `G` is target-direction injective there, with surviving valency at
  most three.

This section records the elementary incidence dictionary of any candidate at
the two new target vertices.

## What is NOT proved here

Nothing about a specific candidate.  The census of star blocks is in
`GeneralKRowStar` and the row dictionary itself in `GeneralKRowEquiv`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKRowCore

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4StableSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {G : GluingDatum target degree}

/-! ## 1.  The two new target vertices and their endpoint partitions -/

variable (C : BalancedGlobal.Candidate target degree G wall)

/-- The pasted local resolution of a candidate. -/
noncomputable abbrev pasted : LocalResolution degree :=
  LocalResolution.paste (G.vertexPartition wall) C.resolution C.contracts

/-- The endpoint partition on one side of the new target edge. -/
noncomputable def endPart (b : Bool) : SheetPartition degree :=
  if b then (pasted C).right else (pasted C).left

/-- The target vertex on one side of the new target edge: `false` is the
retained copy of the wall, `true` the fresh vertex. -/
abbrev endV (b : Bool) : (TargetExpansion.graph target wall C.right).V :=
  if b then freshVertex target else oldVertex target wall

/-- The source vertex over one side of the new target edge, through a sheet. -/
noncomputable def epv (b : Bool) (s : Fin degree) : C.datum.SourceVertex :=
  C.datum.sourceEndpoint (endV C b) s

theorem vertexPartition_endV (b : Bool) :
    C.datum.vertexPartition (endV C b) = endPart C b := by
  cases b
  · show C.datum.vertexPartition (oldVertex target wall) = (pasted C).left
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_old_wall]
  · show C.datum.vertexPartition (freshVertex target) = (pasted C).right
    simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
      GlobalResolution.datum_vertexPartition_fresh]

theorem endPart_rel_iff (b : Bool) (x y : Fin degree) :
    (endPart C b).Rel x y ↔
      (if b then (C.resolution ((G.vertexPartition wall).repr x)).right
        else (C.resolution ((G.vertexPartition wall).repr x)).left).Rel x y := by
  cases b
  · exact SheetPartition.paste_rel_iff (G.vertexPartition wall)
      (fun blk ↦ (C.resolution blk).left) (fun blk ↦ (C.contracts blk).left_refines) x y
  · exact SheetPartition.paste_rel_iff (G.vertexPartition wall)
      (fun blk ↦ (C.resolution blk).right) (fun blk ↦ (C.contracts blk).right_refines) x y

theorem newPart_rel_iff (x y : Fin degree) :
    (pasted C).newEdge.Rel x y ↔
      (C.resolution ((G.vertexPartition wall).repr x)).newEdge.Rel x y :=
  SheetPartition.paste_rel_iff (G.vertexPartition wall)
    (fun blk ↦ (C.resolution blk).newEdge)
    (fun blk ↦ (C.resolution blk).edge_refines_left.trans (C.contracts blk).left_refines) x y

theorem endPart_refines (b : Bool) : (endPart C b).Refines (G.vertexPartition wall) := by
  cases b
  · exact LocalResolution.pasteLeft_refines _ C.resolution C.contracts
  · exact LocalResolution.pasteRight_refines _ C.resolution C.contracts

theorem newPart_refines_endPart (b : Bool) : (pasted C).newEdge.Refines (endPart C b) := by
  cases b
  · exact LocalResolution.pasteNewEdge_refines_left _ C.resolution C.contracts
  · exact LocalResolution.pasteNewEdge_refines_right _ C.resolution C.contracts

theorem newPart_refines : (pasted C).newEdge.Refines (G.vertexPartition wall) :=
  (newPart_refines_endPart C false).trans (endPart_refines C false)

theorem epv_eq_iff (b : Bool) (s t : Fin degree) :
    epv C b s = epv C b t ↔ (endPart C b).Rel s t := by
  rw [← vertexPartition_endV C b]
  constructor
  · intro h
    exact congrArg (fun v : C.datum.SourceVertex ↦ v.1.2) h
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact h

theorem epv_ne_flip (b : Bool) (s t : Fin degree) : epv C b s ≠ epv C (!b) t := by
  intro h
  have h1 := congrArg (fun v : C.datum.SourceVertex ↦ v.1.1) h
  cases b <;> cases h1

/-! ## 2.  Incidence at the two new target vertices -/

theorem newSourceEdge_eq_iff (s t : Fin degree) :
    C.newSourceEdge s = C.newSourceEdge t ↔ (pasted C).newEdge.Rel s t := by
  constructor
  · intro h
    exact congrArg (fun e : C.datum.SourceEdge ↦ e.1.2) h
  · intro h
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact h

theorem new_ne_old (s : Fin degree) (o : G.SourceEdge) :
    C.newSourceEdge s ≠ C.oldSourceEdge o := by
  intro hEq
  have h := (occurrenceEquiv target wall C.right).injective
    (congrArg (fun e : C.datum.SourceEdge ↦ e.1.1) hEq)
  cases h

theorem sourceEnds_newSourceEdge (s : Fin degree) :
    C.datum.sourceEnds (C.newSourceEdge s) = (epv C false s, epv C true s) :=
  GlobalResolution.sourceEnds_newSourceEdge _ _ _ _ _ s

theorem newSourceEdge_incident (b : Bool) (s : Fin degree) :
    Incident C.datum (C.newSourceEdge s) (epv C b s) := by
  cases b
  · exact Or.inl (congrArg Prod.fst (sourceEnds_newSourceEdge C s))
  · exact Or.inr (congrArg Prod.snd (sourceEnds_newSourceEdge C s))

theorem newSourceEdge_incident_iff (b : Bool) (s t : Fin degree) :
    Incident C.datum (C.newSourceEdge s) (epv C b t) ↔ (endPart C b).Rel t s := by
  constructor
  · rintro (h | h)
    · rw [sourceEnds_newSourceEdge] at h
      cases b
      · exact ((epv_eq_iff C false s t).mp h).symm
      · exact absurd h (epv_ne_flip C false s t)
    · rw [sourceEnds_newSourceEdge] at h
      cases b
      · exact absurd h (epv_ne_flip C true s t)
      · exact ((epv_eq_iff C true s t).mp h).symm
  · intro h
    have hEq : epv C b s = epv C b t := (epv_eq_iff C b s t).mpr h.symm
    rw [← hEq]
    exact newSourceEdge_incident C b s

theorem mem_incidentEdges_endV_old (b : Bool) (edge : target.edges) :
    occurrenceEquiv target wall C.right (some edge) ∈
        GluingDatum.incidentEdges (endV C b) ↔
      (edge ∈ GluingDatum.incidentEdges wall ∧ C.right edge = b) := by
  rw [GluingContraction.mem_incidentEdges_iff, occurrenceEquiv_some,
    GluingContraction.mem_incidentEdges_iff]
  cases b
  · exact oldEnds_incident_oldVertex_iff target wall C.right edge
  · exact oldEnds_incident_freshVertex_iff target wall C.right edge

theorem oldSourceEdge_incident_iff (b : Bool) (o : G.SourceEdge) (t : Fin degree) :
    Incident C.datum (C.oldSourceEdge o) (epv C b t) ↔
      o.1.1 ∈ GluingDatum.incidentEdges wall ∧ C.right o.1.1 = b ∧
        (endPart C b).Rel t o.1.2 := by
  rw [incident_iff_target_mem_and_rel]
  have hV : (epv C b t).1.1 = endV C b := rfl
  rw [hV, BalancedGlobal.Candidate.oldSourceEdge_target, mem_incidentEdges_endV_old,
    BalancedGlobal.Candidate.oldSourceEdge_sheet, vertexPartition_endV]
  have hS : (epv C b t).1.2 = (endPart C b).repr t := by
    show (C.datum.vertexPartition (endV C b)).repr t = _
    rw [vertexPartition_endV]
  rw [hS, and_assoc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (SheetPartition.rel_repr_right _ t).trans h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, (SheetPartition.rel_repr_right _ t).symm.trans h3⟩

/-- Every source vertex over one of the two new target vertices is an endpoint
vertex through its own sheet. -/
theorem vertex_cases (v : C.datum.SourceVertex) :
    (∃ old : G.SourceVertex, old.1.1 ≠ wall ∧
        ResolutionAwayFromWall.retainedVertex C old = v) ∨
      ∃ b : Bool, epv C b v.1.2 = v := by
  cases hTarget : v.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst hAt
        right
        refine ⟨false, ?_⟩
        exact (C.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩
      · obtain ⟨old, hOldTarget, hOldVertex⟩ :=
          ResolutionAwayFromWall.exists_retainedVertex_of_target C v place hAt hTarget
        exact Or.inl ⟨old, fun hEq ↦ hAt (hOldTarget.symm.trans hEq), hOldVertex⟩
  | inr point =>
      cases point
      right
      refine ⟨true, ?_⟩
      exact (C.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨hTarget.symm, rfl⟩

/-! ## 3.  Counting at one vertex of any connected datum -/

section Counting

variable {tgt : CFGraph} {D : GluingDatum tgt degree}

theorem three_le_nd {v : D.SourceVertex} {a b c : D.SourceEdge}
    (ha : a ∈ nonDanglingIncident D v) (hb : b ∈ nonDanglingIncident D v)
    (hc : c ∈ nonDanglingIncident D v) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    3 ≤ nonDanglingValency D v := by
  classical
  rw [← card_nonDanglingIncident]
  have hSub : ({a, b, c} : Finset D.SourceEdge) ⊆ nonDanglingIncident D v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hCard : ({a, b, c} : Finset D.SourceEdge).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]),
      Finset.card_insert_of_notMem (by simp [hbc]), Finset.card_singleton]
  exact hCard ▸ Finset.card_le_card hSub

theorem four_le_nd {v : D.SourceVertex} {a b c d : D.SourceEdge}
    (ha : a ∈ nonDanglingIncident D v) (hb : b ∈ nonDanglingIncident D v)
    (hc : c ∈ nonDanglingIncident D v) (hd : d ∈ nonDanglingIncident D v)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    4 ≤ nonDanglingValency D v := by
  classical
  rw [← card_nonDanglingIncident]
  have hSub : ({a, b, c, d} : Finset D.SourceEdge) ⊆ nonDanglingIncident D v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hCard : ({a, b, c, d} : Finset D.SourceEdge).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  exact hCard ▸ Finset.card_le_card hSub

/-- An occurrence alone in the surviving star of a vertex it meets is dangling:
otherwise that vertex would have surviving valency one. -/
theorem isDangling_of_subset_singleton (hConn : D.Connected) {v : D.SourceVertex}
    {a : D.SourceEdge} (hSub : nonDanglingIncident D v ⊆ {a}) (hInc : Incident D a v) :
    IsDangling D a := by
  classical
  by_contra hSurv
  have hCard := Finset.card_le_card hSub
  rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
  have hNe := NonDanglingValency.nonDanglingValency_ne_one D hConn v
  have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident D hSurv hInc
  omega

/-- If the surviving star of a vertex lies in `{a, b}`, `b` survives and both
meet the vertex, then `a` survives too and the vertex is divalent. -/
theorem survives_of_subset_pair (hConn : D.Connected) {v : D.SourceVertex}
    {a b : D.SourceEdge} (hab : a ≠ b) (hSub : nonDanglingIncident D v ⊆ {a, b})
    (hIncA : Incident D a v) (hSurvB : ¬ IsDangling D b) (hIncB : Incident D b v) :
    ¬ IsDangling D a ∧ nonDanglingValency D v = 2 := by
  classical
  have hNe := NonDanglingValency.nonDanglingValency_ne_one D hConn v
  have hbMem : b ∈ nonDanglingIncident D v := (mem_nonDanglingIncident _ _ _).mpr ⟨hSurvB, hIncB⟩
  have hSurvA : ¬ IsDangling D a := by
    intro hDang
    have hSub' : nonDanglingIncident D v ⊆ {b} := by
      intro z hz
      have hz' := hSub hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
      rcases hz' with rfl | rfl
      · exact absurd ((mem_nonDanglingIncident _ _ _).mp hz).1 (not_not.mpr hDang)
      · exact Finset.mem_singleton_self _
    have hCard := Finset.card_le_card hSub'
    rw [card_nonDanglingIncident, Finset.card_singleton] at hCard
    have hPos := ClassInjectivity.nonDanglingValency_ne_zero_of_incident D hSurvB hIncB
    omega
  refine ⟨hSurvA, ?_⟩
  have haMem : a ∈ nonDanglingIncident D v := (mem_nonDanglingIncident _ _ _).mpr ⟨hSurvA, hIncA⟩
  have hEq : nonDanglingIncident D v = {a, b} := by
    refine Finset.Subset.antisymm hSub ?_
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact haMem
    · exact hbMem
  rw [← card_nonDanglingIncident, hEq, Finset.card_insert_of_notMem (by simpa using hab),
    Finset.card_singleton]

/-- Two distinct survivors meeting at a vertex whose surviving star lies in
their pair are consecutive. -/
theorem consecutive_of_subset_pair (hConn : D.Connected) {v : D.SourceVertex}
    (a b : NonDanglingEdge D) (hab : a ≠ b)
    (hSub : nonDanglingIncident D v ⊆ {a.1, b.1})
    (hIncA : Incident D a.1 v) (hIncB : Incident D b.1 v) : Consecutive D a b :=
  ⟨hab, v, hIncA, hIncB,
    (survives_of_subset_pair hConn (fun h ↦ hab (Subtype.ext h)) hSub hIncA b.2 hIncB).2⟩

end Counting

/-! ## 4.  The surviving star at an endpoint vertex -/

section Star

variable (hValid : G.Valid) (hGenus : genus C.datum.sourceGraph = genus G.sourceGraph)

include hValid hGenus in
/-- Old occurrences keep their pruning status in a genus-preserving candidate. -/
theorem isDangling_old_iff (o : G.SourceEdge) :
    IsDangling C.datum (C.oldSourceEdge o) ↔ IsDangling G o :=
  ResolutionPruning.isDangling_oldSourceEdge_iff C hValid hGenus o

include hValid hGenus in
/-- **The surviving star at an endpoint vertex**: retained survivors on that
side whose sheet the endpoint partition relates, and surviving new
occurrences whose sheet it relates. -/
theorem mem_ndI_epv (b : Bool) (x : Fin degree) (f : C.datum.SourceEdge) :
    f ∈ nonDanglingIncident C.datum (epv C b x) ↔
      (∃ o : G.SourceEdge, ¬ IsDangling G o ∧ o.1.1 ∈ GluingDatum.incidentEdges wall ∧
        C.right o.1.1 = b ∧ (endPart C b).Rel x o.1.2 ∧ f = C.oldSourceEdge o) ∨
      (∃ t : Fin degree, (endPart C b).Rel x t ∧ ¬ IsDangling C.datum (C.newSourceEdge t) ∧
        f = C.newSourceEdge t) := by
  rw [mem_nonDanglingIncident]
  constructor
  · rintro ⟨hSurv, hInc⟩
    rcases ResolutionPruning.sourceEdge_cases C f with ⟨o, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := (oldSourceEdge_incident_iff C b o x).mp hInc
      exact Or.inl ⟨o, fun h ↦ hSurv ((isDangling_old_iff C hValid hGenus o).mpr h), h1, h2,
        h3, rfl⟩
    · exact Or.inr ⟨t, (newSourceEdge_incident_iff C b t x).mp hInc, hSurv, rfl⟩
  · rintro (⟨o, hS, h1, h2, h3, rfl⟩ | ⟨t, h, hS, rfl⟩)
    · exact ⟨fun h ↦ hS ((isDangling_old_iff C hValid hGenus o).mp h),
        (oldSourceEdge_incident_iff C b o x).mpr ⟨h1, h2, h3⟩⟩
    · exact ⟨hS, (newSourceEdge_incident_iff C b t x).mpr h⟩

end Star

end DraismaVargas.Count.GeneralKRowCore
