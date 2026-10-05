module

public import DraismaVargas.LocalCases.ResolutionStableIncidence
public import DraismaVargas.LocalCases.StableSourceMatrix
public import DraismaVargas.LocalCases.M11SplitSurvival

@[expose] public section

/-!
# The generic limit-matrix chain

The five stages of every outgoing-member chain of the local cases —
survival readers, stable lift, row descent, limit matrices, stable incidence
graph — stated **once**, for an arbitrary `BalancedGlobal.Candidate` that
retains exactly one wall direction at the old endpoint and installs that
direction's own star away from one distinguished wall block.  Nothing here
names a case, a figure, a member constructor or a star size.

Apart from the structures, the two-star/`n`-star unification in §2 and the
`Finset` regrown route in §5, the proofs below are the arguments of the
individual case chains (the four-candidate chain of Case {w3} and the chain of
Case {w2-r2-nd3-M-kk}, among others) with the case object replaced by one
field.

## The parameters, in order of appearance

* §0 — occurrence identities for an arbitrary candidate, stated here so that
  no chain module sits below this one.
* §1 — reading a surviving star off a complete incidence list: the four
  endpoint shapes `(card, surviving) ∈ {(2,2), (2,0), (3,2), (3,3)}` above
  the distinguished block.
* §2 — `WallCandidate`: a candidate together with the one wall direction it
  keeps at the retained endpoint.  The endpoint dictionary is stated for that
  direction and, at the fresh endpoint, for `wallEdgesAssigned … true`, so
  one block serves two-, three- and four-star walls; the two-star forms are
  corollaries.
* §3 — `BackgroundShape`: a `WallCandidate` with a distinguished-block anchor
  and, off that block, the retained direction's own star.  The star is
  recorded **blockwise** (`left_block`, `right_block`, `newEdge_block`), not
  as an equality of local resolutions: the members of Case
  {w2-r2-nd3-M-11} install
  `ResolutionM11.joinedResolutionAt` off `A₀`, which agrees with the
  direction's fine star block by block (local ramification zero) but not as a
  `LocalResolution`.  `Background.replace` is the bijection of surviving stars
  at every background wall vertex, at arbitrary old valency.
* §4 — `LiftData` (stage 2), `SelectedData` (stages 3, 4) and `GraphData`
  (stage 5): the member's selected-star census, in the three sizes the stages
  need.  A chain that stops at the limit matrices instantiates
  `SelectedData`; one that reaches the stable incidence graph instantiates
  `GraphData`.  `selectedSide : Bool` records which expanded endpoint above
  the distinguished block is the member's branch vertex; both values occur.
* §5 — the regrown column: `Gauge`, `RegrownAt`, `occurrences_new_eq`
  (`Finset`, no distinctness), `matrix_new` (list, `Nodup` **after**
  `newSourceEdge`), and the `Finset` split `matrix_new_split` into a
  selected half and `backgroundColumn`.

## Discipline

Every endpoint statement is an identity of **occurrence** sets, never of
stable-row labels; nothing asks the rows of the selected survivors to be
distinct.  No hypothesis beyond the structure fields and `data.Valid` is
added to any statement.
-/

namespace DraismaVargas.LocalCases.LimitChainCore

open DraismaVargas.Infrastructure
open TargetExpansion
open BalancedGlobal
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open ResolutionCoarseFine ResolutionM11
open ResolutionAwayFromWall StableSourceMatrix StablePathCount

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) : DecidableEq (IncidentSourceEdge datum vertex) :=
  Classical.decEq _

/-! ## §0  Occurrence identities for an arbitrary candidate -/

theorem sourceEdge_eq_iff_rel (data : GluingDatum target degree)
    (edge : target.edges) (first second : Fin degree) :
    data.sourceEdge edge first = data.sourceEdge edge second ↔
      (data.edgePartition edge).Rel first second := by
  constructor
  · intro hEqual
    exact congrArg (fun item : data.SourceEdge ↦ item.1.2) hEqual
  · intro hRel
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact hRel

/-- A sheet names the wall block of its own quotient-source vertex. -/
theorem sourceVertex_ofSheet (data : GluingDatum target degree) (wall : target.V)
    (sheet : Fin degree) :
    WallBlock.sourceVertex data wall (WallBlock.ofSheet data wall sheet) =
      data.sourceEndpoint wall sheet := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (data.vertexPartition wall).repr_idem sheet

/-- An occurrence incident to a wall source vertex has its sheet in that
vertex's wall block. -/
theorem wall_rel_of_incident (data : GluingDatum target degree) (wall : target.V)
    (sheet : Fin degree) (edge : data.SourceEdge)
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    (data.vertexPartition wall).Rel sheet edge.1.2 := by
  have hRel := ((incident_iff_target_mem_and_rel data edge _).mp hIncident).2
  change (data.vertexPartition wall).Rel
    ((data.vertexPartition wall).repr sheet) edge.1.2 at hRel
  exact ((data.vertexPartition wall).rel_repr_right sheet).trans hRel


/-- Sheets of one wall block name one quotient-source vertex. -/
theorem sourceEndpoint_eq_of_rel (data : GluingDatum target degree)
    (wall : target.V) {first second : Fin degree}
    (hRel : (data.vertexPartition wall).Rel first second) :
    data.sourceEndpoint wall first = data.sourceEndpoint wall second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact hRel


/-- The pasted local resolution of a candidate: its two endpoint partitions
and its new-edge partition. -/
noncomputable abbrev pasted (candidate : BalancedGlobal.Candidate target degree data wall) :
    LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall) candidate.resolution
    candidate.contracts


/-- An old occurrence incident at a selected fresh endpoint was already
incident to the distinguished source vertex.  The conclusion retains the
literal side assignment, which excludes the wrong member of the profile's
two-survivor pair. -/
theorem old_incident_fresh_selected_info
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (block : WallBlock data wall) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor)
    (old : data.SourceEdge)
    (hIncident : Incident candidate.datum (candidate.oldSourceEdge old)
      (candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    Incident data old (WallBlock.sourceVertex data wall block) ∧
      candidate.right old.1.1 = true := by
  let pasted := LocalResolution.paste (data.vertexPartition wall)
    candidate.resolution candidate.contracts
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.oldSourceEdge old)
    (candidate.datum.sourceEndpoint (freshVertex target) anchor)).mp hIncident
  change occurrenceEquiv target wall candidate.right (some old.1.1) ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    pasted.right.Rel (pasted.right.repr anchor) old.1.2 at hOutgoing
  have hTarget : occurrenceEquiv target wall candidate.right (some old.1.1) ∈
      GluingDatum.incidentEdges (freshVertex target) := hOutgoing.1
  have hTargetRaw := hTarget
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, occurrenceEquiv_some] at hTargetRaw
  have hSide := (oldEnds_incident_freshVertex_iff target wall candidate.right
    old.1.1).mp hTargetRaw
  have hRel : pasted.right.Rel (pasted.right.repr anchor) old.1.2 := hOutgoing.2
  have hRightRefines : pasted.right.Refines (data.vertexPartition wall) :=
    SheetPartition.IsJoin.right_refines (LocalResolution.paste_contracts
      (data.vertexPartition wall) candidate.resolution candidate.contracts)
  have hWallRepr : (data.vertexPartition wall).Rel
      (pasted.right.repr anchor) anchor :=
    hRightRefines.rel (pasted.right.rel_repr_left anchor)
  have hWallOld : (data.vertexPartition wall).Rel block.1 old.1.2 :=
    hAnchor.trans (hWallRepr.symm.trans (hRightRefines.rel hRel))
  refine ⟨?_, hSide.2⟩
  apply (incident_wallBlock_sourceVertex_iff data block old).mpr
  refine ⟨?_, Subtype.ext ?_⟩
  · simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hSide.1
  · exact hWallOld.symm.trans block.2

/-! ### The divalent-endpoint counterpart of `old_incident_fresh_selected_info`

`old_incident_fresh_selected_info` classifies an old occurrence incident to a
**fresh** selected endpoint.  The same statement at the retained **old**
endpoint is where a branch vertex on the retained side sits; the proof is the
mirror image. -/

theorem old_incident_old_selected_info
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (block : WallBlock data wall) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor)
    (old : data.SourceEdge)
    (hIncident : Incident candidate.datum (candidate.oldSourceEdge old)
      (candidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    Incident data old (WallBlock.sourceVertex data wall block) ∧
      candidate.right old.1.1 = false := by
  let pasted := LocalResolution.paste (data.vertexPartition wall)
    candidate.resolution candidate.contracts
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
    pasted.left.Rel (pasted.left.repr anchor) old.1.2 at hOutgoing
  have hTargetRaw := hOutgoing.1
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
    true_and, occurrenceEquiv_some] at hTargetRaw
  have hSide := (oldEnds_incident_oldVertex_iff target wall candidate.right
    old.1.1).mp hTargetRaw
  have hLeftRefines : pasted.left.Refines (data.vertexPartition wall) :=
    SheetPartition.IsJoin.left_refines (LocalResolution.paste_contracts
      (data.vertexPartition wall) candidate.resolution candidate.contracts)
  have hWallRepr : (data.vertexPartition wall).Rel
      (pasted.left.repr anchor) anchor :=
    hLeftRefines.rel (pasted.left.rel_repr_left anchor)
  have hWallOld : (data.vertexPartition wall).Rel block.1 old.1.2 :=
    hAnchor.trans (hWallRepr.symm.trans (hLeftRefines.rel hOutgoing.2))
  refine ⟨?_, hSide.2⟩
  apply (incident_wallBlock_sourceVertex_iff data block old).mpr
  refine ⟨?_, Subtype.ext ?_⟩
  · simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] using hSide.1
  · exact hWallOld.symm.trans block.2

/-! ### Reading a sheet relation off an incidence -/

theorem old_incident_fresh_sheet_rel
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (anchor : Fin degree) (old : data.SourceEdge)
    (hIncident : Incident candidate.datum (candidate.oldSourceEdge old)
      (candidate.datum.sourceEndpoint (freshVertex target) anchor)) :
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
        candidate.contracts).right.Rel anchor old.1.2 := by
  let pasted := LocalResolution.paste (data.vertexPartition wall)
    candidate.resolution candidate.contracts
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.oldSourceEdge old)
    (candidate.datum.sourceEndpoint (freshVertex target) anchor)).mp hIncident
  change occurrenceEquiv target wall candidate.right (some old.1.1) ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    pasted.right.Rel (pasted.right.repr anchor) old.1.2 at hOutgoing
  exact (pasted.right.rel_repr_right anchor).trans hOutgoing.2

theorem new_incident_old_sheet_rel
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (anchor sheet : Fin degree)
    (hIncident : Incident candidate.datum (candidate.newSourceEdge sheet)
      (candidate.datum.sourceEndpoint (oldVertex target wall) anchor)) :
    (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
        candidate.contracts).left.Rel anchor
      ((LocalResolution.paste (data.vertexPartition wall) candidate.resolution
        candidate.contracts).newEdge.repr sheet) := by
  let pasted := LocalResolution.paste (data.vertexPartition wall)
    candidate.resolution candidate.contracts
  have hOutgoing := (incident_iff_target_mem_and_rel candidate.datum
    (candidate.newSourceEdge sheet)
    (candidate.datum.sourceEndpoint (oldVertex target wall) anchor)).mp hIncident
  simp only [BalancedGlobal.Candidate.datum, GlobalAssembly.datum,
    GluingDatum.sourceEndpoint,
    GlobalResolution.datum_vertexPartition_old_wall] at hOutgoing
  change occurrenceEquiv target wall candidate.right none ∈
      GluingDatum.incidentEdges (oldVertex target wall) ∧
    pasted.left.Rel (pasted.left.repr anchor)
      (pasted.newEdge.repr sheet) at hOutgoing
  exact (pasted.left.rel_repr_right anchor).trans hOutgoing.2

theorem newSourceEdge_repr
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (sheet : Fin degree) :
    candidate.newSourceEdge ((LocalResolution.paste (data.vertexPartition wall)
        candidate.resolution candidate.contracts).newEdge.repr sheet) =
      candidate.newSourceEdge sheet := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (LocalResolution.paste (data.vertexPartition wall) candidate.resolution
      candidate.contracts).newEdge.repr_idem sheet

/-- The divalent-endpoint counterpart of `old_incident_fresh_sheet_rel`: an old
occurrence incident to a retained endpoint has its sheet in that endpoint's
class. -/
theorem old_incident_old_sheet_rel
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

/-- A retained old target occurrence assigned to the retained side carries its
same-sheet source occurrence to the literal old source endpoint. -/
theorem oldSourceEdge_incident_old
    (candidate : BalancedGlobal.Candidate target degree data wall)
    (edge : target.edges) (hAt : edge ∈ GluingDatum.incidentEdges wall)
    (hRight : candidate.right edge = false) (sheet : Fin degree) :
    Incident candidate.datum (candidate.oldSourceEdge (data.sourceEdge edge sheet))
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet) := by
  have hAtUp : occurrenceEquiv target wall candidate.right (some edge) ∈
      GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (oldVertex target wall) := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
      true_and] at hAt ⊢
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_oldVertex_iff target wall candidate.right edge).mpr
      ⟨hAt, hRight⟩
  have hIncident := incident_sourceEdge_sourceEndpoint candidate.datum
    (oldVertex target wall)
    (occurrenceEquiv target wall candidate.right (some edge)) hAtUp sheet
  have hEq : candidate.datum.sourceEdge
      (occurrenceEquiv target wall candidate.right (some edge)) sheet =
      candidate.oldSourceEdge (data.sourceEdge edge sheet) :=
    ResolutionSideCounts.sourceEdge_old data wall candidate.right
      (LocalResolution.paste _ candidate.resolution candidate.contracts)
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) edge sheet
  exact hEq ▸ hIncident

/-- At a connected source vertex with exactly two incidences, either both
occurrences survive pruning or both dangle. -/
theorem survives_iff_of_card_two (datum : GluingDatum target degree)
    (hConnected : datum.Connected) (vertex : datum.SourceVertex)
    (first second : datum.SourceEdge)
    (hFirstIncident : Incident datum first vertex)
    (hSecondIncident : Incident datum second vertex)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 2) :
    (¬ IsDangling datum first) ↔ ¬ IsDangling datum second := by
  classical
  have force_other : ∀ survivor other : datum.SourceEdge,
      Incident datum survivor vertex → Incident datum other vertex →
      ¬ IsDangling datum survivor → ¬ IsDangling datum other := by
    intro survivor other hSurvivorIncident hOtherIncident hSurvivor hOther
    have hDanglingPositive : 0 <
        ((Finset.univ : Finset (IncidentSourceEdge datum vertex)).filter
          (fun edge ↦ IsDangling datum edge.1)).card :=
      Finset.card_pos.mpr ⟨⟨other, hOtherIncident⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hOther⟩⟩
    have hSurvivingPositive :=
      ClassInjectivity.nonDanglingValency_ne_zero_of_incident datum
        hSurvivor hSurvivorIncident
    have hNotOne := NonDanglingValency.nonDanglingValency_ne_one datum
      hConnected vertex
    have hTotal := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (IncidentSourceEdge datum vertex)))
      (p := fun edge ↦ IsDangling datum edge.1)
    rw [card_filter_not_isDangling_eq_nonDanglingValency, Finset.card_univ,
      hCard] at hTotal
    omega
  exact ⟨force_other first second hFirstIncident hSecondIncident,
    force_other second first hSecondIncident hFirstIncident⟩

/-- A divalent source vertex carrying one survivor has surviving valency two. -/
theorem nonDanglingValency_eq_two_of_card_two_of_survives
    (datum : GluingDatum target degree) (hConnected : datum.Connected)
    (vertex : datum.SourceVertex) (edge : datum.SourceEdge)
    (hIncident : Incident datum edge vertex) (hSurvives : ¬ IsDangling datum edge)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 2) :
    nonDanglingValency datum vertex = 2 := by
  classical
  have hPositive := ClassInjectivity.nonDanglingValency_ne_zero_of_incident
    datum hSurvives hIncident
  have hNotOne := NonDanglingValency.nonDanglingValency_ne_one datum hConnected vertex
  have hLe : nonDanglingValency datum vertex ≤
      Fintype.card (IncidentSourceEdge datum vertex) := by
    rw [← card_filter_not_isDangling_eq_nonDanglingValency, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  omega


/-! ## §1  Reading a surviving star off a complete incidence list

The four endpoint shapes that occur above the distinguished block:
`(card, surviving) ∈ {(2,2), (2,0), (3,2), (3,3)}`.  Stated for a bare datum
and vertex; no wall, star or candidate enters. -/


/-- Two distinct incidences exhaust a divalent source vertex. -/
theorem forall_eq_of_card_two (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) (a b : IncidentSourceEdge datum vertex) (hab : a ≠ b)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 2)
    (c : IncidentSourceEdge datum vertex) : c = a ∨ c = b := by
  let _ : DecidableEq (IncidentSourceEdge datum vertex) := Classical.decEq _
  have hUniv : ({a, b} : Finset (IncidentSourceEdge datum vertex)) = Finset.univ :=
    Finset.eq_univ_of_card _ ((Finset.card_pair hab).trans hCard.symm)
  have hc : c ∈ ({a, b} : Finset (IncidentSourceEdge datum vertex)) :=
    hUniv ▸ Finset.mem_univ c
  simpa using hc

/-- Three distinct incidences exhaust a trivalent source vertex. -/
theorem forall_eq_of_card_three (datum : GluingDatum target degree)
    (vertex : datum.SourceVertex) (a b c : IncidentSourceEdge datum vertex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 3)
    (d : IncidentSourceEdge datum vertex) : d = a ∨ d = b ∨ d = c := by
  let _ : DecidableEq (IncidentSourceEdge datum vertex) := Classical.decEq _
  have hNotMem : a ∉ ({b, c} : Finset (IncidentSourceEdge datum vertex)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hab rfl
    · exact hac rfl
  have hUniv : ({a, b, c} : Finset (IncidentSourceEdge datum vertex)) = Finset.univ :=
    Finset.eq_univ_of_card _
      (((Finset.card_insert_of_notMem hNotMem).trans
        (congrArg (· + 1) (Finset.card_pair hbc))).trans hCard.symm)
  have hd : d ∈ ({a, b, c} : Finset (IncidentSourceEdge datum vertex)) :=
    hUniv ▸ Finset.mem_univ d
  simpa using hd

/-! ### Reading a surviving star off a complete incidence list -/

/-- At a divalent vertex with two named surviving incidences, the surviving
star is exactly that pair. -/
theorem nonDanglingIncident_pair_of_card_two (datum : GluingDatum target degree)
    {vertex : datum.SourceVertex} {first second : datum.SourceEdge}
    (hFirst : Incident datum first vertex) (hSecond : Incident datum second vertex)
    (hNe : first ≠ second) (hFirstSurvives : ¬ IsDangling datum first)
    (hSecondSurvives : ¬ IsDangling datum second)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 2) :
    nonDanglingIncident datum vertex = {first, second} := by
  classical
  ext edge
  simp only [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hIncident⟩
    rcases forall_eq_of_card_two datum vertex ⟨first, hFirst⟩ ⟨second, hSecond⟩
      (fun h ↦ hNe (congrArg Subtype.val h)) hCard ⟨edge, hIncident⟩ with hEq | hEq
    · exact Or.inl (congrArg Subtype.val hEq)
    · exact Or.inr (congrArg Subtype.val hEq)
  · rintro (rfl | rfl)
    · exact ⟨hFirstSurvives, hFirst⟩
    · exact ⟨hSecondSurvives, hSecond⟩

/-- At a divalent vertex both of whose incidences dangle, nothing survives. -/
theorem nonDanglingIncident_empty_of_card_two (datum : GluingDatum target degree)
    {vertex : datum.SourceVertex} {first second : datum.SourceEdge}
    (hFirst : Incident datum first vertex) (hSecond : Incident datum second vertex)
    (hNe : first ≠ second) (hFirstDangles : IsDangling datum first)
    (hSecondDangles : IsDangling datum second)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 2) :
    nonDanglingIncident datum vertex = ∅ := by
  classical
  ext edge
  simp only [mem_nonDanglingIncident, Finset.notMem_empty, iff_false, not_and]
  intro hSurvives hIncident
  rcases forall_eq_of_card_two datum vertex ⟨first, hFirst⟩ ⟨second, hSecond⟩
    (fun h ↦ hNe (congrArg Subtype.val h)) hCard ⟨edge, hIncident⟩ with hEq | hEq
  · have hVal : edge = first := congrArg Subtype.val hEq
    rw [hVal] at hSurvives
    exact hSurvives hFirstDangles
  · have hVal : edge = second := congrArg Subtype.val hEq
    rw [hVal] at hSurvives
    exact hSurvives hSecondDangles

/-- At a trivalent vertex with one dangling incidence, the surviving star is
the other two. -/
theorem nonDanglingIncident_pair_of_card_three (datum : GluingDatum target degree)
    {vertex : datum.SourceVertex} {first second deleted : datum.SourceEdge}
    (hFirst : Incident datum first vertex) (hSecond : Incident datum second vertex)
    (hDeleted : Incident datum deleted vertex)
    (hFirstNe : first ≠ second) (hFirstNeDeleted : first ≠ deleted)
    (hSecondNeDeleted : second ≠ deleted)
    (hFirstSurvives : ¬ IsDangling datum first)
    (hSecondSurvives : ¬ IsDangling datum second)
    (hDeletedDangles : IsDangling datum deleted)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 3) :
    nonDanglingIncident datum vertex = {first, second} := by
  classical
  ext edge
  simp only [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hSurvives, hIncident⟩
    rcases forall_eq_of_card_three datum vertex ⟨first, hFirst⟩ ⟨second, hSecond⟩
      ⟨deleted, hDeleted⟩
      (fun h ↦ hFirstNe (congrArg Subtype.val h))
      (fun h ↦ hFirstNeDeleted (congrArg Subtype.val h))
      (fun h ↦ hSecondNeDeleted (congrArg Subtype.val h)) hCard
      ⟨edge, hIncident⟩ with hEq | hEq | hEq
    · exact Or.inl (congrArg Subtype.val hEq)
    · exact Or.inr (congrArg Subtype.val hEq)
    · have hVal : edge = deleted := congrArg Subtype.val hEq
      rw [hVal] at hSurvives
      exact absurd hDeletedDangles hSurvives
  · rintro (rfl | rfl)
    · exact ⟨hFirstSurvives, hFirst⟩
    · exact ⟨hSecondSurvives, hSecond⟩

/-- At a trivalent vertex all of whose incidences survive, the surviving star
is all three: a branch vertex. -/
theorem nonDanglingIncident_triple_of_card_three (datum : GluingDatum target degree)
    {vertex : datum.SourceVertex} {first second third : datum.SourceEdge}
    (hFirst : Incident datum first vertex) (hSecond : Incident datum second vertex)
    (hThird : Incident datum third vertex)
    (hFirstNe : first ≠ second) (hFirstNeThird : first ≠ third)
    (hSecondNeThird : second ≠ third)
    (hFirstSurvives : ¬ IsDangling datum first)
    (hSecondSurvives : ¬ IsDangling datum second)
    (hThirdSurvives : ¬ IsDangling datum third)
    (hCard : Fintype.card (IncidentSourceEdge datum vertex) = 3) :
    nonDanglingIncident datum vertex = {first, second, third} := by
  classical
  ext edge
  simp only [mem_nonDanglingIncident, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hIncident⟩
    rcases forall_eq_of_card_three datum vertex ⟨first, hFirst⟩ ⟨second, hSecond⟩
      ⟨third, hThird⟩
      (fun h ↦ hFirstNe (congrArg Subtype.val h))
      (fun h ↦ hFirstNeThird (congrArg Subtype.val h))
      (fun h ↦ hSecondNeThird (congrArg Subtype.val h)) hCard
      ⟨edge, hIncident⟩ with hEq | hEq | hEq
    · exact Or.inl (congrArg Subtype.val hEq)
    · exact Or.inr (Or.inl (congrArg Subtype.val hEq))
    · exact Or.inr (Or.inr (congrArg Subtype.val hEq))
  · rintro (rfl | rfl | rfl)
    · exact ⟨hFirstSurvives, hFirst⟩
    · exact ⟨hSecondSurvives, hSecond⟩
    · exact ⟨hThirdSurvives, hThird⟩


/-! ## §2  A candidate retaining one wall direction

Every member of the local cases keeps exactly one wall direction at the retained
endpoint — `W3Nd2SourceCandidates.rightOf` in the three- and four-star cases,
`TwoStar.right` in the two-star ones — and sends every other wall direction to
the fresh endpoint.  `WallCandidate` names that direction.  The two `right`
conventions disagree **off** the wall (`rightOf` is `true` there,
`TwoStar.right` is `false`), so `unique` is stated for wall-incident edges
only; nothing below needs more. -/

/-- A candidate together with the one wall direction it retains. -/
structure WallCandidate (data : GluingDatum target degree) (wall : target.V) where
  /-- The candidate. -/
  candidate : BalancedGlobal.Candidate target degree data wall
  /-- The retained direction. -/
  retainedTarget : target.edges
  target_mem : retainedTarget ∈ GluingDatum.incidentEdges wall
  /-- It sits at the retained endpoint. -/
  left : candidate.right retainedTarget = false
  /-- and is the only wall direction there. -/
  unique : ∀ edge ∈ GluingDatum.incidentEdges wall, candidate.right edge = false →
    edge = retainedTarget

section Candidate

variable {candidate : BalancedGlobal.Candidate target degree data wall}

/-- Two sheets in one block of the retained endpoint name one source vertex. -/
theorem sourceEndpoint_old_eq_of_rel (first second : Fin degree)
    (hRel : (pasted candidate).left.Rel first second) :
    candidate.datum.sourceEndpoint (oldVertex target wall) first =
      candidate.datum.sourceEndpoint (oldVertex target wall) second := by
  refine (candidate.datum.sourceEndpoint_eq_iff (oldVertex target wall) first _).mpr
    ⟨rfl, ?_⟩
  have hVertex : candidate.datum.vertexPartition (oldVertex target wall) =
      (pasted candidate).left :=
    GlobalResolution.expandedVertexPartition_old_wall data wall _
  change (candidate.datum.vertexPartition (oldVertex target wall)).Rel first
    ((candidate.datum.vertexPartition (oldVertex target wall)).repr second)
  rw [hVertex]
  exact hRel.trans ((pasted candidate).left.rel_repr_right second)

/-- Two sheets in one block of the fresh endpoint name one source vertex. -/
theorem sourceEndpoint_fresh_eq_of_rel (first second : Fin degree)
    (hRel : (pasted candidate).right.Rel first second) :
    candidate.datum.sourceEndpoint (freshVertex target) first =
      candidate.datum.sourceEndpoint (freshVertex target) second := by
  refine (candidate.datum.sourceEndpoint_eq_iff (freshVertex target) first _).mpr
    ⟨rfl, ?_⟩
  have hVertex : candidate.datum.vertexPartition (freshVertex target) =
      (pasted candidate).right :=
    GlobalResolution.expandedVertexPartition_fresh data wall _
  change (candidate.datum.vertexPartition (freshVertex target)).Rel first
    ((candidate.datum.vertexPartition (freshVertex target)).repr second)
  rw [hVertex]
  exact hRel.trans ((pasted candidate).right.rel_repr_right second)

/-- The new occurrence through a sheet meets both of its new endpoints. -/
theorem newSourceEdge_incident_old (sheet : Fin degree) :
    Incident candidate.datum (candidate.newSourceEdge sheet)
      (candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  Or.inl (congrArg Prod.fst (GlobalResolution.sourceEnds_newSourceEdge data wall
    candidate.right (pasted candidate)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet))

theorem newSourceEdge_incident_fresh (sheet : Fin degree) :
    Incident candidate.datum (candidate.newSourceEdge sheet)
      (candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
  Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
    candidate.right (pasted candidate)
    (GlobalAssembly.blockwiseCompatible _ _ _ _ _ candidate.exterior) sheet))

/-- A retained occurrence and a new occurrence are never equal: they lie over
different target occurrences. -/
theorem oldSourceEdge_ne_newSourceEdge (edge : data.SourceEdge) (sheet : Fin degree) :
    candidate.oldSourceEdge edge ≠ candidate.newSourceEdge sheet := by
  intro hEqual
  have hTargets := congrArg (fun item : candidate.datum.SourceEdge ↦ item.1.1) hEqual
  rw [BalancedGlobal.Candidate.oldSourceEdge_target,
    BalancedGlobal.Candidate.newSourceEdge_target] at hTargets
  cases (occurrenceEquiv target wall candidate.right).injective hTargets


/-- Two regrown occurrences coincide exactly when their sheets share a block
of the pasted new edge. -/
theorem newSourceEdge_eq_iff_rel (first second : Fin degree) :
    candidate.newSourceEdge first = candidate.newSourceEdge second ↔
      (pasted candidate).newEdge.Rel first second := by
  constructor
  · intro hEqual
    have hSheets := congrArg (fun edge : candidate.datum.SourceEdge ↦ edge.1.2) hEqual
    rw [BalancedGlobal.Candidate.newSourceEdge_sheet,
      BalancedGlobal.Candidate.newSourceEdge_sheet] at hSheets
    exact hSheets
  · intro hRel
    refine Subtype.ext (Prod.ext rfl ?_)
    change (pasted candidate).newEdge.repr first = (pasted candidate).newEdge.repr second
    exact hRel

/-- The fresh endpoint of any candidate carries the new occurrence and every
wall direction assigned to the fresh side. -/
theorem target_incident_fresh (candidate : BalancedGlobal.Candidate target degree data wall) :
    GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (freshVertex target) =
      insert (occurrenceEquiv target wall candidate.right none)
        ((wallEdgesAssigned target wall candidate.right true).image
          fun edge ↦ occurrenceEquiv target wall candidate.right (some edge)) := by
  classical
  ext edge
  obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall candidate.right).surjective edge
  rw [Finset.mem_insert, Finset.mem_image]
  cases label with
  | none =>
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_none]
      exact ⟨fun _ ↦ Or.inl trivial, fun _ ↦ Or.inr rfl⟩
  | some place =>
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_some,
        (occurrenceEquiv target wall candidate.right).injective.eq_iff,
        reduceCtorEq, false_or, Option.some.injEq, exists_eq_right,
        mem_wallEdgesAssigned]
      exact ⟨fun hAt ↦ (oldEnds_incident_freshVertex_iff target wall candidate.right place).mp hAt,
        fun hAt ↦ (oldEnds_incident_freshVertex_iff target wall candidate.right place).mpr hAt⟩

/-- The complete source incidence count at a fresh new endpoint: the new
occurrences inside its block, plus the fresh-side old occurrences inside it. -/
theorem card_incident_fresh (candidate : BalancedGlobal.Candidate target degree data wall)
    (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge candidate.datum
        (candidate.datum.sourceEndpoint (freshVertex target) sheet)) =
      (pasted candidate).newEdge.blockCountWithin (pasted candidate).right sheet +
        ∑ edge ∈ wallEdgesAssigned target wall candidate.right true,
          (data.edgePartition edge).blockCountWithin (pasted candidate).right sheet := by
  classical
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (freshVertex target),
    (candidate.datum.edgePartition edge).blockCountWithin
      (candidate.datum.vertexPartition (freshVertex target))
      ((candidate.datum.vertexPartition (freshVertex target)).repr sheet)) = _
  rw [target_incident_fresh candidate]
  have hNotMem : occurrenceEquiv target wall candidate.right none ∉
      (wallEdgesAssigned target wall candidate.right true).image
        fun edge ↦ occurrenceEquiv target wall candidate.right (some edge) := by
    rw [Finset.mem_image]
    rintro ⟨place, _, hEqual⟩
    cases (occurrenceEquiv target wall candidate.right).injective hEqual
  rw [Finset.sum_insert hNotMem, Finset.sum_image (fun _ _ _ _ hEqual ↦
    Option.some.inj ((occurrenceEquiv target wall candidate.right).injective hEqual))]
  have hVertex : candidate.datum.vertexPartition (freshVertex target) =
      (pasted candidate).right :=
    GlobalResolution.expandedVertexPartition_fresh data wall _
  have hNew : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right none) =
      (pasted candidate).newEdge :=
    GlobalResolution.expandedEdgePartition_new data wall _ _
  rw [hVertex, hNew,
    SheetPartition.blockCountWithin_congr _ _ ((pasted candidate).right.rel_repr_left sheet)]
  congr 1
  refine Finset.sum_congr rfl fun place _ ↦ ?_
  have hOld : candidate.datum.edgePartition
      (occurrenceEquiv target wall candidate.right (some place)) =
      data.edgePartition place :=
    GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hOld,
    SheetPartition.blockCountWithin_congr _ _ ((pasted candidate).right.rel_repr_left sheet)]

end Candidate

namespace WallCandidate

variable (wc : WallCandidate data wall)

/-- Every wall direction other than the retained one is assigned to the fresh
side. -/
theorem right_eq_true_iff (edge : target.edges) (hMem : edge ∈ GluingDatum.incidentEdges wall) :
    wc.candidate.right edge = true ↔ edge ≠ wc.retainedTarget := by
  constructor
  · intro hRight hEqual
    rw [hEqual, wc.left] at hRight
    exact Bool.noConfusion hRight
  · intro hNe
    cases hRight : wc.candidate.right edge with
    | false => exact absurd (wc.unique edge hMem hRight) hNe
    | true => rfl

/-- The retained endpoint carries exactly the new occurrence and the retained
direction. -/
theorem target_incident_old :
    GluingDatum.incidentEdges (target := graph target wall wc.candidate.right)
        (oldVertex target wall) =
      {occurrenceEquiv target wall wc.candidate.right none,
        occurrenceEquiv target wall wc.candidate.right (some wc.retainedTarget)} := by
  classical
  ext edge
  obtain ⟨label, rfl⟩ := (occurrenceEquiv target wall wc.candidate.right).surjective edge
  rw [Finset.mem_insert, Finset.mem_singleton,
    (occurrenceEquiv target wall wc.candidate.right).injective.eq_iff,
    (occurrenceEquiv target wall wc.candidate.right).injective.eq_iff]
  cases label with
  | none =>
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_none]
      exact ⟨fun _ ↦ Or.inl trivial, fun _ ↦ Or.inl rfl⟩
  | some place =>
      simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and, occurrenceEquiv_some, reduceCtorEq, false_or, Option.some.injEq]
      constructor
      · intro hAt
        obtain ⟨hMem, hRight⟩ :=
          (oldEnds_incident_oldVertex_iff target wall wc.candidate.right place).mp hAt
        exact wc.unique place (by
          simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
            true_and] using hMem) hRight
      · rintro rfl
        refine (oldEnds_incident_oldVertex_iff target wall wc.candidate.right _).mpr
          ⟨?_, wc.left⟩
        simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
          true_and] using wc.target_mem

/-- The complete source incidence count at a retained new endpoint: the new
occurrences inside its block, plus the retained direction's occurrences
inside it. -/
theorem card_incident_old (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge wc.candidate.datum
        (wc.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) =
      (pasted wc.candidate).newEdge.blockCountWithin (pasted wc.candidate).left sheet +
        (data.edgePartition wc.retainedTarget).blockCountWithin
          (pasted wc.candidate).left sheet := by
  classical
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  change (∑ edge ∈ GluingDatum.incidentEdges (oldVertex target wall),
    (wc.candidate.datum.edgePartition edge).blockCountWithin
      (wc.candidate.datum.vertexPartition (oldVertex target wall))
      ((wc.candidate.datum.vertexPartition (oldVertex target wall)).repr sheet)) = _
  rw [wc.target_incident_old]
  have hNe : occurrenceEquiv target wall wc.candidate.right none ≠
      occurrenceEquiv target wall wc.candidate.right (some wc.retainedTarget) :=
    (occurrenceEquiv target wall wc.candidate.right).injective.ne (by simp)
  rw [Finset.sum_pair hNe]
  have hVertex : wc.candidate.datum.vertexPartition (oldVertex target wall) =
      (pasted wc.candidate).left :=
    GlobalResolution.expandedVertexPartition_old_wall data wall _
  have hNew : wc.candidate.datum.edgePartition
      (occurrenceEquiv target wall wc.candidate.right none) =
      (pasted wc.candidate).newEdge :=
    GlobalResolution.expandedEdgePartition_new data wall _ _
  have hOld : wc.candidate.datum.edgePartition
      (occurrenceEquiv target wall wc.candidate.right (some wc.retainedTarget)) =
      data.edgePartition wc.retainedTarget :=
    GlobalResolution.expandedEdgePartition_old data wall _ _ _
  rw [hVertex, hNew, hOld,
    SheetPartition.blockCountWithin_congr _ _ ((pasted wc.candidate).left.rel_repr_left sheet),
    SheetPartition.blockCountWithin_congr _ _ ((pasted wc.candidate).left.rel_repr_left sheet)]

/-- A retained occurrence in the retained direction is the canonical one
through its own sheet. -/
theorem sourceEdge_retained_self {edge : data.SourceEdge}
    (hTarget : edge.1.1 = wc.retainedTarget) :
    data.sourceEdge wc.retainedTarget edge.1.2 = edge := by
  rw [show wc.retainedTarget = edge.1.1 from hTarget.symm]
  exact GluingDatum.sourceEdge_self data edge

end WallCandidate

/-! ### Two-star walls

A two-star candidate whose `right` is the star's own retains label `0`; label
`1` is the only fresh-side direction, so the fresh endpoint dictionary
collapses to one term.  These are the forms that `W2MkkStableGraph` and the
chain of Case {w2-r2-nd3-P} consume. -/

section TwoStar

variable (candidate : BalancedGlobal.Candidate target degree data wall)
  (twoStar : W2R1Target.TwoStar target wall)

/-- A two-star candidate retains the star's label `0`. -/
noncomputable def WallCandidate.ofTwoStar
    (hRight : ∀ edge, candidate.right edge = twoStar.right edge) :
    WallCandidate data wall where
  candidate := candidate
  retainedTarget := twoStar.edge 0
  target_mem := twoStar.edge_mem_incidentEdges 0
  left := by rw [hRight]; exact twoStar.right_edge_zero
  unique := by
    intro edge hMem hFalse
    obtain ⟨label, hLabel⟩ := twoStar.label.surjective ⟨edge, hMem⟩
    have hEdge : edge = twoStar.edge label := (congrArg Subtype.val hLabel).symm
    rw [hEdge, hRight] at hFalse
    rw [hEdge]
    match label, hFalse with
    | 0, _ => rfl
    | 1, hFalse => exact absurd hFalse (by rw [twoStar.right_edge_one]; decide)

variable {candidate twoStar}

/-- The retained endpoint of a two-star candidate carries exactly the new
occurrence and the two-star's label-`0` direction. -/
theorem target_incident_pair_old (hRight : ∀ edge, candidate.right edge = twoStar.right edge) :
    GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (oldVertex target wall) =
      {occurrenceEquiv target wall candidate.right none,
        occurrenceEquiv target wall candidate.right (some (twoStar.edge 0))} :=
  (WallCandidate.ofTwoStar candidate twoStar hRight).target_incident_old

theorem wallEdgesAssigned_true_eq_of_right
    (hRight : ∀ edge, candidate.right edge = twoStar.right edge) :
    wallEdgesAssigned target wall candidate.right true = {twoStar.edge 1} := by
  rw [show candidate.right = twoStar.right from funext hRight]
  exact twoStar.wallEdgesAssigned_true

/-- The fresh endpoint of a two-star candidate carries exactly the new
occurrence and the two-star's label-`1` direction. -/
theorem target_incident_pair_fresh (hRight : ∀ edge, candidate.right edge = twoStar.right edge) :
    GluingDatum.incidentEdges (target := graph target wall candidate.right)
        (freshVertex target) =
      {occurrenceEquiv target wall candidate.right none,
        occurrenceEquiv target wall candidate.right (some (twoStar.edge 1))} := by
  rw [target_incident_fresh candidate, wallEdgesAssigned_true_eq_of_right hRight,
    Finset.image_singleton]

/-- The complete source incidence count at a retained new endpoint of a
two-star candidate. -/
theorem card_incident_oldEndpoint
    (hRight : ∀ edge, candidate.right edge = twoStar.right edge) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge candidate.datum
        (candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) =
      (pasted candidate).newEdge.blockCountWithin (pasted candidate).left sheet +
        (data.edgePartition (twoStar.edge 0)).blockCountWithin
          (pasted candidate).left sheet :=
  (WallCandidate.ofTwoStar candidate twoStar hRight).card_incident_old sheet

/-- The complete source incidence count at a fresh new endpoint of a two-star
candidate. -/
theorem card_incident_freshEndpoint
    (hRight : ∀ edge, candidate.right edge = twoStar.right edge) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge candidate.datum
        (candidate.datum.sourceEndpoint (freshVertex target) sheet)) =
      (pasted candidate).newEdge.blockCountWithin (pasted candidate).right sheet +
        (data.edgePartition (twoStar.edge 1)).blockCountWithin
          (pasted candidate).right sheet := by
  rw [card_incident_fresh candidate sheet, wallEdgesAssigned_true_eq_of_right hRight,
    Finset.sum_singleton]

end TwoStar


/-! ## §3  The background: one direction's own star off the distinguished block

Above every wall block other than the distinguished one a member installs the
retained direction's **own** star.  So each background new occurrence has one
old representative — the retained direction's occurrence through the same
sheet — and carries its pruning status, its stable row and its index.  The
installation is recorded block by block: at a background sheet the pasted
retained endpoint and the pasted new edge carry the retained direction's
class, and the pasted fresh endpoint the whole wall block.  Nothing here says
which local resolution produced those blocks. -/

/-- What a member looks like away from the distinguished wall block. -/
structure BackgroundShape (data : GluingDatum target degree) (wall : target.V)
    extends WallCandidate data wall where
  /-- The distinguished block's anchor. -/
  selected : Fin degree
  /-- Off that block the retained endpoint carries the retained direction's
  class. -/
  left_block : ∀ {sheet : Fin degree},
    ¬ (data.vertexPartition wall).Rel selected sheet →
      (pasted candidate).left.block sheet = (data.edgePartition retainedTarget).block sheet
  /-- the fresh endpoint the whole wall block. -/
  right_block : ∀ {sheet : Fin degree},
    ¬ (data.vertexPartition wall).Rel selected sheet →
      (pasted candidate).right.block sheet = (data.vertexPartition wall).block sheet
  /-- and the new edge the retained direction's class. -/
  newEdge_block : ∀ {sheet : Fin degree},
    ¬ (data.vertexPartition wall).Rel selected sheet →
      (pasted candidate).newEdge.block sheet = (data.edgePartition retainedTarget).block sheet
  genus_eq : genus candidate.datum.sourceGraph = genus data.sourceGraph

namespace BackgroundShape

variable (shape : BackgroundShape data wall)

/-- The pasted local resolution of the member. -/
noncomputable def pasted : LocalResolution degree :=
  LimitChainCore.pasted shape.candidate

theorem pasted_left_block {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    shape.pasted.left.block sheet =
      (data.edgePartition shape.retainedTarget).block sheet :=
  shape.left_block hSheet

/-- Off the distinguished block the trivalent endpoint carries the whole wall
block. -/
theorem pasted_right_block {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    shape.pasted.right.block sheet = (data.vertexPartition wall).block sheet :=
  shape.right_block hSheet

theorem pasted_newEdge_block {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    shape.pasted.newEdge.block sheet =
      (data.edgePartition shape.retainedTarget).block sheet :=
  shape.newEdge_block hSheet


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
          (data.sourceEdge shape.retainedTarget sheet))
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
  oldSourceEdge_incident_old shape.candidate shape.retainedTarget
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
        (data.sourceEdge shape.retainedTarget sheet) := by
  rcases ResolutionPruning.sourceEdge_cases shape.candidate edge with
    ⟨old, rfl⟩ | ⟨new, rfl⟩
  · right
    obtain ⟨hData, hRight⟩ :=
      old_incident_old_selected_info shape.candidate
        (WallBlock.ofSheet data wall sheet) sheet
        ((data.vertexPartition wall).rel_repr_left sheet) old hIncident
    have hTarget : old.1.1 = shape.retainedTarget := shape.unique _
      ((incident_iff_target_mem_and_rel data old _).mp hData).1 hRight
    have hSheetRel := old_incident_old_sheet_rel shape.candidate sheet old
      hIncident
    have hMem : old.1.2 ∈ shape.pasted.left.block sheet :=
      (shape.pasted.left.mem_block_iff _ _).mpr hSheetRel
    rw [shape.pasted_left_block hSheet] at hMem
    have hEdgeRel :=
      ((data.edgePartition shape.retainedTarget).mem_block_iff _ _).mp hMem
    refine congrArg shape.candidate.oldSourceEdge (Subtype.ext (Prod.ext ?_ ?_)).symm
    · exact hTarget.symm
    · change (data.edgePartition shape.retainedTarget).repr sheet = old.1.2
      have hRepr : (data.edgePartition shape.retainedTarget).repr old.1.2 =
          old.1.2 := by rw [← hTarget]; exact old.2
      exact hEdgeRel.trans hRepr
  · left
    have hSheetRel := new_incident_old_sheet_rel
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
          (data.sourceEdge shape.retainedTarget sheet)} := by
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
      IsDangling data (data.sourceEdge shape.retainedTarget sheet) := by
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
          (data.sourceEdge shape.retainedTarget sheet)} := by
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
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.retainedTarget sheet)) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
      {shape.candidate.newSourceEdge sheet,
        shape.candidate.oldSourceEdge
          (data.sourceEdge shape.retainedTarget sheet)} := by
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
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.retainedTarget sheet)) :
    nonDanglingValency shape.candidate.datum
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2 := by
  rw [← card_nonDanglingIncident,
    shape.nonDanglingIncident_old hValid hSheet hSurvives]
  exact Finset.card_pair (shape.new_ne_old _ _)

/-- **Every surviving background new occurrence lies in its old
representative's stable row.** -/
theorem new_stablePath_eq (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (hSurvives : ¬ IsDangling data (data.sourceEdge shape.retainedTarget sheet)) :
    NonDanglingEdge.stablePath
        (⟨shape.candidate.newSourceEdge sheet,
          fun h ↦ hSurvives ((shape.new_isDangling_iff hValid hSheet).mp h)⟩ :
          NonDanglingEdge shape.candidate.datum) =
      NonDanglingEdge.stablePath
        (⟨shape.candidate.oldSourceEdge
            (data.sourceEdge shape.retainedTarget sheet),
          fun h ↦ hSurvives ((shape.old_isDangling_iff hValid _).mp h)⟩ :
          NonDanglingEdge shape.candidate.datum) := by
  refine stablePath_eq_of_consecutive ⟨?_, _, shape.new_incident_old sheet,
    shape.background_incident_old sheet,
    shape.old_nonDanglingValency_eq_two hValid hSheet hSurvives⟩
  intro hEq
  exact shape.new_ne_old sheet _ (congrArg Subtype.val hEq)

/-- **And carries its index**: `σ⁽ᵠ⁾(J₀,1) = σ₀(J₀,α)` in the paper's notation. -/
theorem newIndex_eq {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    shape.candidate.datum.sourceEdgeIndex
        (shape.candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex (data.sourceEdge shape.retainedTarget sheet) := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    GluingDatum.sourceEdgeIndex_sourceEdge]
  change shape.pasted.newEdge.blockCard sheet =
    (data.edgePartition shape.retainedTarget).blockCard sheet
  unfold SheetPartition.blockCard
  rw [shape.pasted_newEdge_block hSheet]


end BackgroundShape

/-! ### The background wall blocks

Away from the distinguished block the member installs the retained direction's
own star.  The retained endpoint above a background sheet carries only that
direction and the member's own new occurrence; the trivalent endpoint carries
the whole wall block and every direction but the retained one. -/

namespace Background

variable (shape : BackgroundShape data wall)

/-- Sheets of one background wall block give one trivalent endpoint. -/
theorem fresh_endpoint_eq {first second : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel shape.selected first)
    (hRel : (data.vertexPartition wall).Rel first second) :
    shape.candidate.datum.sourceEndpoint (freshVertex target) first =
      shape.candidate.datum.sourceEndpoint (freshVertex target) second := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change shape.pasted.right.repr first = shape.pasted.right.repr second
    have hMem : second ∈ (data.vertexPartition wall).block first :=
      ((data.vertexPartition wall).mem_block_iff first second).mpr hRel
    rw [← shape.pasted_right_block hFirst] at hMem
    exact (shape.pasted.right.mem_block_iff first second).mp hMem

/-- Background new occurrences are indexed by the background direction's own
classes. -/
theorem newSourceEdge_eq_of_edge_rel {first second : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel shape.selected first)
    (hRel : (data.edgePartition shape.retainedTarget).Rel first second) :
    shape.candidate.newSourceEdge second = shape.candidate.newSourceEdge first := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change shape.pasted.newEdge.repr second = shape.pasted.newEdge.repr first
    have hMem : second ∈ (data.edgePartition shape.retainedTarget).block first :=
      ((data.edgePartition shape.retainedTarget).mem_block_iff first second).mpr
        hRel
    rw [← shape.pasted_newEdge_block hFirst] at hMem
    exact ((shape.pasted.newEdge.mem_block_iff first second).mp hMem).symm

theorem newSourceEdge_eq_iff {first second : Fin degree}
    (hFirst : ¬ (data.vertexPartition wall).Rel shape.selected first) :
    shape.candidate.newSourceEdge first = shape.candidate.newSourceEdge second ↔
      (data.edgePartition shape.retainedTarget).Rel first second := by
  constructor
  · intro hEqual
    have hRel : shape.pasted.newEdge.Rel first second :=
      congrArg (fun item : shape.candidate.datum.SourceEdge ↦ item.1.2) hEqual
    have hMem : second ∈ shape.pasted.newEdge.block first :=
      (shape.pasted.newEdge.mem_block_iff _ _).mpr hRel
    rw [shape.pasted_newEdge_block hFirst] at hMem
    exact ((data.edgePartition shape.retainedTarget).mem_block_iff _ _).mp hMem
  · intro hRel
    exact (newSourceEdge_eq_of_edge_rel shape hFirst hRel).symm

/-- A new occurrence meets the trivalent endpoint above every sheet of its own
wall block. -/
theorem new_incident_fresh {sheet other : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (hRel : (data.vertexPartition wall).Rel sheet other) :
    Incident shape.candidate.datum (shape.candidate.newSourceEdge other)
      (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
  have hBase : Incident shape.candidate.datum
      (shape.candidate.newSourceEdge other)
      (shape.candidate.datum.sourceEndpoint (freshVertex target) other) :=
    Or.inr (congrArg Prod.snd (GlobalResolution.sourceEnds_newSourceEdge data wall
      shape.candidate.right shape.pasted
      (GlobalAssembly.blockwiseCompatible _ _ _ _ _ shape.candidate.exterior)
      other))
  rwa [fresh_endpoint_eq shape hSheet hRel]

/-- Conversely a new occurrence at a background trivalent endpoint is named by
a sheet of that endpoint's wall block. -/
theorem new_incident_fresh_rel {sheet new : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (hIncident : Incident shape.candidate.datum
      (shape.candidate.newSourceEdge new)
      (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    (data.vertexPartition wall).Rel sheet (shape.pasted.newEdge.repr new) := by
  have hOutgoing := (incident_iff_target_mem_and_rel shape.candidate.datum
    (shape.candidate.newSourceEdge new)
    (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet)).mp hIncident
  change occurrenceEquiv target wall shape.candidate.right none ∈
      GluingDatum.incidentEdges (freshVertex target) ∧
    shape.pasted.right.Rel (shape.pasted.right.repr sheet)
      (shape.pasted.newEdge.repr new) at hOutgoing
  have hRightRel : shape.pasted.right.Rel sheet
      (shape.pasted.newEdge.repr new) :=
    (shape.pasted.right.rel_repr_right sheet).trans hOutgoing.2
  have hMem : shape.pasted.newEdge.repr new ∈ shape.pasted.right.block sheet :=
    (shape.pasted.right.mem_block_iff _ _).mpr hRightRel
  rw [shape.pasted_right_block hSheet] at hMem
  exact ((data.vertexPartition wall).mem_block_iff _ _).mp hMem

/-- **The complete incidence dictionary at a background trivalent endpoint for
retained occurrences.** -/
theorem old_incident_fresh_iff {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (old : data.SourceEdge) :
    Incident shape.candidate.datum (shape.candidate.oldSourceEdge old)
        (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) ↔
      Incident data old (data.sourceEndpoint wall sheet) ∧
        old.1.1 ≠ shape.retainedTarget := by
  constructor
  · intro hIncident
    obtain ⟨hData, hRight⟩ := old_incident_fresh_selected_info
      shape.candidate (WallBlock.ofSheet data wall sheet) sheet
      ((data.vertexPartition wall).rel_repr_left sheet) old hIncident
    rw [sourceVertex_ofSheet data wall sheet] at hData
    exact ⟨hData, (shape.right_eq_true_iff old.1.1
      ((incident_iff_target_mem_and_rel data old _).mp hData).1).mp hRight⟩
  · rintro ⟨hData, hNe⟩
    have hMem : old.1.1 ∈ GluingDatum.incidentEdges wall :=
      ((incident_iff_target_mem_and_rel data old _).mp hData).1
    have hBase : Incident shape.candidate.datum
        (shape.candidate.oldSourceEdge (data.sourceEdge old.1.1 old.1.2))
        (shape.candidate.datum.sourceEndpoint (freshVertex target) old.1.2) :=
      M11SplitSurvival.oldSourceEdge_incident_fresh shape.candidate old.1.1 hMem
        ((shape.right_eq_true_iff old.1.1 hMem).mpr hNe) old.1.2
    rw [GluingDatum.sourceEdge_self data old] at hBase
    rwa [← fresh_endpoint_eq shape hSheet
      (wall_rel_of_incident data wall sheet old hData)] at hBase


/-! ### The replacement bijection at a background trivalent endpoint -/

/-- An occurrence at a background wall vertex has a background sheet. -/
theorem background_of_incident {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    {edge : data.SourceEdge}
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    ¬ (data.vertexPartition wall).Rel shape.selected edge.1.2 := fun hRel ↦
  hSheet (hRel.trans (wall_rel_of_incident data wall sheet edge hIncident).symm)

/-- **The member occurrence representing an incoming survivor at a background
wall vertex**: itself, unless it points along the background direction, in
which case the member's own new occurrence through its sheet. -/
noncomputable def replace (shape : BackgroundShape data wall)
    (edge : data.SourceEdge) : shape.candidate.datum.SourceEdge :=
  if edge.1.1 = shape.retainedTarget then
    shape.candidate.newSourceEdge edge.1.2
  else shape.candidate.oldSourceEdge edge

theorem replace_of_target {edge : data.SourceEdge}
    (hTarget : edge.1.1 = shape.retainedTarget) :
    replace shape edge = shape.candidate.newSourceEdge edge.1.2 := ite_eq_left hTarget

theorem replace_of_target_ne {edge : data.SourceEdge}
    (hTarget : edge.1.1 ≠ shape.retainedTarget) :
    replace shape edge = shape.candidate.oldSourceEdge edge := ite_eq_right hTarget

theorem replace_survives (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    ¬ IsDangling shape.candidate.datum (replace shape edge) := by
  by_cases hTarget : edge.1.1 = shape.retainedTarget
  · rw [replace_of_target shape hTarget]
    intro hDangling
    apply hSurvives
    rw [← shape.sourceEdge_retained_self hTarget]
    exact (shape.new_isDangling_iff hValid
      (background_of_incident shape hSheet hIncident)).mp hDangling
  · rw [replace_of_target_ne shape hTarget]
    exact ResolutionSurvival.not_isDangling_oldSourceEdge shape.candidate hValid.1
      edge hSurvives

theorem replace_incident {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    {edge : data.SourceEdge}
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet)) :
    Incident shape.candidate.datum (replace shape edge)
      (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) := by
  by_cases hTarget : edge.1.1 = shape.retainedTarget
  · rw [replace_of_target shape hTarget]
    exact new_incident_fresh shape hSheet
      (wall_rel_of_incident data wall sheet edge hIncident)
  · rw [replace_of_target_ne shape hTarget]
    exact (old_incident_fresh_iff shape hSheet edge).mpr ⟨hIncident, hTarget⟩

/-- **The background trivalent endpoint's surviving star is the image of the
incoming one.**  No ramification bound and no no-return hypothesis is used, so
this holds at arbitrary old valency. -/
theorem nonDanglingIncident_fresh_eq_image (hValid : data.Valid)
    {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) =
      (nonDanglingIncident data (data.sourceEndpoint wall sheet)).image
        (replace shape) := by
  classical
  ext item
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases shape.candidate item with
      ⟨old, rfl⟩ | ⟨new, rfl⟩
    · obtain ⟨hData, hNe⟩ := (old_incident_fresh_iff shape hSheet old).mp hIncident
      refine Finset.mem_image.mpr ⟨old, (mem_nonDanglingIncident _ _ _).mpr
        ⟨fun hDangling ↦ hSurvives
          ((shape.old_isDangling_iff hValid old).mpr hDangling), hData⟩, ?_⟩
      exact replace_of_target_ne shape hNe
    · have hRel := new_incident_fresh_rel shape hSheet hIncident
      have hRepr : shape.candidate.newSourceEdge
          (shape.pasted.newEdge.repr new) =
            shape.candidate.newSourceEdge new :=
        newSourceEdge_repr shape.candidate new
      have hBackground : ¬ (data.vertexPartition wall).Rel shape.selected
          (shape.pasted.newEdge.repr new) := fun hSel ↦ hSheet (hSel.trans hRel.symm)
      have hNewSurvives : ¬ IsDangling shape.candidate.datum
          (shape.candidate.newSourceEdge (shape.pasted.newEdge.repr new)) := by
        rw [hRepr]; exact hSurvives
      have hOldSurvives : ¬ IsDangling data (data.sourceEdge
          shape.retainedTarget (shape.pasted.newEdge.repr new)) :=
        fun hDangling ↦ hNewSurvives
          ((shape.new_isDangling_iff hValid hBackground).mpr hDangling)
      refine Finset.mem_image.mpr ⟨data.sourceEdge shape.retainedTarget
        (shape.pasted.newEdge.repr new), (mem_nonDanglingIncident _ _ _).mpr
        ⟨hOldSurvives, ?_⟩, ?_⟩
      · rw [sourceEndpoint_eq_of_rel data wall hRel]
        exact incident_sourceEdge_sourceEndpoint data wall shape.retainedTarget
          shape.target_mem _
      · rw [replace_of_target shape (by rfl)]
        refine Eq.trans ?_ hRepr
        exact newSourceEdge_eq_of_edge_rel shape hBackground
          ((data.edgePartition shape.retainedTarget).rel_repr_right _)
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨replace_survives shape hValid hSheet hSurvives hIncident,
        replace_incident shape hSheet hIncident⟩

theorem replace_injOn {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    Set.InjOn (replace shape)
      ↑(nonDanglingIncident data (data.sourceEndpoint wall sheet)) := by
  intro first hFirst second hSecond hEqual
  have hFirstIncident : Incident data first (data.sourceEndpoint wall sheet) :=
    ((mem_nonDanglingIncident _ _ _).mp hFirst).2
  have hSecondIncident : Incident data second (data.sourceEndpoint wall sheet) :=
    ((mem_nonDanglingIncident _ _ _).mp hSecond).2
  by_cases hFirstTarget : first.1.1 = shape.retainedTarget
  · by_cases hSecondTarget : second.1.1 = shape.retainedTarget
    · rw [replace_of_target shape hFirstTarget,
        replace_of_target shape hSecondTarget] at hEqual
      have hRel := (newSourceEdge_eq_iff shape
        (background_of_incident shape hSheet hFirstIncident)).mp hEqual
      have hSource := (sourceEdge_eq_iff_rel data shape.retainedTarget
        first.1.2 second.1.2).mpr hRel
      rw [shape.sourceEdge_retained_self hFirstTarget,
        shape.sourceEdge_retained_self hSecondTarget] at hSource
      exact hSource
    · rw [replace_of_target shape hFirstTarget,
        replace_of_target_ne shape hSecondTarget] at hEqual
      exact absurd hEqual (shape.new_ne_old _ _)
  · by_cases hSecondTarget : second.1.1 = shape.retainedTarget
    · rw [replace_of_target_ne shape hFirstTarget,
        replace_of_target shape hSecondTarget] at hEqual
      exact absurd hEqual.symm (shape.new_ne_old _ _)
    · rw [replace_of_target_ne shape hFirstTarget,
        replace_of_target_ne shape hSecondTarget] at hEqual
      exact ResolutionCut.oldSourceEdge_injective shape.candidate hEqual

/-- **Background trivalent endpoints keep the incoming surviving valency.** -/
theorem nonDanglingValency_fresh_eq (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet) :
    nonDanglingValency shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  classical
  rw [← card_nonDanglingIncident, ← card_nonDanglingIncident,
    nonDanglingIncident_fresh_eq_image shape hValid hSheet,
    Finset.card_image_of_injOn (replace_injOn shape hSheet)]

/-- **Every retained background survivor keeps the row of its replacement.** -/
theorem retained_stablePath_eq_replace (hValid : data.Valid) {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet))
    (hReplace : ¬ IsDangling shape.candidate.datum (replace shape edge)) :
    (retainedEdge shape.candidate hValid.1 ⟨edge, hSurvives⟩).stablePath =
      NonDanglingEdge.stablePath
        (⟨replace shape edge, hReplace⟩ : NonDanglingEdge shape.candidate.datum) := by
  by_cases hTarget : edge.1.1 = shape.retainedTarget
  · have hBackground := background_of_incident shape hSheet hIncident
    have hSelf := shape.sourceEdge_retained_self hTarget
    have hOldSurvives : ¬ IsDangling data
        (data.sourceEdge shape.retainedTarget edge.1.2) := by
      rw [hSelf]; exact hSurvives
    have hPath := shape.new_stablePath_eq hValid hBackground hOldSurvives
    refine Eq.trans ?_ (hPath.symm.trans ?_)
    · exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (congrArg shape.candidate.oldSourceEdge hSelf.symm))
    · exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (replace_of_target shape hTarget).symm)
  · exact congrArg NonDanglingEdge.stablePath
      (Subtype.ext (replace_of_target_ne shape hTarget).symm)


/-- **The background half of the lift's well-definedness.**  A consecutive
pair of the incoming stable quotient meeting a background wall vertex keeps one
outgoing row, at arbitrary old valency and with no ramification receipt. -/
theorem background_retained_eq_of_consecutive (hValid : data.Valid)
    {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (first second : NonDanglingEdge data) (hNe : first ≠ second)
    (hFirst : Incident data first.1 (data.sourceEndpoint wall sheet))
    (hSecond : Incident data second.1 (data.sourceEndpoint wall sheet))
    (hValency : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2) :
    (retainedEdge shape.candidate hValid.1 first).stablePath =
      (retainedEdge shape.candidate hValid.1 second).stablePath := by
  classical
  have hFirstMem : first.1 ∈ nonDanglingIncident data
      (data.sourceEndpoint wall sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨first.2, hFirst⟩
  have hSecondMem : second.1 ∈ nonDanglingIncident data
      (data.sourceEndpoint wall sheet) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨second.2, hSecond⟩
  have hFirstReplace := replace_survives shape hValid hSheet first.2 hFirst
  have hSecondReplace := replace_survives shape hValid hSheet second.2 hSecond
  have hNeReplace :
      (⟨replace shape first.1, hFirstReplace⟩ :
          NonDanglingEdge shape.candidate.datum) ≠
        ⟨replace shape second.1, hSecondReplace⟩ := by
    intro hEqual
    exact hNe (Subtype.ext (replace_injOn shape hSheet
      (Finset.mem_coe.mpr hFirstMem) (Finset.mem_coe.mpr hSecondMem)
      (congrArg Subtype.val hEqual)))
  have hConsecutive : Consecutive shape.candidate.datum
      ⟨replace shape first.1, hFirstReplace⟩
      ⟨replace shape second.1, hSecondReplace⟩ :=
    ⟨hNeReplace, shape.candidate.datum.sourceEndpoint (freshVertex target) sheet,
      replace_incident shape hSheet hFirst, replace_incident shape hSheet hSecond,
      (nonDanglingValency_fresh_eq shape hValid hSheet).trans hValency⟩
  calc (retainedEdge shape.candidate hValid.1 first).stablePath
      = NonDanglingEdge.stablePath
          (⟨replace shape first.1, hFirstReplace⟩ :
            NonDanglingEdge shape.candidate.datum) :=
        retained_stablePath_eq_replace shape hValid hSheet first.2 hFirst _
    _ = NonDanglingEdge.stablePath
          (⟨replace shape second.1, hSecondReplace⟩ :
            NonDanglingEdge shape.candidate.datum) :=
        stablePath_eq_of_consecutive hConsecutive
    _ = (retainedEdge shape.candidate hValid.1 second).stablePath :=
        (retained_stablePath_eq_replace shape hValid hSheet second.2 hSecond _).symm

/-- The complete surviving star at a divalent background endpoint of surviving
valency two. -/
theorem nonDanglingIncident_old_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel shape.selected sheet)
    (hValency : nonDanglingValency shape.candidate.datum
      (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2) :
    nonDanglingIncident shape.candidate.datum
        (shape.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
      {shape.candidate.newSourceEdge sheet,
        shape.candidate.oldSourceEdge
          (data.sourceEdge shape.retainedTarget sheet)} := by
  classical
  refine Finset.eq_of_subset_of_card_le (shape.nonDanglingIncident_old_subset hSheet)
    (le_of_eq ?_)
  rw [Finset.card_pair (shape.new_ne_old _ _), card_nonDanglingIncident, hValency]

end Background

/-- The expanded target endpoint on one side of the new edge: `false` is the
retained copy of the wall and `true` the fresh copy. -/
def wallSide (target : CFGraph) (wall : target.V) (side : Bool) :
    TargetExpansion.Vertex target :=
  if side then freshVertex target else oldVertex target wall

@[simp] theorem wallSide_false (target : CFGraph) (wall : target.V) :
    wallSide target wall false = oldVertex target wall := rfl

@[simp] theorem wallSide_true (target : CFGraph) (wall : target.V) :
    wallSide target wall true = freshVertex target := rfl

/-! ## §4  The member's selected-star census, in three sizes

All members share the background shape and differ only in what the
distinguished block's endpoints carry.  `LiftData` is what the stable lift
needs (that no consecutive pair of the incoming stable quotient meets the
distinguished vertex); `SelectedData` adds the old representative of a
selected new occurrence and the surviving star at every selected endpoint of
surviving valency two, which is what the row descent and the limit matrices
need; `GraphData` adds the flag dictionary at the member's branch vertex,
which is what the stable incidence graph needs.  No numerical receipt and no
distinctness of stable rows appears anywhere. -/

/-- A member for which the incoming distinguished vertex is not divalent, so
that retention respects the incoming stable quotient. -/
structure LiftData (data : GluingDatum target degree) (wall : target.V)
    extends BackgroundShape data wall where
  valid : data.Valid
  /-- No consecutive pair of the incoming stable quotient meets the
  distinguished source vertex. -/
  selected_valency_ne_two :
    nonDanglingValency data (data.sourceEndpoint wall selected) ≠ 2

/-- A member together with the selected-block data the row descent and the
limit matrices need. -/
structure SelectedData (data : GluingDatum target degree) (wall : target.V)
    extends LiftData data wall where
  /-- The old occurrence a selected new occurrence represents. -/
  selectedRep : Fin degree → data.SourceEdge
  selectedRep_survives : ∀ sheet : Fin degree,
    (data.vertexPartition wall).Rel selected sheet →
      ¬ IsDangling data (selectedRep sheet)
  /-- Selected sheets carrying the same new occurrence carry the same
  representative. -/
  selectedRep_congr : ∀ first second : Fin degree,
    (data.vertexPartition wall).Rel selected first →
      (data.vertexPartition wall).Rel selected second →
      candidate.newSourceEdge first = candidate.newSourceEdge second →
        selectedRep first = selectedRep second
  /-- A surviving selected new occurrence lies in its representative's row. -/
  selected_new_stablePath : ∀ (sheet : Fin degree),
    (data.vertexPartition wall).Rel selected sheet →
    ∀ (hSurvives : ¬ IsDangling candidate.datum (candidate.newSourceEdge sheet))
      (hRep : ¬ IsDangling candidate.datum (candidate.oldSourceEdge (selectedRep sheet))),
      NonDanglingEdge.stablePath
          (⟨candidate.newSourceEdge sheet, hSurvives⟩ : NonDanglingEdge candidate.datum) =
        NonDanglingEdge.stablePath
          (⟨candidate.oldSourceEdge (selectedRep sheet), hRep⟩ :
            NonDanglingEdge candidate.datum)
  /-- A selected retained endpoint of surviving valency two carries exactly
  one new occurrence and its representative. -/
  selected_left_pair : ∀ sheet : Fin degree,
    (data.vertexPartition wall).Rel selected sheet →
    nonDanglingValency candidate.datum
        (candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2 →
    ∃ other : Fin degree,
      (data.vertexPartition wall).Rel selected other ∧
        nonDanglingIncident candidate.datum
            (candidate.datum.sourceEndpoint (oldVertex target wall) sheet) =
          {candidate.newSourceEdge other, candidate.oldSourceEdge (selectedRep other)}
  /-- The same at a selected fresh endpoint. -/
  selected_right_pair : ∀ sheet : Fin degree,
    (data.vertexPartition wall).Rel selected sheet →
    nonDanglingValency candidate.datum
        (candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2 →
    ∃ other : Fin degree,
      (data.vertexPartition wall).Rel selected other ∧
        nonDanglingIncident candidate.datum
            (candidate.datum.sourceEndpoint (freshVertex target) sheet) =
          {candidate.newSourceEdge other, candidate.oldSourceEdge (selectedRep other)}

/-- A member together with the flag dictionary at its branch vertex above the
distinguished block: everything the stable incidence graph needs. -/
structure GraphData (data : GluingDatum target degree) (wall : target.V)
    extends SelectedData data wall where
  /-- Which expanded endpoint above the distinguished block is the member's
  branch vertex: `false` the retained one, `true` the fresh one. -/
  selectedSide : Bool
  /-- The flag correspondence there, sending the incoming survivors at the
  distinguished vertex to the surviving occurrences of the member's branch
  star. -/
  selectedFlag : data.SourceEdge → candidate.datum.SourceEdge
  selectedFlag_star :
    nonDanglingIncident candidate.datum
        (candidate.datum.sourceEndpoint (wallSide target wall selectedSide) selected) =
      (nonDanglingIncident data (data.sourceEndpoint wall selected)).image selectedFlag
  selectedFlag_injOn : Set.InjOn selectedFlag
    ↑(nonDanglingIncident data (data.sourceEndpoint wall selected))
  /-- Every other endpoint above the distinguished block is divalent or
  entirely pruned. -/
  selected_not_branch : ∀ (side : Bool) (sheet : Fin degree),
    (data.vertexPartition wall).Rel selected sheet →
    candidate.datum.sourceEndpoint (wallSide target wall side) sheet ≠
      candidate.datum.sourceEndpoint (wallSide target wall selectedSide) selected →
    nonDanglingValency candidate.datum
      (candidate.datum.sourceEndpoint (wallSide target wall side) sheet) ≤ 2
  selectedFlag_row : ∀ (edge : data.SourceEdge) (hSurvives : ¬ IsDangling data edge),
    Incident data edge (data.sourceEndpoint wall selected) →
    ∀ hFlag : ¬ IsDangling candidate.datum (selectedFlag edge),
      NonDanglingEdge.stablePath (⟨selectedFlag edge, hFlag⟩ :
          NonDanglingEdge candidate.datum) =
        (retainedEdge candidate valid.1 ⟨edge, hSurvives⟩).stablePath


namespace LiftData

variable (rd : LiftData data wall)

/-! ### The stable lift -/

/-- **The defining relation of the incoming stable quotient is respected by
retention.**  The selected case is vacuous by trivalence of the distinguished
source vertex; the background case is the replacement bijection. -/
theorem retained_stablePath_eq_of_consecutive
    (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    (retainedEdge rd.candidate rd.valid.1 first).stablePath =
      (retainedEdge rd.candidate rd.valid.1 second).stablePath := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    have hValency' : nonDanglingValency data
        (data.sourceEndpoint wall vertex.1.2) = 2 := by
      rw [hVertex]; exact hValency
    have hFirst' : Incident data first.1
        (data.sourceEndpoint wall vertex.1.2) := by rw [hVertex]; exact hFirst
    have hSecond' : Incident data second.1
        (data.sourceEndpoint wall vertex.1.2) := by rw [hVertex]; exact hSecond
    by_cases hSelected : (data.vertexPartition wall).Rel
        rd.selected vertex.1.2
    · rw [← sourceEndpoint_eq_of_rel data wall hSelected] at hValency'
      exact absurd hValency' rd.selected_valency_ne_two
    · exact Background.background_retained_eq_of_consecutive rd.toBackgroundShape rd.valid
        (hSelected) first second hNe hFirst'
        hSecond' hValency'
  · exact stablePath_eq_of_consecutive
      (consecutive_retained_of_away rd.candidate rd.valid rd.genus_eq
        first second hNe vertex hAt hFirst hSecond hValency)

/-- **The occurrence-induced stable-row map of a member.**  It is
induced by retaining an actual surviving occurrence of the incoming datum, not
read off a path list. -/
noncomputable def stablePathLift :
    StablePath data → StablePath rd.candidate.datum :=
  Quot.lift (fun edge ↦ (retainedEdge rd.candidate rd.valid.1 edge).stablePath)
    (fun _ _ hConsecutive ↦
      rd.retained_stablePath_eq_of_consecutive _ _ hConsecutive)

@[simp] theorem stablePathLift_mk (edge : NonDanglingEdge data) :
    rd.stablePathLift edge.stablePath =
      (retainedEdge rd.candidate rd.valid.1 edge).stablePath := rfl


theorem replace_stablePath {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel rd.selected sheet)
    {edge : data.SourceEdge} (hSurvives : ¬ IsDangling data edge)
    (hIncident : Incident data edge (data.sourceEndpoint wall sheet))
    (hReplace : ¬ IsDangling rd.candidate.datum
      (Background.replace rd.toBackgroundShape edge)) :
    NonDanglingEdge.stablePath
        (⟨Background.replace rd.toBackgroundShape edge, hReplace⟩ :
          NonDanglingEdge rd.candidate.datum) =
      rd.stablePathLift
        (NonDanglingEdge.stablePath (⟨edge, hSurvives⟩ : NonDanglingEdge data)) := by
  exact Eq.trans (Background.retained_stablePath_eq_replace rd.toBackgroundShape rd.valid
      (hSheet) hSurvives hIncident hReplace).symm
    (rd.stablePathLift_mk ⟨edge, hSurvives⟩).symm


end LiftData


namespace SelectedData

variable (rd : SelectedData data wall)

/-- The member's retained occurrences survive. -/
theorem retainedRep_survives {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel rd.selected sheet) :
    ¬ IsDangling rd.candidate.datum
      (rd.candidate.oldSourceEdge (rd.selectedRep sheet)) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge rd.candidate rd.valid.1 _
    (rd.selectedRep_survives sheet hSheet)
/-! ### The old occurrence represented by a surviving new occurrence -/

/-- Above `A₀` the member's new occurrence represents `selectedRep`; away from
it, the background direction's own occurrence through the same sheet. -/
noncomputable def newOldSourceEdge (sheet : Fin degree) :
    data.SourceEdge :=
  if (data.vertexPartition wall).Rel rd.selected sheet then
    rd.selectedRep sheet
  else data.sourceEdge rd.retainedTarget sheet

theorem newOldSourceEdge_selected {sheet : Fin degree}
    (hSheet : (data.vertexPartition wall).Rel rd.selected sheet) :
    rd.newOldSourceEdge sheet = rd.selectedRep sheet := ite_eq_left hSheet

theorem newOldSourceEdge_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel rd.selected sheet) :
    rd.newOldSourceEdge sheet =
      data.sourceEdge rd.retainedTarget sheet := ite_eq_right hSheet

theorem newOldSourceEdge_survives (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet)) :
    ¬ IsDangling data (rd.newOldSourceEdge sheet) := by
  by_cases hSelected : (data.vertexPartition wall).Rel
      rd.selected sheet
  · rw [rd.newOldSourceEdge_selected hSelected]
    exact rd.selectedRep_survives sheet hSelected
  · rw [rd.newOldSourceEdge_background hSelected]
    intro hDangling
    exact hSurvives ((rd.new_isDangling_iff rd.valid
      (hSelected)).mpr hDangling)

/-- The surviving incoming occurrence a surviving new occurrence represents. -/
noncomputable def newOldEdge (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet)) : NonDanglingEdge data :=
  ⟨rd.newOldSourceEdge sheet, rd.newOldSourceEdge_survives sheet hSurvives⟩

/-- **Every surviving new occurrence lies in its representative's outgoing
row.** -/
theorem new_stablePath_eq_retained (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet)) :
    NonDanglingEdge.stablePath
        (⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge rd.candidate.datum) =
      (retainedEdge rd.candidate rd.valid.1
        (rd.newOldEdge sheet hSurvives)).stablePath := by
  by_cases hSelected : (data.vertexPartition wall).Rel
      rd.selected sheet
  · refine Eq.trans (rd.selected_new_stablePath sheet hSelected hSurvives
      (rd.retainedRep_survives hSelected)) ?_
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      (congrArg rd.candidate.oldSourceEdge
        (rd.newOldSourceEdge_selected hSelected).symm))
  · have hBackground := hSelected
    have hOldSurvives : ¬ IsDangling data
        (data.sourceEdge rd.retainedTarget sheet) := by
      rw [← rd.newOldSourceEdge_background hSelected]
      exact rd.newOldSourceEdge_survives sheet hSurvives
    refine Eq.trans (rd.new_stablePath_eq rd.valid hBackground hOldSurvives) ?_
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      (congrArg rd.candidate.oldSourceEdge
        (rd.newOldSourceEdge_background hSelected).symm))

/-! ### Surjectivity of the induced row map -/

/-- Every surviving occurrence of a member lies on the outgoing row
of an actual retained incoming survivor. -/
theorem exists_retained_row (edge : NonDanglingEdge rd.candidate.datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge rd.candidate rd.valid.1 old).stablePath =
        edge.stablePath := by
  rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq edge
    with ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · exact ⟨rd.newOldEdge sheet hSurvives,
      (rd.new_stablePath_eq_retained sheet hSurvives).symm⟩

theorem stablePathLift_surjective : Function.Surjective rd.stablePathLift := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := rd.exists_retained_row edge
      exact ⟨old.stablePath, hPath⟩


/-! ### The explicit reverse row assignment -/

/-- Two new occurrences that agree have the same representative. -/
theorem newOldSourceEdge_congr {first second : Fin degree}
    (hEq : rd.candidate.newSourceEdge first =
      rd.candidate.newSourceEdge second) :
    rd.newOldSourceEdge first = rd.newOldSourceEdge second := by
  have hRefines : (data.edgePartition rd.retainedTarget).Refines
      (data.vertexPartition wall) :=
    refines_of_mem_incidentEdges data rd.target_mem
  by_cases hFirst : (data.vertexPartition wall).Rel rd.selected first
  · by_cases hSecond : (data.vertexPartition wall).Rel
        rd.selected second
    · rw [rd.newOldSourceEdge_selected hFirst, rd.newOldSourceEdge_selected hSecond]
      exact rd.selectedRep_congr first second hFirst hSecond hEq
    · exfalso
      have hRel := (Background.newSourceEdge_eq_iff rd.toBackgroundShape
        (hSecond)).mp hEq.symm
      exact hSecond (hFirst.trans (hRefines.rel hRel).symm)
  · by_cases hSecond : (data.vertexPartition wall).Rel
        rd.selected second
    · exfalso
      have hRel := (Background.newSourceEdge_eq_iff rd.toBackgroundShape
        (hFirst)).mp hEq
      exact hFirst (hSecond.trans (hRefines.rel hRel).symm)
    · rw [rd.newOldSourceEdge_background hFirst,
        rd.newOldSourceEdge_background hSecond]
      exact (sourceEdge_eq_iff_rel data rd.retainedTarget first second).mpr
        ((Background.newSourceEdge_eq_iff rd.toBackgroundShape
          (hFirst)).mp hEq)

/-- A surviving occurrence that is not retained is an actual surviving new
occurrence. -/
theorem new_representation (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) :
    ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling rd.candidate.datum
        (rd.candidate.newSourceEdge sheet)),
      edge = ⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ := by
  rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq edge
    with ⟨old, hOld⟩ | ⟨sheet, hSurvives, hNew⟩
  · exact (hNotOld ⟨old, hOld.symm⟩).elim
  · exact ⟨sheet, hSurvives, hNew⟩

noncomputable def newSheet (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) : Fin degree :=
  (rd.new_representation edge hNotOld).choose

theorem newSheet_survives (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) :
    ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge (rd.newSheet edge hNotOld)) :=
  (rd.new_representation edge hNotOld).choose_spec.choose

theorem newSheet_spec (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) :
    edge = ⟨rd.candidate.newSourceEdge (rd.newSheet edge hNotOld),
      rd.newSheet_survives edge hNotOld⟩ :=
  (rd.new_representation edge hNotOld).choose_spec.choose_spec

/-- **The reverse row assignment.**  A retained occurrence returns to its own
incoming row; a surviving new occurrence returns to the row of the incoming
occurrence it represents. -/
noncomputable def rowOfEdge (edge : NonDanglingEdge rd.candidate.datum) :
    StablePath data := by
  classical
  exact if hOld : ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge then
    (Classical.choose hOld).stablePath
  else
    (rd.newOldEdge (rd.newSheet edge hOld) (rd.newSheet_survives edge hOld)).stablePath

@[simp] theorem rowOfEdge_retained (old : NonDanglingEdge data) :
    rd.rowOfEdge (retainedEdge rd.candidate rd.valid.1 old) =
      old.stablePath := by
  classical
  have hOld : ∃ other : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 other =
        retainedEdge rd.candidate rd.valid.1 old := ⟨old, rfl⟩
  rw [rowOfEdge, dite_eq_left hOld]
  exact congrArg NonDanglingEdge.stablePath
    (retainedEdge_injective rd.candidate rd.valid.1
      (Classical.choose_spec hOld))

theorem new_not_retained (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet)) :
    ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old =
        ⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ := by
  rintro ⟨old, hOld⟩
  exact rd.new_ne_old sheet old.1 (congrArg Subtype.val hOld).symm

theorem rowOfEdge_not_retained (edge : NonDanglingEdge rd.candidate.datum)
    (hNotOld : ¬ ∃ old : NonDanglingEdge data,
      retainedEdge rd.candidate rd.valid.1 old = edge) :
    rd.rowOfEdge edge =
      (rd.newOldEdge (rd.newSheet edge hNotOld)
        (rd.newSheet_survives edge hNotOld)).stablePath := by
  classical
  exact dite_eq_right hNotOld

theorem rowOfEdge_new (sheet : Fin degree)
    (hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet)) :
    rd.rowOfEdge ⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ =
      (rd.newOldEdge sheet hSurvives).stablePath := by
  classical
  have hNotOld := rd.new_not_retained sheet hSurvives
  refine Eq.trans (rd.rowOfEdge_not_retained _ hNotOld) ?_
  refine congrArg NonDanglingEdge.stablePath (Subtype.ext ?_)
  exact rd.newOldSourceEdge_congr
    (congrArg Subtype.val (rd.newSheet_spec _ hNotOld)).symm


/-! #### The reverse assignment at the two expanded endpoints -/

/-- At a selected endpoint of surviving valency two the reverse assignment is
constant: both occurrences return to the representative's row. -/
theorem rowOfEdge_eq_selected_pair {vertex : rd.candidate.datum.SourceVertex}
    {other : Fin degree}
    (hOther : (data.vertexPartition wall).Rel rd.selected other)
    (hStar : nonDanglingIncident rd.candidate.datum vertex =
      {rd.candidate.newSourceEdge other,
        rd.candidate.oldSourceEdge (rd.selectedRep other)})
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1 vertex)
    (hSecond : Incident rd.candidate.datum second.1 vertex) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  classical
  have key : ∀ edge : NonDanglingEdge rd.candidate.datum,
      Incident rd.candidate.datum edge.1 vertex →
      rd.rowOfEdge edge = NonDanglingEdge.stablePath
        (⟨rd.selectedRep other, rd.selectedRep_survives other hOther⟩ :
          NonDanglingEdge data) := by
    intro edge hIncident
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum vertex :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    rw [hStar] at hMem
    rcases Finset.mem_insert.mp hMem with hNew | hOld
    · have hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge other) := by
        rw [← hNew]; exact edge.2
      rw [show edge = ⟨rd.candidate.newSourceEdge other, hSurvives⟩ from
        Subtype.ext hNew, rd.rowOfEdge_new]
      exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (rd.newOldSourceEdge_selected hOther))
    · rw [Finset.mem_singleton] at hOld
      exact Eq.trans (congrArg rd.rowOfEdge
        (show edge = retainedEdge rd.candidate rd.valid.1
            ⟨rd.selectedRep other, rd.selectedRep_survives other hOther⟩ from
          Subtype.ext hOld)) (rd.rowOfEdge_retained _)
  rw [key first hFirst, key second hSecond]

/-- At a background divalent endpoint of surviving valency two both
occurrences return to the background direction's own row. -/
theorem rowOfEdge_eq_left_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel rd.selected sheet)
    (hValency : nonDanglingValency rd.candidate.datum
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet))
    (hSecond : Incident rd.candidate.datum second.1
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  classical
  have hBackground := hSheet
  have hStar := Background.nonDanglingIncident_old_background rd.toBackgroundShape hBackground
    hValency
  have hOldMem : rd.candidate.oldSourceEdge
      (data.sourceEdge rd.retainedTarget sheet) ∈
      nonDanglingIncident rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) := by
    rw [hStar]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hOldSurvives : ¬ IsDangling data
      (data.sourceEdge rd.retainedTarget sheet) := fun hDangling ↦
    ((mem_nonDanglingIncident _ _ _).mp hOldMem).1
      ((rd.old_isDangling_iff rd.valid _).mpr hDangling)
  have key : ∀ edge : NonDanglingEdge rd.candidate.datum,
      Incident rd.candidate.datum edge.1
        (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) →
      rd.rowOfEdge edge = NonDanglingEdge.stablePath
        (⟨data.sourceEdge rd.retainedTarget sheet, hOldSurvives⟩ :
          NonDanglingEdge data) := by
    intro edge hIncident
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    rw [hStar] at hMem
    rcases Finset.mem_insert.mp hMem with hNew | hOld
    · have hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge sheet) := by
        rw [← hNew]; exact edge.2
      rw [show edge = ⟨rd.candidate.newSourceEdge sheet, hSurvives⟩ from
        Subtype.ext hNew, rd.rowOfEdge_new]
      exact congrArg NonDanglingEdge.stablePath
        (Subtype.ext (rd.newOldSourceEdge_background hSheet))
    · rw [Finset.mem_singleton] at hOld
      exact Eq.trans (congrArg rd.rowOfEdge
        (show edge = retainedEdge rd.candidate rd.valid.1
            ⟨data.sourceEdge rd.retainedTarget sheet, hOldSurvives⟩ from
          Subtype.ext hOld)) (rd.rowOfEdge_retained _)
  rw [key first hFirst, key second hSecond]


/-- At a background trivalent endpoint of surviving valency two both
occurrences return to rows of incoming survivors at the same wall vertex,
which is itself divalent, so the two rows agree. -/
theorem rowOfEdge_eq_right_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel rd.selected sheet)
    (hValency : nonDanglingValency rd.candidate.datum
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet))
    (hSecond : Incident rd.candidate.datum second.1
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  classical
  have hBackground := hSheet
  have hStar := Background.nonDanglingIncident_fresh_eq_image rd.toBackgroundShape rd.valid
    hBackground
  have hIncoming : nonDanglingValency data (data.sourceEndpoint wall sheet) = 2 :=
    (Background.nonDanglingValency_fresh_eq rd.toBackgroundShape rd.valid hBackground).symm.trans
      hValency
  have key : ∀ edge : NonDanglingEdge rd.candidate.datum,
      Incident rd.candidate.datum edge.1
        (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) →
      ∃ old : NonDanglingEdge data,
        Incident data old.1 (data.sourceEndpoint wall sheet) ∧
          rd.rowOfEdge edge = old.stablePath := by
    intro edge hIncident
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    rw [hStar] at hMem
    obtain ⟨old, hOldMem, hReplace⟩ := Finset.mem_image.mp hMem
    obtain ⟨hOldSurvives, hOldIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOldMem
    refine ⟨⟨old, hOldSurvives⟩, hOldIncident, ?_⟩
    by_cases hTarget : old.1.1 = rd.retainedTarget
    · have hNew : edge.1 = rd.candidate.newSourceEdge old.1.2 :=
        hReplace.symm.trans (Background.replace_of_target rd.toBackgroundShape hTarget)
      have hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge old.1.2) := by
        rw [← hNew]; exact edge.2
      have hOldBackground : ¬ (data.vertexPartition wall).Rel
          rd.selected old.1.2 :=
        (Background.background_of_incident rd.toBackgroundShape hBackground hOldIncident)
      rw [show edge = ⟨rd.candidate.newSourceEdge old.1.2, hSurvives⟩ from
        Subtype.ext hNew, rd.rowOfEdge_new]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((rd.newOldSourceEdge_background hOldBackground).trans
          (rd.sourceEdge_retained_self hTarget)))
    · have hOldEq : edge.1 = rd.candidate.oldSourceEdge old :=
        hReplace.symm.trans (Background.replace_of_target_ne rd.toBackgroundShape hTarget)
      exact Eq.trans (congrArg rd.rowOfEdge
        (show edge = retainedEdge rd.candidate rd.valid.1 ⟨old, hOldSurvives⟩
          from Subtype.ext hOldEq)) (rd.rowOfEdge_retained _)
  obtain ⟨oldFirst, hOldFirst, hRowFirst⟩ := key first hFirst
  obtain ⟨oldSecond, hOldSecond, hRowSecond⟩ := key second hSecond
  rw [hRowFirst, hRowSecond]
  by_cases hEqual : oldFirst = oldSecond
  · rw [hEqual]
  · exact stablePath_eq_of_consecutive ⟨hEqual, data.sourceEndpoint wall sheet,
      hOldFirst, hOldSecond, hIncoming⟩


/-- The reverse assignment is constant at every divalent endpoint above the
wall. -/
theorem rowOfEdge_eq_left (sheet : Fin degree)
    (hValency : nonDanglingValency rd.candidate.datum
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet) = 2)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet))
    (hSecond : Incident rd.candidate.datum second.1
      (rd.candidate.datum.sourceEndpoint (oldVertex target wall) sheet)) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  by_cases hSelected : (data.vertexPartition wall).Rel rd.selected sheet
  · obtain ⟨other, hOther, hStar⟩ := rd.selected_left_pair sheet hSelected hValency
    exact rd.rowOfEdge_eq_selected_pair hOther hStar first second hFirst hSecond
  · exact rd.rowOfEdge_eq_left_background hSelected hValency first second hFirst
      hSecond

/-- The same at every trivalent endpoint above the wall. -/
theorem rowOfEdge_eq_right (sheet : Fin degree)
    (hValency : nonDanglingValency rd.candidate.datum
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) = 2)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet))
    (hSecond : Incident rd.candidate.datum second.1
      (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet)) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  by_cases hSelected : (data.vertexPartition wall).Rel rd.selected sheet
  · obtain ⟨other, hOther, hStar⟩ := rd.selected_right_pair sheet hSelected hValency
    exact rd.rowOfEdge_eq_selected_pair hOther hStar first second hFirst hSecond
  · exact rd.rowOfEdge_eq_right_background hSelected hValency first second hFirst
      hSecond

/-- Away from the expanded wall both survivors at a divalent vertex are
retained, and their incoming rows meet there. -/
theorem rowOfEdge_eq_away (vertex : data.SourceVertex) (hAway : vertex.1.1 ≠ wall)
    (first second : NonDanglingEdge rd.candidate.datum)
    (hFirst : Incident rd.candidate.datum first.1
      (retainedVertex rd.candidate vertex))
    (hSecond : Incident rd.candidate.datum second.1
      (retainedVertex rd.candidate vertex))
    (hValency : nonDanglingValency rd.candidate.datum
      (retainedVertex rd.candidate vertex) = 2) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  classical
  rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq first
    with ⟨oldFirst, rfl⟩ | ⟨sheetFirst, hFirstSurvives, rfl⟩
  · rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq
      second with ⟨oldSecond, rfl⟩ | ⟨sheetSecond, hSecondSurvives, rfl⟩
    · refine Eq.trans (rd.rowOfEdge_retained oldFirst)
        (Eq.trans ?_ (rd.rowOfEdge_retained oldSecond).symm)
      by_cases hEqual : oldFirst = oldSecond
      · exact congrArg NonDanglingEdge.stablePath hEqual
      · exact stablePath_eq_of_consecutive ⟨hEqual, vertex,
          (incident_oldSourceEdge_iff rd.candidate vertex hAway
            oldFirst.1).mp hFirst,
          (incident_oldSourceEdge_iff rd.candidate vertex hAway
            oldSecond.1).mp hSecond,
          (nonDanglingValency_retainedVertex rd.candidate rd.valid
            rd.genus_eq vertex hAway).symm.trans hValency⟩
    · exact (not_incident_newSourceEdge rd.candidate vertex hAway sheetSecond
        hSecond).elim
  · exact (not_incident_newSourceEdge rd.candidate vertex hAway sheetFirst
      hFirst).elim

/-- **The reverse assignment is constant on every actual consecutive pair of
the member.** -/
theorem rowOfEdge_eq_of_consecutive
    (first second : NonDanglingEdge rd.candidate.datum)
    (hConsecutive : Consecutive rd.candidate.datum first second) :
    rd.rowOfEdge first = rd.rowOfEdge second := by
  obtain ⟨_, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  have hSelf : rd.candidate.datum.sourceEndpoint vertex.1.1 vertex.1.2 =
      vertex :=
    (rd.candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : vertex.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : rd.candidate.datum.sourceEndpoint
            (oldVertex target wall) vertex.1.2 = vertex :=
          (congrArg (fun item ↦ rd.candidate.datum.sourceEndpoint item
            vertex.1.2) hTarget.symm).trans hSelf
        rw [← hEndpoint] at hFirst hSecond hValency
        exact rd.rowOfEdge_eq_left vertex.1.2 hValency first second hFirst hSecond
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target
          rd.candidate vertex place hAt hTarget
        rw [← hVertex] at hFirst hSecond hValency
        exact rd.rowOfEdge_eq_away old (hOld ▸ hAt) first second hFirst hSecond
          hValency
  | inr point =>
      cases point
      have hEndpoint : rd.candidate.datum.sourceEndpoint
          (freshVertex target) vertex.1.2 = vertex :=
        (congrArg (fun item ↦ rd.candidate.datum.sourceEndpoint item
          vertex.1.2) hTarget.symm).trans hSelf
      rw [← hEndpoint] at hFirst hSecond hValency
      exact rd.rowOfEdge_eq_right vertex.1.2 hValency first second hFirst hSecond


/-! ### The occurrence-induced stable-row equivalence -/

/-- The reverse row assignment descends through the member's stable
quotient. -/
noncomputable def stablePathDescend :
    StablePath rd.candidate.datum → StablePath data :=
  Quot.lift rd.rowOfEdge rd.rowOfEdge_eq_of_consecutive

@[simp] theorem stablePathDescend_mk
    (edge : NonDanglingEdge rd.candidate.datum) :
    rd.stablePathDescend edge.stablePath = rd.rowOfEdge edge := rfl

/-- Descent is a literal left inverse of the retained-occurrence lift. -/
theorem stablePathDescend_lift (path : StablePath data) :
    rd.stablePathDescend (rd.stablePathLift path) = path := by
  induction path using Quot.inductionOn with
  | h edge => exact rd.rowOfEdge_retained edge

theorem stablePathLift_injective : Function.Injective rd.stablePathLift :=
  Function.LeftInverse.injective rd.stablePathDescend_lift

/-- **The occurrence-induced stable-row equivalence of a member.**
It is the retained-occurrence map of the incoming stable source, with an
explicit geometric left inverse; no cardinality argument is used. -/
noncomputable def stablePathEquiv :
    StablePath data ≃ StablePath rd.candidate.datum :=
  Equiv.ofBijective rd.stablePathLift
    ⟨rd.stablePathLift_injective, rd.stablePathLift_surjective⟩

@[simp] theorem stablePathEquiv_mk (edge : NonDanglingEdge data) :
    rd.stablePathEquiv edge.stablePath =
      (retainedEdge rd.candidate rd.valid.1 edge).stablePath := rfl

/-- The inverse of the row equivalence is the explicit reverse assignment. -/
@[simp] theorem stablePathEquiv_symm_apply
    (path : StablePath rd.candidate.datum) :
    rd.stablePathEquiv.symm path = rd.stablePathDescend path := by
  obtain ⟨row, hRow⟩ := rd.stablePathLift_surjective path
  rw [← hRow, rd.stablePathDescend_lift]
  exact rd.stablePathEquiv.symm_apply_apply row

/-! ### The honest natural stable-length matrix: the retained columns

This is the limit-matrix lemma of Draisma--Vargas Part I
(`lemma-limit-matrix-change`), in the up direction and without a
compatible-labelling hypothesis.  The regrown column
is evaluated in §5. -/

theorem occurrences_retained (path : StablePath data) (place : target.edges) :
    occurrences rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right (some place)) =
      (occurrences data path place).image rd.candidate.oldSourceEdge := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases rd.candidate edge with
      ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hOld : ¬ IsDangling data old := fun hDangling ↦ hSurvives
        ((rd.old_isDangling_iff rd.valid old).mpr hDangling)
      refine Finset.mem_image.mpr ⟨old, (mem_occurrences _ _ _).mpr
        ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
      · exact rd.stablePathEquiv.injective
          ((rd.stablePathEquiv_mk ⟨old, hOld⟩).trans hRow)
      · exact Option.some.inj ((occurrenceEquiv target wall
          rd.candidate.right).injective hTarget)
    · have hLabels := (occurrenceEquiv target wall
        rd.candidate.right).injective hTarget
      cases hLabels
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine (mem_occurrences _ _ _).mpr
      ⟨⟨ResolutionSurvival.not_isDangling_oldSourceEdge rd.candidate
        rd.valid.1 old hSurvives, ?_⟩, ?_⟩
    · exact (rd.stablePathEquiv_mk ⟨old, hSurvives⟩).symm.trans
        (congrArg rd.stablePathEquiv hRow)
    · exact congrArg (fun label ↦ occurrenceEquiv target wall
        rd.candidate.right (some label)) hTarget

/-- **Every retained column of a member is the incoming wall
column.**  Indices are preserved literally by retention, and the row map is the
proved occurrence-induced equivalence. -/
theorem matrix_retained (path : StablePath data) (place : target.edges) :
    matrix rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right (some place)) =
      matrix data path place := by
  classical
  unfold matrix
  rw [rd.occurrences_retained, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by
      rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]
  · intro first _ second _ hEqual
    exact ResolutionCut.oldSourceEdge_injective _ hEqual

/-- The regrown column is supported on the surviving new occurrences, and each
of them sits on the outgoing row of the incoming occurrence it represents.
This pins the support the regrown half still has to evaluate; it does not
evaluate it. -/
theorem mem_occurrences_new_iff (path : StablePath data)
    (edge : rd.candidate.datum.SourceEdge) :
    edge ∈ occurrences rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) ↔
      ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge sheet)),
        edge = rd.candidate.newSourceEdge sheet ∧
          (rd.newOldEdge sheet hSurvives).stablePath = path := by
  classical
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    rcases ResolutionPruning.sourceEdge_cases rd.candidate edge with
      ⟨old, rfl⟩ | ⟨sheet, rfl⟩
    · have hLabels := (occurrenceEquiv target wall
        rd.candidate.right).injective hTarget
      exact absurd hLabels (by simp)
    · refine ⟨sheet, hSurvives, rfl, rd.stablePathEquiv.injective ?_⟩
      rw [rd.stablePathEquiv_mk]
      exact (rd.new_stablePath_eq_retained sheet hSurvives).symm.trans hRow
  · rintro ⟨sheet, hSurvives, rfl, hRow⟩
    refine ⟨⟨hSurvives, ?_⟩, rfl⟩
    rw [← hRow, rd.stablePathEquiv_mk]
    exact rd.new_stablePath_eq_retained sheet hSurvives


/-! ### Incidence counts away from the distinguished block -/

/-- **Away from the wall retention preserves every incidence count.** -/
theorem incidenceCount_retained (vertex : data.SourceVertex)
    (hAway : vertex.1.1 ≠ wall) (path : StablePath data) :
    incidenceCount data vertex path =
      incidenceCount rd.candidate.datum
        (retainedVertex rd.candidate vertex) (rd.stablePathLift path) := by
  classical
  refine Finset.card_bij
    (fun edge _ ↦ retainedEdge rd.candidate rd.valid.1 edge) ?_ ?_ ?_
  · intro edge hEdge
    rw [Finset.mem_filter, mem_incidentEdges] at hEdge ⊢
    exact ⟨(incident_oldSourceEdge_iff rd.candidate vertex hAway
        edge.1).mpr hEdge.1,
      (rd.stablePathLift_mk edge).symm.trans
        (congrArg rd.stablePathLift hEdge.2)⟩
  · intro first _ second _ hEqual
    exact retainedEdge_injective rd.candidate rd.valid.1 hEqual
  · intro edge hEdge
    rw [Finset.mem_filter, mem_incidentEdges] at hEdge
    rcases nonDanglingEdge_cases rd.candidate rd.valid rd.genus_eq edge
      with ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
    · refine ⟨old, ?_, rfl⟩
      rw [Finset.mem_filter, mem_incidentEdges]
      refine ⟨(incident_oldSourceEdge_iff rd.candidate vertex hAway
        old.1).mp hEdge.1, ?_⟩
      exact rd.stablePathLift_injective
        ((rd.stablePathLift_mk old).trans hEdge.2)
    · exact absurd hEdge.1 (not_incident_newSourceEdge rd.candidate vertex
        hAway sheet)

/-- **At a background wall vertex the replacement bijection preserves every
incidence count.** -/
theorem incidenceCount_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel rd.selected sheet)
    (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall sheet) path =
      incidenceCount rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet)
        (rd.stablePathLift path) := by
  classical
  have hBackground := hSheet
  refine Finset.card_bij
    (fun edge hEdge ↦ (⟨Background.replace rd.toBackgroundShape edge.1,
      Background.replace_survives rd.toBackgroundShape rd.valid hBackground edge.2
        ((mem_incidentEdges data _ edge).mp
          (Finset.mem_filter.mp hEdge).1)⟩ :
      NonDanglingEdge rd.candidate.datum)) ?_ ?_ ?_
  · intro edge hEdge
    have hIncident := (mem_incidentEdges data _ edge).mp
      (Finset.mem_filter.mp hEdge).1
    exact Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr
        (Background.replace_incident rd.toBackgroundShape hBackground hIncident),
      (rd.replace_stablePath hSheet edge.2 hIncident _).trans
        (congrArg rd.stablePathLift (Finset.mem_filter.mp hEdge).2)⟩
  · intro first hFirst second hSecond hEqual
    have hFirstMem : first.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨first.2,
        (mem_incidentEdges data _ first).mp (Finset.mem_filter.mp hFirst).1⟩
    have hSecondMem : second.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨second.2,
        (mem_incidentEdges data _ second).mp (Finset.mem_filter.mp hSecond).1⟩
    exact Subtype.ext (Background.replace_injOn rd.toBackgroundShape hBackground
      (Finset.mem_coe.mpr hFirstMem) (Finset.mem_coe.mpr hSecondMem)
      (congrArg Subtype.val hEqual))
  · intro edge hEdge
    have hIncident := (mem_incidentEdges _ _ edge).mp
      (Finset.mem_filter.mp hEdge).1
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum
        (rd.candidate.datum.sourceEndpoint (freshVertex target) sheet) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    rw [Background.nonDanglingIncident_fresh_eq_image rd.toBackgroundShape rd.valid
      hBackground] at hMem
    obtain ⟨old, hOldMem, hReplace⟩ := Finset.mem_image.mp hMem
    obtain ⟨hOldSurvives, hOldIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOldMem
    refine ⟨⟨old, hOldSurvives⟩, ?_, Subtype.ext hReplace⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hOldIncident,
      rd.stablePathLift_injective ?_⟩
    refine Eq.trans (rd.replace_stablePath hSheet hOldSurvives hOldIncident
      (Background.replace_survives rd.toBackgroundShape rd.valid hBackground hOldSurvives
        hOldIncident)).symm ?_
    exact Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext hReplace : (⟨Background.replace rd.toBackgroundShape old,
        Background.replace_survives rd.toBackgroundShape rd.valid hBackground hOldSurvives
          hOldIncident⟩ :
        NonDanglingEdge rd.candidate.datum) = edge))
      (Finset.mem_filter.mp hEdge).2

end SelectedData


namespace GraphData

variable (rd : GraphData data wall)

/-- The member's branch vertex above the distinguished block. -/
noncomputable def branchVertex : rd.candidate.datum.SourceVertex :=
  rd.candidate.datum.sourceEndpoint (wallSide target wall rd.selectedSide)
    rd.selected

theorem branchVertex_star :
    nonDanglingIncident rd.candidate.datum rd.branchVertex =
      (nonDanglingIncident data
        (data.sourceEndpoint wall rd.selected)).image rd.selectedFlag :=
  rd.selectedFlag_star


theorem selectedFlag_survives {edge : data.SourceEdge}
    (hMem : edge ∈ nonDanglingIncident data
      (data.sourceEndpoint wall rd.selected)) :
    ¬ IsDangling rd.candidate.datum (rd.selectedFlag edge) := by
  have hImage : rd.selectedFlag edge ∈
      nonDanglingIncident rd.candidate.datum rd.branchVertex := by
    rw [rd.branchVertex_star]
    exact Finset.mem_image_of_mem _ hMem
  exact ((mem_nonDanglingIncident _ _ _).mp hImage).1

theorem selectedFlag_incident {edge : data.SourceEdge}
    (hMem : edge ∈ nonDanglingIncident data
      (data.sourceEndpoint wall rd.selected)) :
    Incident rd.candidate.datum (rd.selectedFlag edge) rd.branchVertex := by
  have hImage : rd.selectedFlag edge ∈
      nonDanglingIncident rd.candidate.datum rd.branchVertex := by
    rw [rd.branchVertex_star]
    exact Finset.mem_image_of_mem _ hMem
  exact ((mem_nonDanglingIncident _ _ _).mp hImage).2

/-- **At the distinguished wall vertex the branch flag preserves every
incidence count.**  Occurrences are counted with multiplicity, so a stable loop
through the branch vertex contributes twice on both sides. -/
theorem incidenceCount_selected (path : StablePath data) :
    incidenceCount data (data.sourceEndpoint wall rd.selected) path =
      incidenceCount rd.candidate.datum rd.branchVertex
        (rd.stablePathLift path) := by
  classical
  refine Finset.card_bij (fun edge hEdge ↦ (⟨rd.selectedFlag edge.1,
    rd.selectedFlag_survives ((mem_nonDanglingIncident _ _ _).mpr ⟨edge.2,
      (mem_incidentEdges data _ edge).mp (Finset.mem_filter.mp hEdge).1⟩)⟩ :
    NonDanglingEdge rd.candidate.datum)) ?_ ?_ ?_
  · intro edge hEdge
    have hIncident := (mem_incidentEdges data _ edge).mp
      (Finset.mem_filter.mp hEdge).1
    have hMem : edge.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall rd.selected) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2, hIncident⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_incidentEdges _ _ _).mpr (rd.selectedFlag_incident hMem),
        (rd.selectedFlag_row edge.1 edge.2 hIncident _).trans
          ((rd.stablePathLift_mk edge).symm.trans
            (congrArg rd.stablePathLift (Finset.mem_filter.mp hEdge).2))⟩
  · intro first hFirst second hSecond hEqual
    have hFirstMem : first.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall rd.selected) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨first.2,
        (mem_incidentEdges data _ first).mp (Finset.mem_filter.mp hFirst).1⟩
    have hSecondMem : second.1 ∈ nonDanglingIncident data
        (data.sourceEndpoint wall rd.selected) :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨second.2,
        (mem_incidentEdges data _ second).mp (Finset.mem_filter.mp hSecond).1⟩
    exact Subtype.ext (rd.selectedFlag_injOn (Finset.mem_coe.mpr hFirstMem)
      (Finset.mem_coe.mpr hSecondMem) (congrArg Subtype.val hEqual))
  · intro edge hEdge
    have hMem : edge.1 ∈ nonDanglingIncident rd.candidate.datum
        rd.branchVertex :=
      (mem_nonDanglingIncident _ _ _).mpr ⟨edge.2,
        (mem_incidentEdges _ _ edge).mp (Finset.mem_filter.mp hEdge).1⟩
    rw [rd.branchVertex_star] at hMem
    obtain ⟨old, hOldMem, hFlag⟩ := Finset.mem_image.mp hMem
    obtain ⟨hOldSurvives, hOldIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOldMem
    refine ⟨⟨old, hOldSurvives⟩, ?_, Subtype.ext hFlag⟩
    refine Finset.mem_filter.mpr ⟨(mem_incidentEdges _ _ _).mpr hOldIncident,
      rd.stablePathLift_injective ?_⟩
    refine Eq.trans (rd.stablePathLift_mk ⟨old, hOldSurvives⟩) ?_
    refine Eq.trans (rd.selectedFlag_row old hOldSurvives hOldIncident
      (rd.selectedFlag_survives hOldMem)).symm ?_
    exact Eq.trans (congrArg NonDanglingEdge.stablePath
      (Subtype.ext hFlag : (⟨rd.selectedFlag old,
        rd.selectedFlag_survives hOldMem⟩ :
        NonDanglingEdge rd.candidate.datum) = edge))
      (Finset.mem_filter.mp hEdge).2


end GraphData

/-! ### The branch-vertex correspondence and the stable incidence graph

Surviving branch vertices correspond: away from the wall by retention, above a
background wall block by the trivalent endpoint, and above the distinguished
block by the member's own branch vertex.  Every other expanded endpoint is
divalent or entirely pruned, which is what `selected_not_branch` and the
background subset bound say. -/

namespace GraphData

variable (rd : GraphData data wall)

/-- The member vertex a source vertex becomes. -/
noncomputable def branchImage (vertex : data.SourceVertex) :
    rd.candidate.datum.SourceVertex := by
  classical
  exact if vertex.1.1 = wall then
      (if (data.vertexPartition wall).Rel rd.selected vertex.1.2 then
        rd.branchVertex
      else rd.candidate.datum.sourceEndpoint (freshVertex target) vertex.1.2)
    else retainedVertex rd.candidate vertex

theorem branchImage_away {vertex : data.SourceVertex} (hAway : vertex.1.1 ≠ wall) :
    rd.branchImage vertex = retainedVertex rd.candidate vertex := by
  classical
  exact ite_eq_right hAway

theorem branchImage_selected {vertex : data.SourceVertex} (hAt : vertex.1.1 = wall)
    (hSelected : (data.vertexPartition wall).Rel rd.selected
      vertex.1.2) :
    rd.branchImage vertex = rd.branchVertex := by
  classical
  exact (ite_eq_left hAt).trans (ite_eq_left hSelected)

theorem branchImage_background {vertex : data.SourceVertex}
    (hAt : vertex.1.1 = wall)
    (hBackground : ¬ (data.vertexPartition wall).Rel rd.selected
      vertex.1.2) :
    rd.branchImage vertex =
      rd.candidate.datum.sourceEndpoint (freshVertex target) vertex.1.2 := by
  classical
  exact (ite_eq_left hAt).trans (ite_eq_right hBackground)

/-- The member's branch vertex has the incoming distinguished valency. -/
theorem nonDanglingValency_branchVertex :
    nonDanglingValency rd.candidate.datum rd.branchVertex =
      nonDanglingValency data
        (data.sourceEndpoint wall rd.selected) := by
  classical
  rw [← card_nonDanglingIncident, ← card_nonDanglingIncident, rd.branchVertex_star,
    Finset.card_image_of_injOn rd.selectedFlag_injOn]

/-- **Surviving valency is preserved.** -/
theorem nonDanglingValency_branchImage (vertex : data.SourceVertex) :
    nonDanglingValency rd.candidate.datum (rd.branchImage vertex) =
      nonDanglingValency data vertex := by
  classical
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSelected : (data.vertexPartition wall).Rel rd.selected
        vertex.1.2
    · have hAnchor : data.sourceEndpoint wall rd.selected = vertex :=
        (sourceEndpoint_eq_of_rel data wall hSelected).trans hVertex
      exact Eq.trans (congrArg (nonDanglingValency rd.candidate.datum)
          (rd.branchImage_selected hAt hSelected))
        (rd.nonDanglingValency_branchVertex.trans
          (congrArg (nonDanglingValency data) hAnchor))
    · exact Eq.trans (congrArg (nonDanglingValency rd.candidate.datum)
          (rd.branchImage_background hAt hSelected))
        ((Background.nonDanglingValency_fresh_eq rd.toBackgroundShape rd.valid
          (hSelected)).trans
          (congrArg (nonDanglingValency data) hVertex))
  · exact Eq.trans (congrArg (nonDanglingValency rd.candidate.datum)
      (rd.branchImage_away hAt))
      (nonDanglingValency_retainedVertex rd.candidate rd.valid
        rd.genus_eq vertex hAt)

/-- **Every incidence count is preserved.** -/
theorem incidenceCount_branchImage (vertex : data.SourceVertex)
    (path : StablePath data) :
    incidenceCount data vertex path =
      incidenceCount rd.candidate.datum (rd.branchImage vertex)
        (rd.stablePathLift path) := by
  classical
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    by_cases hSelected : (data.vertexPartition wall).Rel rd.selected
        vertex.1.2
    · have hAnchor : data.sourceEndpoint wall rd.selected = vertex :=
        (sourceEndpoint_eq_of_rel data wall hSelected).trans hVertex
      refine Eq.trans ?_ (congrArg (fun item ↦ incidenceCount
        rd.candidate.datum item (rd.stablePathLift path))
        (rd.branchImage_selected hAt hSelected)).symm
      exact (congrArg (fun item ↦ incidenceCount data item path) hAnchor).symm.trans
        (rd.incidenceCount_selected path)
    · refine Eq.trans ?_ (congrArg (fun item ↦ incidenceCount
        rd.candidate.datum item (rd.stablePathLift path))
        (rd.branchImage_background hAt hSelected)).symm
      exact (congrArg (fun item ↦ incidenceCount data item path) hVertex).symm.trans
        (rd.incidenceCount_background hSelected path)
  · refine Eq.trans ?_ (congrArg (fun item ↦ incidenceCount
      rd.candidate.datum item (rd.stablePathLift path))
      (rd.branchImage_away hAt)).symm
    exact rd.incidenceCount_retained vertex hAt path

/-! #### The branch map is a bijection -/

theorem branchVertex_target :
    (rd.branchVertex).1.1 = wallSide target wall rd.selectedSide := rfl

theorem branchVertex_ne_background {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel rd.selected sheet) :
    rd.candidate.datum.sourceEndpoint (freshVertex target) sheet ≠
      rd.branchVertex := by
  intro hEqual
  cases hSide : rd.selectedSide with
  | false =>
      have hTarget : freshVertex target = wallSide target wall rd.selectedSide :=
        congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.1)
          hEqual
      rw [hSide] at hTarget
      simp only [wallSide_false, freshVertex, oldVertex] at hTarget
      exact absurd hTarget (by simp)
  | true =>
      have hBranch : rd.branchVertex = rd.candidate.datum.sourceEndpoint
          (wallSide target wall rd.selectedSide) rd.selected := rfl
      rw [hSide, wallSide_true] at hBranch
      have hRel : rd.pasted.right.Rel sheet rd.selected :=
        congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.2)
          (hEqual.trans hBranch)
      have hMem : rd.selected ∈ rd.pasted.right.block sheet :=
        (rd.pasted.right.mem_block_iff _ _).mpr hRel
      rw [rd.pasted_right_block
        (hSheet)] at hMem
      exact hSheet ((((data.vertexPartition wall).mem_block_iff _ _).mp hMem).symm)

theorem branchVertex_ne_retained {vertex : data.SourceVertex}
    (hAway : vertex.1.1 ≠ wall) :
    retainedVertex rd.candidate vertex ≠ rd.branchVertex := by
  intro hEqual
  have hTarget : oldVertex target vertex.1.1 =
      wallSide target wall rd.selectedSide :=
    congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.1) hEqual
  cases hSide : rd.selectedSide with
  | false =>
      rw [hSide] at hTarget
      simp only [wallSide_false, oldVertex] at hTarget
      exact hAway (by simpa using hTarget)
  | true =>
      rw [hSide] at hTarget
      simp only [wallSide_true, oldVertex, freshVertex] at hTarget
      exact absurd hTarget (by simp)

theorem retained_ne_fresh {vertex : data.SourceVertex} (sheet : Fin degree) :
    retainedVertex rd.candidate vertex ≠
      rd.candidate.datum.sourceEndpoint (freshVertex target) sheet := by
  intro hEqual
  have hTarget : oldVertex target vertex.1.1 = freshVertex target :=
    congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.1) hEqual
  simp only [oldVertex, freshVertex] at hTarget
  exact absurd hTarget (by simp)

theorem branchImage_injective : Function.Injective rd.branchImage := by
  classical
  intro first second hEqual
  by_cases hFirstAt : first.1.1 = wall
  · by_cases hSecondAt : second.1.1 = wall
    · have hFirstRepr : (data.vertexPartition wall).repr first.1.2 = first.1.2 := by
        have := first.2
        rw [hFirstAt] at this
        exact this
      have hSecondRepr : (data.vertexPartition wall).repr second.1.2 =
          second.1.2 := by
        have := second.2
        rw [hSecondAt] at this
        exact this
      by_cases hFirstSel : (data.vertexPartition wall).Rel rd.selected
          first.1.2
      · by_cases hSecondSel : (data.vertexPartition wall).Rel
            rd.selected second.1.2
        · refine Subtype.ext (Prod.ext (hFirstAt.trans hSecondAt.symm) ?_)
          exact hFirstRepr.symm.trans (hFirstSel.symm.trans hSecondSel |>.trans
            hSecondRepr)
        · exact absurd ((rd.branchImage_background hSecondAt hSecondSel).symm.trans
            ((hEqual.symm).trans (rd.branchImage_selected hFirstAt hFirstSel)))
            (rd.branchVertex_ne_background hSecondSel)
      · by_cases hSecondSel : (data.vertexPartition wall).Rel
            rd.selected second.1.2
        · exact absurd ((rd.branchImage_background hFirstAt hFirstSel).symm.trans
            (hEqual.trans (rd.branchImage_selected hSecondAt hSecondSel)))
            (rd.branchVertex_ne_background hFirstSel)
        · have hFresh := (rd.branchImage_background hFirstAt hFirstSel).symm.trans
            (hEqual.trans (rd.branchImage_background hSecondAt hSecondSel))
          have hRel : rd.pasted.right.Rel first.1.2 second.1.2 :=
            congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.2)
              hFresh
          have hMem : second.1.2 ∈ rd.pasted.right.block first.1.2 :=
            (rd.pasted.right.mem_block_iff _ _).mpr hRel
          rw [rd.pasted_right_block
            (hFirstSel)] at hMem
          have hWall := ((data.vertexPartition wall).mem_block_iff _ _).mp hMem
          refine Subtype.ext (Prod.ext (hFirstAt.trans hSecondAt.symm) ?_)
          exact hFirstRepr.symm.trans (hWall.trans hSecondRepr)
    · by_cases hFirstSel : (data.vertexPartition wall).Rel rd.selected
          first.1.2
      · exact absurd ((rd.branchImage_away hSecondAt).symm.trans
          (hEqual.symm.trans (rd.branchImage_selected hFirstAt hFirstSel)))
          (rd.branchVertex_ne_retained hSecondAt)
      · exact absurd ((rd.branchImage_away hSecondAt).symm.trans
          (hEqual.symm.trans (rd.branchImage_background hFirstAt hFirstSel)))
          (rd.retained_ne_fresh first.1.2)
  · by_cases hSecondAt : second.1.1 = wall
    · by_cases hSecondSel : (data.vertexPartition wall).Rel rd.selected
          second.1.2
      · exact absurd ((rd.branchImage_away hFirstAt).symm.trans
          (hEqual.trans (rd.branchImage_selected hSecondAt hSecondSel)))
          (rd.branchVertex_ne_retained hFirstAt)
      · exact absurd ((rd.branchImage_away hFirstAt).symm.trans
          (hEqual.trans (rd.branchImage_background hSecondAt hSecondSel)))
          (rd.retained_ne_fresh second.1.2)
    · have hRetained := (rd.branchImage_away hFirstAt).symm.trans
        (hEqual.trans (rd.branchImage_away hSecondAt))
      have hTarget : oldVertex target first.1.1 = oldVertex target second.1.1 :=
        congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.1)
          hRetained
      have hPlace : first.1.1 = second.1.1 := by
        simpa only [oldVertex, Sum.inl.injEq] using hTarget
      have hSheet : first.1.2 = second.1.2 := by
        have hFirstSheet := retainedVertex_sheet rd.candidate first hFirstAt
        have hSecondSheet := retainedVertex_sheet rd.candidate second hSecondAt
        exact hFirstSheet.symm.trans
          ((congrArg (fun item : rd.candidate.datum.SourceVertex ↦ item.1.2)
            hRetained).trans hSecondSheet)
      exact Subtype.ext (Prod.ext hPlace hSheet)


/-- **Every surviving branch vertex of the member is hit.**  Above a background
wall block only the trivalent endpoint can be a branch, and above the
distinguished block only the member's own branch vertex. -/
theorem exists_branchImage (w : rd.candidate.datum.SourceVertex)
    (hBranch : 3 ≤ nonDanglingValency rd.candidate.datum w) :
    ∃ vertex : data.SourceVertex, rd.branchImage vertex = w := by
  classical
  have hSelf : rd.candidate.datum.sourceEndpoint w.1.1 w.1.2 = w :=
    (rd.candidate.datum.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, rfl⟩
  cases hTarget : w.1.1 with
  | inl place =>
      by_cases hAt : place = wall
      · subst place
        have hEndpoint : rd.candidate.datum.sourceEndpoint
            (oldVertex target wall) w.1.2 = w :=
          (congrArg (fun item ↦ rd.candidate.datum.sourceEndpoint item
            w.1.2) hTarget.symm).trans hSelf
        by_cases hSel : (data.vertexPartition wall).Rel rd.selected
            w.1.2
        · by_cases hIsBranch : rd.candidate.datum.sourceEndpoint
              (wallSide target wall false) w.1.2 = rd.branchVertex
          · refine ⟨data.sourceEndpoint wall rd.selected, ?_⟩
            refine (rd.branchImage_selected rfl
              ((data.vertexPartition wall).rel_repr_right _)).trans ?_
            simp only [wallSide_false] at hIsBranch
            exact hIsBranch.symm.trans hEndpoint
          · exfalso
            have hLe := rd.selected_not_branch false w.1.2 hSel hIsBranch
            simp only [wallSide_false] at hLe
            rw [hEndpoint] at hLe
            omega
        · exfalso
          have hLe : nonDanglingValency rd.candidate.datum
              (rd.candidate.datum.sourceEndpoint (oldVertex target wall)
                w.1.2) ≤ 2 := by
            rw [← card_nonDanglingIncident]
            exact (Finset.card_le_card (rd.nonDanglingIncident_old_subset
              (hSel))).trans
              (le_of_eq (Finset.card_pair (rd.new_ne_old _ _)))
          rw [hEndpoint] at hLe
          omega
      · obtain ⟨old, hOld, hVertex⟩ := exists_retainedVertex_of_target
          rd.candidate w place hAt hTarget
        exact ⟨old, (rd.branchImage_away (hOld ▸ hAt)).trans hVertex⟩
  | inr point =>
      cases point
      have hEndpoint : rd.candidate.datum.sourceEndpoint
          (freshVertex target) w.1.2 = w :=
        (congrArg (fun item ↦ rd.candidate.datum.sourceEndpoint item
          w.1.2) hTarget.symm).trans hSelf
      by_cases hSel : (data.vertexPartition wall).Rel rd.selected w.1.2
      · by_cases hIsBranch : rd.candidate.datum.sourceEndpoint
            (wallSide target wall true) w.1.2 = rd.branchVertex
        · refine ⟨data.sourceEndpoint wall rd.selected, ?_⟩
          refine (rd.branchImage_selected rfl
            ((data.vertexPartition wall).rel_repr_right _)).trans ?_
          simp only [wallSide_true] at hIsBranch
          exact hIsBranch.symm.trans hEndpoint
        · exfalso
          have hLe := rd.selected_not_branch true w.1.2 hSel hIsBranch
          simp only [wallSide_true] at hLe
          rw [hEndpoint] at hLe
          omega
      · refine ⟨data.sourceEndpoint wall w.1.2, ?_⟩
        have hBg : ¬ (data.vertexPartition wall).Rel rd.selected
            ((data.vertexPartition wall).repr w.1.2) := fun hRel ↦
          hSel (hRel.trans ((data.vertexPartition wall).rel_repr_left w.1.2))
        refine (rd.branchImage_background rfl hBg).trans ?_
        exact (Background.fresh_endpoint_eq rd.toBackgroundShape
          (hBg)
          ((data.vertexPartition wall).rel_repr_left w.1.2)).trans hEndpoint

/-- **The bijection of surviving branch vertices.** -/
noncomputable def branchVertexEquiv :
    StableGraphIncidence.BranchVertex data ≃
      StableGraphIncidence.BranchVertex rd.candidate.datum :=
  Equiv.ofBijective
    (fun vertex ↦ (⟨rd.branchImage vertex.1, by
      rw [rd.nonDanglingValency_branchImage]
      exact vertex.2⟩ :
      StableGraphIncidence.BranchVertex rd.candidate.datum))
    ⟨by
      intro first second hEqual
      exact Subtype.ext (rd.branchImage_injective (congrArg Subtype.val hEqual)),
      by
      intro w
      obtain ⟨vertex, hVertex⟩ := rd.exists_branchImage w.1 w.2
      refine ⟨⟨vertex, ?_⟩, Subtype.ext hVertex⟩
      rw [← rd.nonDanglingValency_branchImage vertex, hVertex]
      exact w.2⟩

@[simp] theorem branchVertexEquiv_apply
    (vertex : StableGraphIncidence.BranchVertex data) :
    (rd.branchVertexEquiv vertex).1 = rd.branchImage vertex.1 := rfl

/-- **The stable incidence graph of the member is the incoming one.**
A bijection of surviving branch vertices together with the occurrence-induced
row equivalence, preserving `incidenceCount` at every branch/row pair.  Nothing
here asserts distinctness of rows: a stable loop is counted twice on both
sides. -/
noncomputable def equivalence :
    StableGraphIncidence.Equivalence data rd.candidate.datum where
  vertex := rd.branchVertexEquiv
  row := rd.stablePathEquiv
  incidence := fun vertex path ↦ rd.incidenceCount_branchImage vertex.1 path

@[simp] theorem equivalence_row (path : StablePath data) :
    rd.equivalence.row path = rd.stablePathEquiv path := rfl

/-- Path ends transport, since the incoming source is connected. -/
theorem hasPathEnds (hEnds : HasPathEnds data) :
    HasPathEnds rd.candidate.datum :=
  rd.equivalence.hasPathEnds rd.valid.1 hEnds

end GraphData

/-! ## §5  The regrown column

`SelectedData.mem_occurrences_new_iff` pins the support of the regrown column
and the row of each occurrence in it.  Turning that into a *value* needs a
description of that support: as a list of sheets whose regrown occurrences
exhaust it (`matrix_new`, where the honesty condition is `Nodup` **after**
`newSourceEdge`, since distinct sheets may carry one regrown occurrence), or
as a `Finset`, where duplicates collapse on their own
(`occurrences_new_eq`, `matrix_new_split`).  `Gauge` is the isomorphism of the
stable source a length matrix cannot see, for members built on a relabelled
copy of the incoming datum. -/

namespace SelectedData

variable (rd : SelectedData data wall)

/-- The sheets a member regrows onto one stable row: those whose new
occurrence survives and represents an incoming survivor of that row. -/
def RegrownAt (path : StablePath data)
    (sheet : Fin degree) : Prop :=
  ∃ hSurvives : ¬ IsDangling rd.candidate.datum
      (rd.candidate.newSourceEdge sheet),
    (rd.newOldEdge sheet hSurvives).stablePath = path

/-- **The support of the regrown column, enumerated.**  A list of sheets whose
regrown occurrences all lie on the row and exhaust it names exactly that
row's regrown occurrences. -/
theorem occurrences_new_eq (path : StablePath data)
    (sheets : List (Fin degree))
    (hMem : ∀ sheet ∈ sheets, RegrownAt rd path sheet)
    (hExhaustive : ∀ sheet : Fin degree, RegrownAt rd path sheet →
      rd.candidate.newSourceEdge sheet ∈
        sheets.map rd.candidate.newSourceEdge) :
    occurrences rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) =
      (sheets.map rd.candidate.newSourceEdge).toFinset := by
  classical
  ext item
  rw [rd.mem_occurrences_new_iff path item, List.mem_toFinset]
  constructor
  · rintro ⟨sheet, hSurvives, rfl, hRow⟩
    exact hExhaustive sheet ⟨hSurvives, hRow⟩
  · intro hItem
    obtain ⟨sheet, hSheet, rfl⟩ := List.mem_map.mp hItem
    obtain ⟨hSurvives, hRow⟩ := hMem sheet hSheet
    exact ⟨sheet, hSurvives, rfl, hRow⟩

/-- **The regrown column of a member, evaluated as a list.**  Its entry in a
stable row is the sum of the reciprocal new-edge indices of the sheets
regrowing onto that row, once per regrown occurrence. -/
theorem matrix_new (path : StablePath data)
    (sheets : List (Fin degree))
    (hMem : ∀ sheet ∈ sheets, RegrownAt rd path sheet)
    (hExhaustive : ∀ sheet : Fin degree, RegrownAt rd path sheet →
      rd.candidate.newSourceEdge sheet ∈
        sheets.map rd.candidate.newSourceEdge)
    (hNodup : (sheets.map rd.candidate.newSourceEdge).Nodup) :
    matrix rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) =
      (sheets.map fun sheet ↦ (1 : ℚ) /
        rd.candidate.datum.sourceEdgeIndex (rd.candidate.newSourceEdge sheet)).sum := by
  classical
  unfold matrix
  rw [occurrences_new_eq rd path sheets hMem hExhaustive,
    List.sum_toFinset _ hNodup, List.map_map]
  rfl


/-! ### The `Finset` route: the regrown column split into its two halves -/

/-- The regrown column's occurrence set of the member, read in the incoming
row. -/
noncomputable def newOccurrences (path : StablePath data) :
    Finset rd.candidate.datum.SourceEdge :=
  occurrences rd.candidate.datum (rd.stablePathEquiv path)
    (occurrenceEquiv target wall rd.candidate.right none)

theorem mem_newOccurrences (path : StablePath data) (edge : rd.candidate.datum.SourceEdge) :
    edge ∈ rd.newOccurrences path ↔
      ∃ (sheet : Fin degree) (hSurvives : ¬ IsDangling rd.candidate.datum
          (rd.candidate.newSourceEdge sheet)),
        edge = rd.candidate.newSourceEdge sheet ∧
          (rd.newOldEdge sheet hSurvives).stablePath = path :=
  rd.mem_occurrences_new_iff path edge

/-- A new occurrence's canonical sheet lies in the wall block of the sheet
naming it. -/
theorem newSourceEdge_sheet_rel_iff (sheet : Fin degree) :
    (data.vertexPartition wall).Rel rd.selected (rd.candidate.newSourceEdge sheet).1.2 ↔
      (data.vertexPartition wall).Rel rd.selected sheet := by
  rw [BalancedGlobal.Candidate.newSourceEdge_sheet]
  have hRefines : (pasted rd.candidate).right.Refines (data.vertexPartition wall) :=
    SheetPartition.IsJoin.right_refines (LocalResolution.paste_contracts
      (data.vertexPartition wall) rd.candidate.resolution rd.candidate.contracts)
  have hRel : (data.vertexPartition wall).Rel sheet
      ((pasted rd.candidate).newEdge.repr sheet) :=
    hRefines.rel ((pasted rd.candidate).edge_refines_right.rel
      ((pasted rd.candidate).newEdge.rel_repr_right sheet))
  exact ⟨fun h ↦ h.trans hRel.symm, fun h ↦ h.trans hRel⟩

theorem eq_newSourceEdge_of_mem (path : StablePath data) (edge : rd.candidate.datum.SourceEdge)
    (hMem : edge ∈ rd.newOccurrences path) :
    edge = rd.candidate.newSourceEdge edge.1.2 :=
  M11SplitRows.eq_newSourceEdge_of_target rd.candidate edge
    ((mem_occurrences _ _ _).mp hMem).2

/-- A surviving selected new occurrence sits in the regrown column exactly in
its representative's row. -/
theorem new_mem_iff_of_survives (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel rd.selected sheet)
    (hSurvives : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge sheet))
    (path : StablePath data) :
    rd.candidate.newSourceEdge sheet ∈ rd.newOccurrences path ↔
      path = NonDanglingEdge.stablePath
        (⟨rd.selectedRep sheet, rd.selectedRep_survives sheet hRel⟩ : NonDanglingEdge data) := by
  rw [rd.mem_newOccurrences]
  constructor
  · rintro ⟨other, hOther, hEqual, hRow⟩
    rw [← hRow]
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext
      ((rd.newOldSourceEdge_congr hEqual.symm).trans (rd.newOldSourceEdge_selected hRel)))
  · intro hPath
    refine ⟨sheet, hSurvives, rfl, ?_⟩
    rw [hPath]
    exact congrArg NonDanglingEdge.stablePath (Subtype.ext (rd.newOldSourceEdge_selected hRel))

theorem new_not_mem_of_dangling (sheet : Fin degree)
    (hDangling : IsDangling rd.candidate.datum (rd.candidate.newSourceEdge sheet))
    (path : StablePath data) :
    rd.candidate.newSourceEdge sheet ∉ rd.newOccurrences path := by
  rw [newOccurrences, mem_occurrences]
  rintro ⟨⟨h, _⟩, _⟩
  exact h hDangling

end SelectedData

/-- The occurrences of one old wall column that lie **outside** the
distinguished block: the background, whose cofactor-weighted sum is the `s`
of every limit box. -/
noncomputable def backgroundOccurrences (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) (path : StablePath data) (place : target.edges) :
    Finset data.SourceEdge := by
  classical
  exact (occurrences data path place).filter
    (fun edge ↦ ¬ (data.vertexPartition wall).Rel anchor edge.1.2)

theorem mem_backgroundOccurrences (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) (path : StablePath data) (place : target.edges)
    (edge : data.SourceEdge) :
    edge ∈ backgroundOccurrences data wall anchor path place ↔
      edge ∈ occurrences data path place ∧
        ¬ (data.vertexPartition wall).Rel anchor edge.1.2 := by
  classical
  simp only [backgroundOccurrences, Finset.mem_filter]

/-- The background `s`, read on one old wall column and one old stable row. -/
noncomputable def backgroundColumn (data : GluingDatum target degree) (wall : target.V)
    (anchor : Fin degree) (path : StablePath data) (place : target.edges) : ℚ :=
  ∑ edge ∈ backgroundOccurrences data wall anchor path place,
    (1 : ℚ) / data.sourceEdgeIndex edge

namespace SelectedData

variable (rd : SelectedData data wall)

/-- **The background half of the regrown column is the retained direction's
own background.**  Every old occurrence of the retained direction outside the
distinguished block is matched with the regrown occurrence of its own wall
block, in the same row and with the same index. -/
theorem background_sum (path : StablePath data) :
    ∑ edge ∈ (rd.newOccurrences path).filter
        (fun edge ↦ ¬ (data.vertexPartition wall).Rel rd.selected edge.1.2),
      (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge =
    backgroundColumn data wall rd.selected path rd.retainedTarget := by
  classical
  symm
  unfold backgroundColumn
  refine Finset.sum_bij (fun edge _ ↦ rd.candidate.newSourceEdge edge.1.2) ?_ ?_ ?_ ?_
  · intro edge hEdge
    obtain ⟨hOld, hBackground⟩ :=
      (mem_backgroundOccurrences data wall rd.selected path rd.retainedTarget edge).mp hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    have hSelf := rd.sourceEdge_retained_self hTarget
    have hNew : ¬ IsDangling rd.candidate.datum (rd.candidate.newSourceEdge edge.1.2) := by
      rw [rd.new_isDangling_iff rd.valid hBackground, hSelf]
      exact hSurvives
    refine Finset.mem_filter.mpr ⟨(rd.mem_newOccurrences path _).mpr
      ⟨edge.1.2, hNew, rfl, ?_⟩, ?_⟩
    · rw [← hRow]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        ((rd.newOldSourceEdge_background hBackground).trans hSelf))
    · exact fun h ↦ hBackground ((rd.newSourceEdge_sheet_rel_iff edge.1.2).mp h)
  · intro first hFirst second hSecond hEqual
    obtain ⟨hFirstOld, hFirstBackground⟩ :=
      (mem_backgroundOccurrences data wall rd.selected path rd.retainedTarget first).mp hFirst
    obtain ⟨hSecondOld, _⟩ :=
      (mem_backgroundOccurrences data wall rd.selected path rd.retainedTarget second).mp hSecond
    have hRel := (Background.newSourceEdge_eq_iff rd.toBackgroundShape hFirstBackground).mp hEqual
    have hSource := (sourceEdge_eq_iff_rel data rd.retainedTarget first.1.2 second.1.2).mpr hRel
    rwa [rd.sourceEdge_retained_self ((mem_occurrences _ _ _).mp hFirstOld).2,
      rd.sourceEdge_retained_self ((mem_occurrences _ _ _).mp hSecondOld).2] at hSource
  · intro edge hEdge
    obtain ⟨hMem, hBackground⟩ := Finset.mem_filter.mp hEdge
    obtain ⟨sheet, hSurvives, rfl, hRow⟩ := (rd.mem_newOccurrences path edge).mp hMem
    have hSheet : ¬ (data.vertexPartition wall).Rel rd.selected sheet :=
      fun h ↦ hBackground ((rd.newSourceEdge_sheet_rel_iff sheet).mpr h)
    have hOldSurvives : ¬ IsDangling data (data.sourceEdge rd.retainedTarget sheet) := by
      rw [← rd.newOldSourceEdge_background hSheet]
      exact rd.newOldSourceEdge_survives sheet hSurvives
    have hRefines : (data.edgePartition rd.retainedTarget).Refines
        (data.vertexPartition wall) :=
      refines_of_mem_incidentEdges data rd.target_mem
    have hRepr : ¬ (data.vertexPartition wall).Rel rd.selected
        (data.sourceEdge rd.retainedTarget sheet).1.2 := fun h ↦
      hSheet (h.trans (hRefines.rel
        ((data.edgePartition rd.retainedTarget).rel_repr_left sheet)))
    refine ⟨data.sourceEdge rd.retainedTarget sheet, ?_, ?_⟩
    · refine (mem_backgroundOccurrences data wall rd.selected path rd.retainedTarget _).mpr
        ⟨(mem_occurrences _ _ _).mpr ⟨⟨hOldSurvives, ?_⟩, rfl⟩, hRepr⟩
      rw [← hRow]
      exact congrArg NonDanglingEdge.stablePath (Subtype.ext
        (rd.newOldSourceEdge_background hSheet).symm)
    · exact Background.newSourceEdge_eq_of_edge_rel rd.toBackgroundShape hSheet
        ((data.edgePartition rd.retainedTarget).rel_repr_right sheet)
  · intro edge hEdge
    obtain ⟨hOld, hBackground⟩ :=
      (mem_backgroundOccurrences data wall rd.selected path rd.retainedTarget edge).mp hEdge
    rw [rd.newIndex_eq hBackground,
      rd.sourceEdge_retained_self ((mem_occurrences _ _ _).mp hOld).2]

/-- **The regrown column, split into its selected and background halves.** -/
theorem matrix_new_split (path : StablePath data) :
    matrix rd.candidate.datum (rd.stablePathEquiv path)
        (occurrenceEquiv target wall rd.candidate.right none) =
      (∑ edge ∈ (rd.newOccurrences path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel rd.selected edge.1.2),
        (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge) +
        backgroundColumn data wall rd.selected path rd.retainedTarget := by
  classical
  rw [← rd.background_sum path]
  exact (Finset.sum_filter_add_sum_filter_not (rd.newOccurrences path)
    (fun edge ↦ (data.vertexPartition wall).Rel rd.selected edge.1.2)
    (fun edge ↦ (1 : ℚ) / rd.candidate.datum.sourceEdgeIndex edge)).symm

/-- The regrown occurrences above the distinguished block, when two anchors
cover its regrown classes. -/
theorem selected_set (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel rd.selected first)
    (hSecond : (data.vertexPartition wall).Rel rd.selected second)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel rd.selected sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first ∨
        rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge second)
    (path : StablePath data) :
    (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel rd.selected edge.1.2) =
      ({rd.candidate.newSourceEdge first, rd.candidate.newSourceEdge second} :
        Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hMem, hRel⟩
    refine ⟨?_, hMem⟩
    rw [rd.eq_newSourceEdge_of_mem path edge hMem]
    exact hCover edge.1.2 hRel
  · rintro ⟨hEq, hMem⟩
    refine ⟨hMem, ?_⟩
    rcases hEq with rfl | rfl
    · exact (rd.newSourceEdge_sheet_rel_iff first).mpr hFirst
    · exact (rd.newSourceEdge_sheet_rel_iff second).mpr hSecond

/-- The same when one of the two regrown classes is pruned. -/
theorem selected_set_of_dangling (first second : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel rd.selected first)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel rd.selected sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first ∨
        rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge second)
    (hDangling : IsDangling rd.candidate.datum (rd.candidate.newSourceEdge second))
    (path : StablePath data) :
    (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel rd.selected edge.1.2) =
      ({rd.candidate.newSourceEdge first} :
        Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hMem, hRel⟩
    refine ⟨?_, hMem⟩
    have hEdgeNew := rd.eq_newSourceEdge_of_mem path edge hMem
    rcases hCover edge.1.2 hRel with h | h
    · exact hEdgeNew.trans h
    · exact absurd (rd.new_not_mem_of_dangling second hDangling path)
        (fun hNot ↦ hNot (by rwa [← h, ← hEdgeNew]))
  · rintro ⟨rfl, hMem⟩
    exact ⟨hMem, (rd.newSourceEdge_sheet_rel_iff first).mpr hFirst⟩

end SelectedData

/-! ### Gauges: the isomorphisms of the stable source a length matrix cannot see

A length matrix reads only the target occurrence and the dilation index of
each occurrence.  That is not enough to carry a *stable row*.  A `Gauge` is an
occurrence bijection which preserves pruning and carries the stable quotient;
both gauges the four-star case uses are of this kind, the identity and the
branch swap of Draisma--Vargas Part I. -/

variable {base : GluingDatum target degree}

/-- An occurrence bijection carrying the whole stable source: target
occurrence, dilation index, pruning, stable rows and the wall partition. -/
structure Gauge (data base : GluingDatum target degree) (wall : target.V) where
  /-- The occurrence bijection. -/
  edge : data.SourceEdge ≃ base.SourceEdge
  /-- It lies over the identity of the target. -/
  target_eq : ∀ e : data.SourceEdge, (edge e).1.1 = e.1.1
  /-- It preserves dilation indices. -/
  index_eq : ∀ e : data.SourceEdge, base.sourceEdgeIndex (edge e) = data.sourceEdgeIndex e
  /-- It preserves pruning. -/
  isDangling_iff : ∀ e : data.SourceEdge, IsDangling base (edge e) ↔ IsDangling data e
  /-- The induced map of stable rows. -/
  row : StablePath data ≃ StablePath base
  /-- which really is induced by the occurrence bijection. -/
  row_mk : ∀ (e : data.SourceEdge) (hSurvives : ¬ IsDangling data e),
    row (NonDanglingEdge.stablePath (⟨e, hSurvives⟩ : NonDanglingEdge data)) =
      NonDanglingEdge.stablePath (⟨edge e, fun hDangling ↦
        hSurvives ((isDangling_iff e).mp hDangling)⟩ : NonDanglingEdge base)
  /-- and it fixes the wall's own sheet partition. -/
  wall_eq : base.vertexPartition wall = data.vertexPartition wall

namespace Gauge

/-- The identity gauge, for a member built on the incoming datum itself. -/
def refl (data : GluingDatum target degree) (wall : target.V) :
    Gauge data data wall where
  edge := Equiv.refl _
  target_eq _ := rfl
  index_eq _ := rfl
  isDangling_iff _ := Iff.rfl
  row := Equiv.refl _
  row_mk _ _ := rfl
  wall_eq := rfl

/-- **Every sheet relabelling of a connected datum is a gauge.**  The
stable quotient is what `SheetRelabelPruning`/`SheetRelabelStable` carry. -/
noncomputable def ofSheetRelabeling (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected)
    (hWall : relabeling.apply.vertexPartition wall = data.vertexPartition wall) :
    Gauge data relabeling.apply wall where
  edge := relabeling.sourceEdgeEquiv
  target_eq _ := rfl
  index_eq := SheetRelabelStable.sourceEdgeIndex_map relabeling
  isDangling_iff e :=
    SheetRelabelPruning.isDangling_sourceEdgeEquiv_iff relabeling hConnected e
  row := SheetRelabelStable.stablePathEquiv relabeling hConnected
  row_mk e hSurvives :=
    SheetRelabelStable.stablePathEquiv_mk relabeling hConnected ⟨e, hSurvives⟩
  wall_eq := hWall

variable (gauge : Gauge data base wall)

/-- A gauge carries the surviving occurrences of a stable row above one
direction onto those of the image row. -/
theorem occurrences_gauge (path : StablePath data) (place : target.edges) :
    occurrences base (gauge.row path) place =
      (occurrences data path place).image gauge.edge := by
  classical
  ext item
  obtain ⟨item, rfl⟩ := gauge.edge.surjective item
  rw [mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    have hOld : ¬ IsDangling data item := fun hDangling ↦
      hSurvives ((gauge.isDangling_iff item).mpr hDangling)
    refine Finset.mem_image.mpr ⟨item, (mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, ?_⟩, rfl⟩
    · exact gauge.row.injective ((gauge.row_mk item hOld).trans hRow)
    · rw [← hTarget, gauge.target_eq item]
  · intro hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    have hEq : old = item := gauge.edge.injective hEqual
    subst hEq
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_occurrences _ _ _).mp hOld
    refine ⟨⟨fun hDangling ↦ hSurvives ((gauge.isDangling_iff old).mp hDangling), ?_⟩, ?_⟩
    · exact (gauge.row_mk old hSurvives).symm.trans (congrArg gauge.row hRow)
    · rw [gauge.target_eq old]; exact hTarget

/-- **A gauge preserves the natural stable-length matrix**, column by column
and row by row. -/
theorem matrix_gauge (path : StablePath data) (place : target.edges) :
    matrix base (gauge.row path) place = matrix data path place := by
  classical
  unfold matrix
  rw [gauge.occurrences_gauge, Finset.sum_image]
  · exact Finset.sum_congr rfl fun item _ ↦ by rw [gauge.index_eq]
  · exact fun _ _ _ _ hEqual ↦ gauge.edge.injective hEqual

end Gauge

/-- A displayed occurrence above `t` is the canonical occurrence through its
own sheet. -/
theorem sourceEdge_of_target (edge : data.SourceEdge) (t : target.edges)
    (hTarget : t = edge.1.1) : data.sourceEdge t edge.1.2 = edge := by
  rw [hTarget]
  exact GluingDatum.sourceEdge_self data edge


end DraismaVargas.LocalCases.LimitChainCore
