import DraismaVargas.LocalCases.StableGraphIncidence
import DraismaVargas.LocalCases.ClassInjectivity
import Utilities.CubicGraphs.CubicDarts

/-!
# The actual stable source as a cubic dart graph

Draisma--Vargas Part I constructs `H(M)` from the actual branch vertices and
maximal stable paths (§3.1). Its occurrence-based row labels descend along
source isomorphisms (§5.2, the induced labelling of a limit). Vargas, Part II
(§1.3, tropical modification) first deletes dangling trees and then takes the
essential model. This module constructs that graph's dart model.

A dart is a literal surviving source occurrence at a branch vertex. The
proved stable-path count gives exactly two darts in each row; their unique
exchange defines the opposite involution. Two ends of a stable loop remain
distinct occurrence flags at the same vertex. No orientation, enumeration,
or supplied graph-isomorphism receipt is used.

Connectivity has two steps. A finite-set induction removes dangling detours
from source walks, following the fibre-restricted argument of
`PrunedContractionFibre.surviving_walk_of_walk_within`. Suppression then
identifies two incident occurrences at a divalent vertex with the same row,
while at a branch they become darts at the same vertex. Thus `ofDatum`
constructs all fields of the cubic graph from connectedness, trivalence, and
`HasPathEnds`, which a full-dimensional presentation already carries.

Genus comparison, incidence-isomorphism transport, seed identification, and
metric/refinement dictionaries are separate consumers, not claimed here.
-/

namespace DraismaVargas.LocalCases.StableSourceDarts

open DraismaVargas.Infrastructure W4StableSource StablePathCount StableGraphIncidence
open CubicDarts

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-- An actual surviving occurrence at an actual branch vertex. -/
def Dart := Σ v : BranchVertex data, {e : NonDanglingEdge data // Incident data e.1 v.1}

noncomputable instance : Fintype (BranchVertex data) := by
  classical
  unfold BranchVertex
  infer_instance
noncomputable instance : DecidableEq (BranchVertex data) := Classical.decEq _
noncomputable instance : Fintype (Dart data) := by
  classical
  exact inferInstanceAs (Fintype (Σ v : BranchVertex data,
    {e : NonDanglingEdge data // Incident data e.1 v.1}))
noncomputable instance : DecidableEq (Dart data) := Classical.decEq _

def row (d : Dart data) : StablePath data := d.2.1.stablePath
def vertex (d : Dart data) : BranchVertex data := d.1

theorem card_incidence (v : BranchVertex data) (r : StablePath data) :
    Fintype.card {e : NonDanglingEdge data // Incident data e.1 v.1 ∧ e.stablePath = r} =
      incidenceCount data v.1 r := by
  classical
  simp [Fintype.card_subtype, incidenceCount, incidentEdges, Finset.filter_filter]

theorem card_row (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (r : StablePath data) : Fintype.card {d : Dart data // row data d = r} = 2 := by
  classical
  let e : {d : Dart data // row data d = r} ≃
      Σ v : BranchVertex data, {e : NonDanglingEdge data // Incident data e.1 v.1 ∧ e.stablePath = r} :=
    { toFun := fun d ↦ ⟨d.1.1, ⟨d.1.2.1, d.1.2.2, d.2⟩⟩
      invFun := fun d ↦ ⟨⟨d.1, ⟨d.2.1, d.2.2.1⟩⟩, d.2.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [card_incidence]
  have hSum : (∑ v : BranchVertex data, incidenceCount data v.1 r) = endCount data r := by
    rw [show (∑ v : BranchVertex data, incidenceCount data v.1 r) =
      ∑ v ∈ Trivalence.stableVertices data, incidenceCount data v r from
        (Finset.sum_subtype (Trivalence.stableVertices data)
          (Trivalence.mem_stableVertices data) (fun v ↦ incidenceCount data v r)).symm]
    unfold endCount
    apply Finset.sum_subset
    · intro v hv
      have := (Trivalence.mem_stableVertices data v).mp hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · intro v hv hn
      have hOne := NonDanglingValency.nonDanglingValency_ne_one data hConnected v
      have hNot := (Trivalence.mem_stableVertices data v).not.mp hn
      have hTwo := (Finset.mem_filter.mp hv).2
      have hZero : nonDanglingValency data v = 0 := by omega
      have hBound := Finset.single_le_sum (f := incidenceCount data v) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ r : r ∈ (Finset.univ : Finset (StablePath data)))
      rw [sum_incidenceCount_vertex data v, hZero] at hBound
      exact Nat.eq_zero_of_le_zero hBound
  rw [hSum]
  exact endCount_eq_two data (NonDanglingValency.nonDanglingValency_ne_one data hConnected) hEnds r

theorem card_vertex (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (v : BranchVertex data) :
    (Finset.univ.filter (fun d : Dart data ↦ vertex data d = v)).card = 3 := by
  classical
  let e : {d : Dart data // vertex data d = v} ≃
      {edge : NonDanglingEdge data // Incident data edge.1 v.1} :=
    { toFun := fun d ↦ ⟨d.1.2.1, by
        have h : d.1.1 = v := d.2
        exact Eq.mp (congrArg (fun w : BranchVertex data ↦
          Incident data d.1.2.1.1 w.1) h) d.1.2.2⟩
      invFun := fun edge ↦ ⟨⟨v, edge⟩, rfl⟩
      left_inv := by rintro ⟨⟨w, edge⟩, h⟩; cases h; rfl
      right_inv := fun _ ↦ rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr e]
  have hCard : Fintype.card {edge : NonDanglingEdge data // Incident data edge.1 v.1} =
      nonDanglingValency data v.1 := by
    rw [Fintype.card_subtype]
    exact card_incidentEdges data v.1
  rw [hCard]
  exact Nat.le_antisymm (hTrivalent v.1) v.2

theorem exists_unique_other (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (d : Dart data) : ∃! e : Dart data, row data e = row data d ∧ e ≠ d := by
  classical
  have hCard : (Finset.univ.filter (fun e : Dart data ↦ row data e = row data d)).card = 2 := by
    rw [← Fintype.card_subtype]
    exact card_row data hConnected hEnds (row data d)
  obtain ⟨a, b, hab, hPair⟩ := Finset.card_eq_two.mp hCard
  have hMem (e : Dart data) : row data e = row data d ↔ e = a ∨ e = b := by
    have := congrArg (fun s : Finset (Dart data) ↦ e ∈ s) hPair
    simpa using this
  rcases (hMem d).mp rfl with h | h
  · refine ⟨b, ⟨(hMem b).mpr (Or.inr rfl), ?_⟩, ?_⟩
    · exact fun hb ↦ hab (h.symm.trans hb.symm)
    · intro e he
      rcases (hMem e).mp he.1 with heq | heq
      · exact (he.2 (heq.trans h.symm)).elim
      · exact heq
  · refine ⟨a, ⟨(hMem a).mpr (Or.inl rfl), ?_⟩, ?_⟩
    · exact fun ha ↦ hab (ha.trans h)
    · intro e he
      rcases (hMem e).mp he.1 with heq | heq
      · exact heq
      · exact (he.2 (heq.trans h.symm)).elim

noncomputable def opposite (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (d : Dart data) : Dart data := (exists_unique_other data hConnected hEnds d).choose

theorem row_opposite (hConnected : data.Connected) (hEnds : HasPathEnds data) (d : Dart data) :
    row data (opposite data hConnected hEnds d) = row data d :=
  (exists_unique_other data hConnected hEnds d).choose_spec.1.1

theorem opposite_ne (hConnected : data.Connected) (hEnds : HasPathEnds data) (d : Dart data) :
    opposite data hConnected hEnds d ≠ d :=
  (exists_unique_other data hConnected hEnds d).choose_spec.1.2

theorem opposite_eq_of_row_eq (hConnected : data.Connected) (hEnds : HasPathEnds data)
    {d e : Dart data} (hRow : row data e = row data d) (hNe : e ≠ d) :
    e = opposite data hConnected hEnds d :=
  (exists_unique_other data hConnected hEnds d).choose_spec.2 e ⟨hRow, hNe⟩

theorem opposite_opposite (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (d : Dart data) : opposite data hConnected hEnds (opposite data hConnected hEnds d) = d :=
  (opposite_eq_of_row_eq data hConnected hEnds
    (row_opposite data hConnected hEnds d).symm
    (Ne.symm (opposite_ne data hConnected hEnds d))).symm

/-- The literal stable rows are exactly the opposite pairs, including loops. -/
theorem row_eq_iff (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (d e : Dart data) : row data d = row data e ↔
      e = d ∨ e = opposite data hConnected hEnds d := by
  constructor
  · intro h
    by_cases he : e = d
    · exact Or.inl he
    · exact Or.inr (opposite_eq_of_row_eq data hConnected hEnds h.symm he)
  · rintro (rfl | rfl)
    · rfl
    · exact (row_opposite data hConnected hEnds d).symm

open ClassInjectivity StableLocalProperties Utilities DanglingDescent

/-- A step across a literal surviving source occurrence. -/
def SurvivingStep (a b : data.SourceVertex) : Prop :=
  ∃ e : NonDanglingEdge data,
    data.sourceEnds e.1 = (a, b) ∨ data.sourceEnds e.1 = (b, a)

/-- Remove dangling detours from an arbitrary source walk. This is the
finite-set pruning argument, with no restriction to a contracted target fibre. -/
theorem surviving_walk_within :
    ∀ vertices : Finset data.SourceVertex, ∀ first second : data.SourceVertex,
      first ∈ vertices → second ∈ vertices →
      nonDanglingValency data first ≠ 0 → nonDanglingValency data second ≠ 0 →
      Relation.ReflTransGen (fun x y ↦ 0 < num_edges data.sourceGraph x y ∧
        x ∈ vertices ∧ y ∈ vertices) first second →
      Relation.ReflTransGen (SurvivingStep data) first second := by
  classical
  intro vertices
  refine Finset.strongInductionOn vertices ?_
  intro vertices ih first second hFirstMem hSecondMem hFirstActive hSecondActive hWalk
  by_cases hEq : first = second
  · subst second
    exact .refl
  obtain ⟨next, hStep, hAvoid⟩ := exists_step_avoiding
    (R := fun x y ↦ 0 < num_edges data.sourceGraph x y ∧ x ∈ vertices ∧ y ∈ vertices)
    (fun {_ _} h ↦ ⟨by rw [num_edges_symmetric]; exact h.1, h.2.2, h.2.1⟩) hWalk hEq
  obtain ⟨edge, hEnds⟩ := ClassInjectivity.exists_sourceEnds_of_num_edges_pos data hStep.1
  have hSurvives : ¬ IsDangling data edge := by
    intro hDangling
    rcases NonDanglingValency.danglingSide_of_isDangling data hEnds hDangling with hCut | hCut
    · obtain ⟨cut⟩ := hCut
      exact hFirstActive (nonDanglingValency_eq_zero_of_danglingSide data cut)
    · obtain ⟨cut⟩ := hCut
      have hInside : second ∈ cut.side :=
        mem_side_of_avoiding cut.toSeparatingEdgeCut
          (Relation.ReflTransGen.mono (fun _ _ h ↦ ⟨h.1.1, h.2.2⟩) _ _ hAvoid)
      exact hSecondActive (nonDanglingValency_eq_zero_of_mem_side data cut.side.card
        next first cut le_rfl second hInside)
  have hNextActive : nonDanglingValency data next ≠ 0 :=
    nonDanglingValency_ne_zero_of_incident data hSurvives (incident_of_sourceEnds data hEnds.symm)
  have hNextNe : next ≠ first := by
    intro hSame
    have hPos := hStep.1
    have hZero : num_edges data.sourceGraph first first = 0 :=
      num_edges_self_zero data.sourceGraph first
    rw [hSame] at hPos
    omega
  have hTail : Relation.ReflTransGen
      (fun x y ↦ 0 < num_edges data.sourceGraph x y ∧
        x ∈ vertices.erase first ∧ y ∈ vertices.erase first) next second :=
    Relation.ReflTransGen.mono
      (fun _ _ h ↦ ⟨h.1.1, Finset.mem_erase.mpr ⟨h.2.1, h.1.2.1⟩,
        Finset.mem_erase.mpr ⟨h.2.2, h.1.2.2⟩⟩) _ _ hAvoid
  exact Relation.ReflTransGen.head ⟨⟨edge, hSurvives⟩, hEnds⟩
    (ih (vertices.erase first) (Finset.erase_ssubset hFirstMem) next second
      (Finset.mem_erase.mpr ⟨hNextNe, hStep.2.2⟩)
      (Finset.mem_erase.mpr ⟨Ne.symm hEq, hSecondMem⟩) hNextActive hSecondActive hTail)

/-- All active source vertices are joined by actual surviving occurrences. -/
theorem surviving_walk (hConnected : data.Connected) {first second : data.SourceVertex}
    (hFirst : nonDanglingValency data first ≠ 0)
    (hSecond : nonDanglingValency data second ≠ 0) :
    Relation.ReflTransGen (SurvivingStep data) first second := by
  classical
  apply surviving_walk_within data Finset.univ first second
    (Finset.mem_univ _) (Finset.mem_univ _) hFirst hSecond
  have h := reach_of_graph_connected hConnected first second
  clear hFirst hSecond
  induction h with
  | refl => exact .refl
  | @tail a b _ hStep ih => exact ih.tail ⟨hStep, Finset.mem_univ _, Finset.mem_univ _⟩

theorem exists_dart_row (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (r : StablePath data) : ∃ d : Dart data, row data d = r := by
  classical
  have hCard := card_row data hConnected hEnds r
  have hNonempty : Nonempty {d : Dart data // row data d = r} :=
    Fintype.card_pos_iff.mp (by omega)
  obtain ⟨d⟩ := hNonempty
  exact ⟨d.1, d.2⟩

noncomputable def rowDart (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (r : StablePath data) : Dart data := (exists_dart_row data hConnected hEnds r).choose

theorem row_rowDart (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (r : StablePath data) : row data (rowDart data hConnected hEnds r) = r :=
  (exists_dart_row data hConnected hEnds r).choose_spec

theorem related_of_row_eq (hConnected : data.Connected) (hEnds : HasPathEnds data)
    {d e : Dart data} (hRow : row data d = row data e) :
    Relation.EqvGen (DartRel (opposite data hConnected hEnds) (vertex data)) d e := by
  by_cases hEq : e = d
  · subst e
    exact .refl _
  exact DartRel.of_op (opposite_eq_of_row_eq data hConnected hEnds hRow.symm hEq).symm

theorem related_incident_rows (hConnected : data.Connected) (hEnds : HasPathEnds data)
    {v : data.SourceVertex} (e f : NonDanglingEdge data)
    (he : Incident data e.1 v) (hf : Incident data f.1 v) :
    Relation.EqvGen (DartRel (opposite data hConnected hEnds) (vertex data))
      (rowDart data hConnected hEnds e.stablePath) (rowDart data hConnected hEnds f.stablePath) := by
  by_cases hTwo : nonDanglingValency data v = 2
  · have hRows : e.stablePath = f.stablePath := by
      by_cases hEq : e = f
      · rw [hEq]
      exact stablePath_eq_of_consecutive ⟨hEq, v, he, hf, hTwo⟩
    rw [hRows]
    exact .refl _
  · have hActive := nonDanglingValency_ne_zero_of_incident data e.2 he
    have hOne := NonDanglingValency.nonDanglingValency_ne_one data hConnected v
    have hBranch : 3 ≤ nonDanglingValency data v := by omega
    let d : Dart data := ⟨⟨v, hBranch⟩, ⟨e, he⟩⟩
    let d' : Dart data := ⟨⟨v, hBranch⟩, ⟨f, hf⟩⟩
    have hFirst := related_of_row_eq data hConnected hEnds
      (d := rowDart data hConnected hEnds e.stablePath) (e := d)
      (row_rowDart data hConnected hEnds e.stablePath)
    have hLast := related_of_row_eq data hConnected hEnds
      (d := d') (e := rowDart data hConnected hEnds f.stablePath)
      (row_rowDart data hConnected hEnds f.stablePath).symm
    exact DartRel.trans hFirst (DartRel.trans
      (DartRel.of_vert (show vertex data d = vertex data d' from rfl)) hLast)

/-- Suppressing the divalent vertices projects each surviving source walk
to the dart graph without choosing an ordering of any stable path. -/
theorem related_of_surviving_walk (hConnected : data.Connected) (hEnds : HasPathEnds data)
    {first second : data.SourceVertex}
    (hWalk : Relation.ReflTransGen (SurvivingStep data) first second)
    (e f : NonDanglingEdge data) (he : Incident data e.1 first) (hf : Incident data f.1 second) :
    Relation.EqvGen (DartRel (opposite data hConnected hEnds) (vertex data))
      (rowDart data hConnected hEnds e.stablePath) (rowDart data hConnected hEnds f.stablePath) := by
  induction hWalk generalizing f with
  | refl => exact related_incident_rows data hConnected hEnds e f he hf
  | @tail previous last hWalk hStep ih =>
    obtain ⟨edge, hEdge⟩ := hStep
    exact DartRel.trans (ih edge (incident_of_sourceEnds data hEdge))
      (related_incident_rows data hConnected hEnds edge f
        (incident_of_sourceEnds data hEdge.symm) hf)

theorem connected (hConnected : data.Connected) (hEnds : HasPathEnds data)
    (d e : Dart data) :
    Relation.EqvGen (DartRel (opposite data hConnected hEnds) (vertex data)) d e := by
  have hWalk := surviving_walk data hConnected
    (first := d.1.1) (second := e.1.1) (by have := d.1.2; omega) (by have := e.1.2; omega)
  have hMiddle := related_of_surviving_walk data hConnected hEnds hWalk d.2.1 e.2.1 d.2.2 e.2.2
  have hFirst := related_of_row_eq data hConnected hEnds
    (d := d) (e := rowDart data hConnected hEnds (row data d))
    (row_rowDart data hConnected hEnds (row data d)).symm
  have hLast := related_of_row_eq data hConnected hEnds
    (d := rowDart data hConnected hEnds (row data e)) (e := e)
    (row_rowDart data hConnected hEnds (row data e))
  exact DartRel.trans hFirst (DartRel.trans hMiddle hLast)

/-- The actual stable source of a connected trivalent datum, with literal
occurrence flags and maximal stable-row labels. -/
noncomputable def ofDatum (hConnected : data.Connected)
    (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3) (hEnds : HasPathEnds data) :
    CubicDartGraph (Dart data) (BranchVertex data) where
  op := opposite data hConnected hEnds
  vert := vertex data
  op_invol := opposite_opposite data hConnected hEnds
  op_ne := opposite_ne data hConnected hEnds
  card_fibre := card_vertex data hTrivalent
  conn := connected data hConnected hEnds

end DraismaVargas.LocalCases.StableSourceDarts

