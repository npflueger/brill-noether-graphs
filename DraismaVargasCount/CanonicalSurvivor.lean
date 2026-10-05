module

public import DraismaVargasCount.PendantRetraction
public import DraismaVargasCount.Fibre
public import DraismaVargas.LocalCases.ClassInjectivity

@[expose] public section

/-!
# The unique surviving representative of every pendant class

Connectedness and one actual surviving vertex force every source vertex to
reach a surviving vertex by dangling occurrences: stop at the first survivor
along a source walk. Combined with the uniqueness theorem
`PendantRetraction.surviving_vertex_unique`, this constructs the literal pendant
retraction on named surviving vertices.
-/

namespace DraismaVargas.Count.CanonicalSurvivor

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource StableGraphIncidence
open DanglingDescent ClassInjectivity PendantRetraction
open Utilities.Certificate.SubdivisionGraph

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}

theorem exists_surviving_of_walk {first last : data.SourceVertex}
    (hLast : 0 < nonDanglingValency data last)
    (hWalk : Reach data.sourceGraph first last) :
    ∃ vertex : data.SourceVertex,
      0 < nonDanglingValency data vertex ∧ retractVertex first = retractVertex vertex := by
  induction hWalk using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨last, hLast, rfl⟩
  | head hStep hRest ih =>
    rename_i a b
    by_cases hActive : 0 < nonDanglingValency data a
    · exact ⟨a, hActive, rfl⟩
    obtain ⟨edge, hEnds⟩ := ClassInjectivity.exists_sourceEnds_of_num_edges_pos data hStep
    have hDangling : IsDangling data edge := by
      by_contra hNot
      have hIncident : Incident data edge a := by
        rcases hEnds with h | h <;> simp only [Incident, h] <;> simp
      have hNotZero := nonDanglingValency_ne_zero_of_incident data hNot hIncident
      omega
    have hClass : retractVertex a = retractVertex b :=
      Quotient.sound (Relation.ReflTransGen.single ⟨edge, hDangling, hEnds⟩)
    obtain ⟨vertex, hVertex, hEq⟩ := ih
    exact ⟨vertex, hVertex, hClass.trans hEq⟩

theorem exists_surviving (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (point : data.SourceVertex) :
    ∃ vertex : data.SourceVertex,
      0 < nonDanglingValency data vertex ∧ retractVertex point = retractVertex vertex := by
  obtain ⟨base, hBase⟩ := hNonempty
  exact exists_surviving_of_walk hBase (reach_of_graph_connected hConnected point base)

/-- The genuine named retraction, with no arbitrary selection among survivors:
uniqueness was proved for the canonical pendant quotient. -/
noncomputable def representative (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (point : data.SourceVertex) : {vertex : data.SourceVertex // 0 < nonDanglingValency data vertex} :=
  ⟨(exists_surviving hConnected hNonempty point).choose,
    (exists_surviving hConnected hNonempty point).choose_spec.1⟩

theorem representative_class (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (point : data.SourceVertex) :
    retractVertex point = retractVertex (representative hConnected hNonempty point).1 :=
  (exists_surviving hConnected hNonempty point).choose_spec.2

theorem representative_eq_iff (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (point : data.SourceVertex)
    (vertex : {v : data.SourceVertex // 0 < nonDanglingValency data v}) :
    representative hConnected hNonempty point = vertex ↔
      retractVertex point = retractVertex vertex.1 := by
  constructor
  · intro h
    exact (representative_class hConnected hNonempty point).trans (congrArg (fun v ↦ retractVertex v.1) h)
  · intro h
    apply Subtype.ext
    exact surviving_vertex_unique (representative hConnected hNonempty point).2 vertex.2
      ((representative_class hConnected hNonempty point).symm.trans h)

theorem representative_fixes (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (vertex : {v : data.SourceVertex // 0 < nonDanglingValency data v}) :
    representative hConnected hNonempty vertex.1 = vertex :=
  (representative_eq_iff hConnected hNonempty vertex.1 vertex).mpr rfl

theorem representative_dangling (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (edge : data.SourceEdge) (hDangling : IsDangling data edge) :
    representative hConnected hNonempty (data.sourceEnds edge).1 =
      representative hConnected hNonempty (data.sourceEnds edge).2 := by
  apply (representative_eq_iff hConnected hNonempty _ _).mpr
  exact (Quotient.sound (Relation.ReflTransGen.single
    ⟨edge, hDangling, Or.inl rfl⟩)).trans (representative_class hConnected hNonempty _)

/-- For an actual member the request's nonempty core supplies the surviving
base point; no hypothesis that the pruned source is nonempty is left to the
caller. -/
theorem member_surviving_nonempty {n p : ℕ} (spec : Spec n p)
    (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree) :
    ∃ vertex : member.data.SourceVertex, 0 < nonDanglingValency member.data vertex := by
  let branch := member.ident.vertex.symm ⟨0, spec.core_nonempty⟩
  exact ⟨branch.1, lt_of_lt_of_le (by decide : 0 < 3) branch.2⟩

/-- The named representative has exactly the canonical retracted fibre as
its literal finite pushforward, pointwise. -/
theorem representative_fibre_sum (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (root : target.V) (vertex : {v : data.SourceVertex // 0 < nonDanglingValency data v}) :
    (∑ point : data.SourceVertex,
      if representative hConnected hNonempty point = vertex then
        (if point.1.1 = root then
          ((data.vertexPartition point.1.1).blockCard point.1.2 : ℤ) else 0) else 0) =
      retractedFibre root (retractVertex vertex.1) := by
  classical
  unfold retractedFibre
  apply Finset.sum_congr rfl
  intro point _
  simp only [representative_eq_iff, ite_and]

/-- Retraction over all surviving vertices retains exactly the total fibre
mass, namely the degree. -/
theorem sum_retractedFibre (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (root : target.V) :
    (∑ vertex : {v : data.SourceVertex // 0 < nonDanglingValency data v},
      retractedFibre root (retractVertex vertex.1)) = (degree : ℤ) := by
  classical
  simp_rw [← representative_fibre_sum hConnected hNonempty root]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact data.sum_sourceVertex_localDegree_over root

theorem retractedFibre_nonneg (root : target.V) (vertex : data.SourceVertex) :
    0 ≤ retractedFibre root (retractVertex vertex) := by
  classical
  unfold retractedFibre
  apply Finset.sum_nonneg
  intro point _
  split_ifs <;> positivity

/-- Every map collapsing the actual dangling occurrences factors through
the canonical pendant equivalence relation. -/
theorem map_eq_of_retract_eq {α : Type*} (f : data.SourceVertex → α)
    (hCollapse : ∀ edge : data.SourceEdge, IsDangling data edge →
      f (data.sourceEnds edge).1 = f (data.sourceEnds edge).2)
    {first second : data.SourceVertex} (hEq : retractVertex first = retractVertex second) :
    f first = f second := by
  have hWalk := Quotient.exact hEq
  change Relation.ReflTransGen DanglingStep first second at hWalk
  clear hEq
  induction hWalk with
  | refl => rfl
  | @tail next last _ hStep ih =>
    obtain ⟨edge, hDangling, hEnds⟩ := hStep
    have h := hCollapse edge hDangling
    rcases hEnds with hEnds | hEnds <;> rw [hEnds] at h
    · exact ih.trans h
    · exact ih.trans h.symm

/-- Fixing the surviving vertices and collapsing dangling occurrences
uniquely determines the named retraction. This identifies it with a
rank-preserving pendant-deletion map without postulating divisor equality. -/
theorem map_eq_representative (hConnected : data.Connected)
    (hNonempty : ∃ vertex : data.SourceVertex, 0 < nonDanglingValency data vertex)
    (f : data.SourceVertex → {v : data.SourceVertex // 0 < nonDanglingValency data v})
    (hFixes : ∀ vertex, f vertex.1 = vertex)
    (hCollapse : ∀ edge : data.SourceEdge, IsDangling data edge →
      f (data.sourceEnds edge).1 = f (data.sourceEnds edge).2)
    (point : data.SourceVertex) : f point = representative hConnected hNonempty point :=
  (map_eq_of_retract_eq f hCollapse (representative_class hConnected hNonempty point)).trans
    (hFixes _)

end DraismaVargas.Count.CanonicalSurvivor

