import DraismaVargas.LocalCases.StableSourceDarts
import DraismaVargas.LocalCases.DanglingBetti
import DraismaVargas.LocalCases.SingleRowForest

/-!
# Incidence and genus consumers of the actual stable-source darts

The `StableSourceDarts.ofDatum` graph is constructed independently. Here an
existing, proved branch/row incidence dictionary induces an actual dart
isomorphism. The only finite choices are within a prescribed branch/row
incidence fibre; the supplied vertex and row maps remain exact. In particular
this consumer introduces no assumption identifying an arbitrary requested core
or caterpillar seed with a gluing datum.

The actual global surviving walks also identify all active vertices of the
pruned source as one component. Together with the existing stable-path Euler
count and dangling Betti invariance, this proves equality with the original
source genus. Positive source genus excludes the all-dangling tree, whose
empty flag graph is permitted by the cubic model but has genus one.

Finally a non-loop dart supplies the literal simple-end condition used by
`SingleRowForest`. No metric-length or terminal-refinement claim is made.
-/

namespace DraismaVargas.LocalCases.StableSourceDarts

open DraismaVargas.Infrastructure W4StableSource StablePathCount StableGraphIncidence
open CubicDarts

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-- Group the literal flags by their branch and stable row. -/
noncomputable def flagEquiv : Dart data ≃
    Σ v : BranchVertex data, Σ r : StablePath data,
      {e : NonDanglingEdge data // Incident data e.1 v.1 ∧ e.stablePath = r} where
  toFun d := ⟨d.1, row data d, ⟨d.2.1, d.2.2, rfl⟩⟩
  invFun d := ⟨d.1, ⟨d.2.2.1, d.2.2.2.1⟩⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨v, r, e, he, hr⟩
    cases hr
    rfl

variable {target' : CFGraph} {degree' : ℕ} {other : GluingDatum target' degree'}

/-- Only within each fixed branch/row incidence fibre is a finite bijection
chosen; both graph labels are prescribed by the actual incidence dictionary. -/
noncomputable def incidenceFibreEquiv (certificate : Equivalence data other)
    (v : BranchVertex data) (r : StablePath data) :
    {e : NonDanglingEdge data // Incident data e.1 v.1 ∧ e.stablePath = r} ≃
      {e : NonDanglingEdge other //
        Incident other e.1 (certificate.vertex v).1 ∧ e.stablePath = certificate.row r} := by
  classical
  apply Fintype.equivOfCardEq
  rw [card_incidence, card_incidence, certificate.incidence]

/-- The dart map retains exactly the certificate's actual branch and row maps. -/
noncomputable def dartEquiv (certificate : Equivalence data other) : Dart data ≃ Dart other :=
  (flagEquiv data).trans
    ((Equiv.sigmaCongr certificate.vertex fun v ↦
      Equiv.sigmaCongr certificate.row (incidenceFibreEquiv data certificate v)).trans
      (flagEquiv other).symm)

theorem dartEquiv_vertex (certificate : Equivalence data other) (d : Dart data) :
    vertex other (dartEquiv data certificate d) = certificate.vertex (vertex data d) := rfl

theorem dartEquiv_row (certificate : Equivalence data other) (d : Dart data) :
    row other (dartEquiv data certificate d) = certificate.row (row data d) :=
  (incidenceFibreEquiv data certificate d.1 (row data d) ⟨d.2.1, d.2.2, rfl⟩).2.2

/-- Multiplicity-preserving incidence equivalence gives an actual dart
isomorphism, including rows whose two ends occur at the same branch. -/
noncomputable def isoOfIncidenceEquivalence
    (hConnected : data.Connected) (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3)
    (hEnds : HasPathEnds data)
    (hConnected' : other.Connected) (hTrivalent' : ∀ v, nonDanglingValency other v ≤ 3)
    (hEnds' : HasPathEnds other) (certificate : Equivalence data other) :
    CubicDartGraph.Iso (ofDatum data hConnected hTrivalent hEnds)
      (ofDatum other hConnected' hTrivalent' hEnds') where
  dart := dartEquiv data certificate
  vtx := certificate.vertex
  vert_map := dartEquiv_vertex data certificate
  op_map d := by
    change opposite other hConnected' hEnds' (dartEquiv data certificate d) =
      dartEquiv data certificate (opposite data hConnected hEnds d)
    symm
    apply opposite_eq_of_row_eq other hConnected' hEnds'
    · rw [dartEquiv_row, dartEquiv_row, row_opposite]
    · exact fun h ↦ opposite_ne data hConnected hEnds d
        ((dartEquiv data certificate).injective h)

open Trivalence PrunedSource DanglingDescent DanglingBetti

theorem card_darts (hConnected : data.Connected) (hEnds : HasPathEnds data) :
    Fintype.card (Dart data) = 2 * Fintype.card (StablePath data) := by
  classical
  calc
    Fintype.card (Dart data) = ∑ r : StablePath data, Fintype.card {d : Dart data // row data d = r} :=
      (Fintype.card_congr (Equiv.sigmaFiberEquiv (row data)).symm).trans Fintype.card_sigma
    _ = 2 * Fintype.card (StablePath data) := by simp [card_row data hConnected hEnds, Nat.mul_comm]

theorem edgeCard_ofDatum (hConnected : data.Connected)
    (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3) (hEnds : HasPathEnds data) :
    (ofDatum data hConnected hTrivalent hEnds).edgeCard = Fintype.card (StablePath data) := by
  unfold CubicDartGraph.edgeCard
  rw [card_darts data hConnected hEnds]
  omega

theorem reach_pruned_of_surviving_walk {first second : data.SourceVertex}
    (h : Relation.ReflTransGen (SurvivingStep data) first second) :
    Reach (prunedSource data) first second := by
  induction h with
  | refl => exact reach_refl _ _
  | @tail a b _ hStep ih =>
    obtain ⟨edge, hEnds⟩ := hStep
    apply ih.tail
    unfold num_edges
    rw [Multiset.card_pos_iff_exists_mem]
    refine ⟨data.sourceEnds edge.1, Multiset.mem_filter.mpr ⟨?_, hEnds⟩⟩
    exact Multiset.mem_map.mpr ⟨edge.1, (mem_nonDanglingEdges data edge.1).mpr edge.2, rfl⟩

/-- The pruned source has one active component and its isolated vertices. -/
theorem componentCount_of_active (hConnected : data.Connected)
    (a : data.SourceVertex) (ha : nonDanglingValency data a ≠ 0) :
    componentCount (prunedSource data) = (isolatedVertices data).card + 1 := by
  classical
  let active := component (prunedSource data) a
  have hComponents : Finset.univ.image (component (prunedSource data)) =
      insert active ((isolatedVertices data).image fun v ↦ ({v} : Finset data.SourceVertex)) := by
    ext s
    constructor
    · intro hs
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hs
      by_cases hv : nonDanglingValency data v = 0
      · apply Finset.mem_insert_of_mem
        exact Finset.mem_image.mpr ⟨v, (mem_isolatedVertices data v).mpr hv,
          (component_prunedSource_eq_singleton data hv).symm⟩
      · apply Finset.mem_insert.mpr
        apply Or.inl
        exact (component_eq_of_reach (reach_pruned_of_surviving_walk data
          (surviving_walk data hConnected hv ha)))
    · intro hs
      rcases Finset.mem_insert.mp hs with h | h
      · exact h ▸ Finset.mem_image_of_mem _ (Finset.mem_univ a)
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h
        rw [← component_prunedSource_eq_singleton data ((mem_isolatedVertices data v).mp hv)]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ v)
  have hNot : active ∉ (isolatedVertices data).image (fun v ↦ ({v} : Finset data.SourceVertex)) := by
    intro h
    obtain ⟨v, hv, hEq⟩ := Finset.mem_image.mp h
    have hA : a ∈ active := self_mem_component (G := prunedSource data) a
    have hMem : a ∈ ({v} : Finset data.SourceVertex) := hEq.symm ▸ hA
    have hav := Finset.mem_singleton.mp hMem
    exact ha (hav.symm ▸ (mem_isolatedVertices data v).mp hv)
  unfold componentCount
  rw [hComponents, Finset.card_insert_of_notMem hNot, Finset.card_image_of_injective]
  exact Finset.singleton_injective

theorem exists_active_of_genus_pos (hConnected : data.Connected)
    (hGenus : 0 < genus data.sourceGraph) :
    ∃ v : data.SourceVertex, nonDanglingValency data v ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hEmpty : nonDanglingEdges data = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro edge he
    exact ClassInjectivity.nonDanglingValency_ne_zero_of_incident data
      ((mem_nonDanglingEdges data edge).mp he) (incident_left data edge)
      (h (data.sourceEnds edge).1)
  have hCount := card_nonDanglingEdges_eq data hConnected
  rw [hEmpty, Finset.card_empty, Nat.cast_zero] at hCount
  have hBound : componentCount (prunedSource data) ≤ Fintype.card data.SourceVertex :=
    (Finset.card_image_le).trans_eq (Finset.card_univ)
  omega

/-- The genus of the constructed cubic graph is the original source genus.
The positive-genus condition excludes an all-dangling tree, whose empty dart
model is allowed by the cubic structure but has its conventional genus one. -/
theorem genus_ofDatum (hConnected : data.Connected)
    (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3) (hEnds : HasPathEnds data)
    (hGenus : 0 < genus data.sourceGraph) :
    ((ofDatum data hConnected hTrivalent hEnds).genus : ℤ) = genus data.sourceGraph := by
  obtain ⟨a, ha⟩ := exists_active_of_genus_pos data hConnected hGenus
  have hComponents := componentCount_of_active data hConnected a ha
  have hEuler := card_stablePath_add_componentCount_eq data hConnected hEnds
  rw [cyclomatic_prunedSource_eq_genus_sourceGraph data hConnected, hComponents] at hEuler
  have hDartEuler := (ofDatum data hConnected hTrivalent hEnds).euler
  rw [edgeCard_ofDatum] at hDartEuler
  have hV : Fintype.card (BranchVertex data) = (stableVertices data).card :=
    (Fintype.card_congr (branchVertexEquivStableVertices data)).trans (Fintype.card_coe _)
  rw [hV] at hDartEuler
  omega

/-- The non-loop edge chosen by a Whitehead move has the exact source-side
simple end required to contract its row without contracting a cycle. -/
theorem hasSimpleEnd_of_not_isLoopDart (hConnected : data.Connected)
    (hTrivalent : ∀ v, nonDanglingValency data v ≤ 3) (hEnds : HasPathEnds data)
    (d : Dart data) (hNonloop : ¬ (ofDatum data hConnected hTrivalent hEnds).IsLoopDart d) :
    SingleRowForest.HasSimpleEnd data (row data d) := by
  apply SingleRowForest.hasSimpleEnd_of_distinct_ends hConnected hEnds (row data d)
    (vertex data d) (vertex data (opposite data hConnected hEnds d))
  · exact fun h ↦ hNonloop h.symm
  · exact (incidenceCount_pos_iff data _ _).mpr ⟨d.2.1, d.2.2, rfl⟩
  · exact (incidenceCount_pos_iff data _ _).mpr
      ⟨(opposite data hConnected hEnds d).2.1, (opposite data hConnected hEnds d).2.2,
        row_opposite data hConnected hEnds d⟩

end DraismaVargas.LocalCases.StableSourceDarts

