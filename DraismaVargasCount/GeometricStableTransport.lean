module

public import DraismaVargasCount.GeometricTransport

@[expose] public section

/-!
# Geometric transport of the stable source and its matrix

The orientation-independent occurrence dictionary descends through pruning and
stable-path contraction and preserves every natural matrix entry and branch
incidence multiplicity. The induced dictionaries are functorial. The proofs
reuse the strict transport constructions with unordered dangling-side transport;
this module does not change any fibre or star quotient.
-/

namespace DraismaVargas.Count.GeometricDatumIso

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open Utilities Utilities.Certificate

variable {target₁ target₂ target₃ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
  {third : GluingDatum target₃ degree}

/-- Pruning depends only on unordered endpoint incidences. -/
theorem isDangling_map_iff (iso : GeometricDatumIso first second) (hConnected : first.Connected)
    (edge : first.SourceEdge) :
    IsDangling second (iso.sourceEdgeEquiv edge) ↔ IsDangling first edge := by
  constructor
  · intro hDangling
    exact TargetRelabelPruning.isDangling_map_unordered
      iso.sourceGraphLaplacianEquiv.symm hConnected
      (iso.sourceEdgeEquiv edge) edge (iso.sourceEnds_map edge).symm hDangling
  · exact TargetRelabelPruning.isDangling_map_unordered
      iso.sourceGraphLaplacianEquiv (iso.connected hConnected)
      edge (iso.sourceEdgeEquiv edge) (iso.sourceEnds_map edge)

/-- Surviving occurrences correspond. -/
noncomputable def nonDanglingEdgeEquiv (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) :
    NonDanglingEdge first ≃ NonDanglingEdge second :=
  iso.sourceEdgeEquiv.subtypeEquiv fun edge ↦
    not_congr (iso.isDangling_map_iff hConnected edge).symm

@[simp] theorem nonDanglingEdgeEquiv_val (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) (edge : NonDanglingEdge first) :
    (iso.nonDanglingEdgeEquiv hConnected edge).1 = iso.sourceEdgeEquiv edge.1 := rfl

theorem nonDanglingIncident_map (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) (vertex : first.SourceVertex) :
    nonDanglingIncident second (iso.sourceVertexEquiv vertex) =
      (nonDanglingIncident first vertex).image iso.sourceEdgeEquiv := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := iso.sourceEdgeEquiv.surjective edge
  rw [mem_nonDanglingIncident, iso.isDangling_map_iff hConnected,
    iso.incident_map_iff]
  simp only [Finset.mem_image, Equiv.apply_eq_iff_eq, exists_eq_right,
    mem_nonDanglingIncident]

/-- Surviving valency is preserved. -/
theorem nonDanglingValency_map (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) (vertex : first.SourceVertex) :
    nonDanglingValency second (iso.sourceVertexEquiv vertex) =
      nonDanglingValency first vertex := by
  rw [← card_nonDanglingIncident, iso.nonDanglingIncident_map hConnected,
    Finset.card_image_of_injective _ iso.sourceEdgeEquiv.injective,
    card_nonDanglingIncident]

/-- Consecutive occurrences correspond to consecutive occurrences. -/
theorem consecutive_map_iff (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) (left right : NonDanglingEdge first) :
    Consecutive second (iso.nonDanglingEdgeEquiv hConnected left)
        (iso.nonDanglingEdgeEquiv hConnected right) ↔
      Consecutive first left right := by
  constructor
  · rintro ⟨hNe, vertex, hLeft, hRight, hValency⟩
    obtain ⟨vertex, rfl⟩ := iso.sourceVertexEquiv.surjective vertex
    refine ⟨fun h ↦ hNe (congrArg (iso.nonDanglingEdgeEquiv hConnected) h),
      vertex, ?_, ?_, ?_⟩
    · exact (iso.incident_map_iff left.1 vertex).mp hLeft
    · exact (iso.incident_map_iff right.1 vertex).mp hRight
    · rwa [iso.nonDanglingValency_map hConnected] at hValency
  · rintro ⟨hNe, vertex, hLeft, hRight, hValency⟩
    refine ⟨(iso.nonDanglingEdgeEquiv hConnected).injective.ne hNe,
      iso.sourceVertexEquiv vertex, ?_, ?_, ?_⟩
    · exact (iso.incident_map_iff left.1 vertex).mpr hLeft
    · exact (iso.incident_map_iff right.1 vertex).mpr hRight
    · rwa [iso.nonDanglingValency_map hConnected]

/-- **The induced dictionary of stable paths**, descended from the literal
occurrence bijection rather than chosen from a cardinality. -/
noncomputable def stablePathEquiv (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) : StablePath first ≃ StablePath second :=
  Quot.congr (iso.nonDanglingEdgeEquiv hConnected)
    fun left right ↦ (iso.consecutive_map_iff hConnected left right).symm

theorem stablePathEquiv_mk (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) (edge : NonDanglingEdge first) :
    iso.stablePathEquiv hConnected edge.stablePath =
      (iso.nonDanglingEdgeEquiv hConnected edge).stablePath := rfl

theorem danglingEdgeNoGlue_map (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) (hNoGlue : DanglingEdgeNoGlue first) :
    DanglingEdgeNoGlue second := by
  intro edge hDangling
  obtain ⟨edge, rfl⟩ := iso.sourceEdgeEquiv.surjective edge
  rw [iso.sourceEdgeIndex_map]
  exact hNoGlue edge ((iso.isDangling_map_iff hConnected edge).mp hDangling)

/-- Row-filtered occurrence sets correspond. -/
theorem occurrences_map (iso : GeometricDatumIso first second) (hConnected : first.Connected)
    (path : StablePath first) (place : target₁.edges) :
    StableSourceMatrix.occurrences second (iso.stablePathEquiv hConnected path)
        (iso.targetEdge place) =
      (StableSourceMatrix.occurrences first path place).image iso.sourceEdgeEquiv := by
  classical
  ext edge
  obtain ⟨edge, rfl⟩ := iso.sourceEdgeEquiv.surjective edge
  rw [StableSourceMatrix.mem_occurrences]
  constructor
  · rintro ⟨⟨hSurvives, hRow⟩, hTarget⟩
    have hOld : ¬ IsDangling first edge := fun h ↦ hSurvives
      ((iso.isDangling_map_iff hConnected edge).mpr h)
    have hOldTarget : edge.1.1 = place := iso.targetEdge.injective hTarget
    apply Finset.mem_image.mpr
    refine ⟨edge, (StableSourceMatrix.mem_occurrences _ _ _).mpr ⟨⟨hOld, ?_⟩, hOldTarget⟩, rfl⟩
    apply (iso.stablePathEquiv hConnected).injective
    exact (iso.stablePathEquiv_mk hConnected ⟨edge, hOld⟩).trans hRow
  · intro hMem
    obtain ⟨old, hOld, hEqual⟩ := Finset.mem_image.mp hMem
    have hEq : old = edge := iso.sourceEdgeEquiv.injective hEqual
    subst hEq
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (StableSourceMatrix.mem_occurrences _ _ _).mp hOld
    have hNew : ¬ IsDangling second (iso.sourceEdgeEquiv old) := fun h ↦
      hSurvives ((iso.isDangling_map_iff hConnected old).mp h)
    refine ⟨⟨hNew, ?_⟩, congrArg iso.targetEdge hTarget⟩
    exact (iso.stablePathEquiv_mk hConnected ⟨old, hSurvives⟩).symm.trans
      (congrArg (iso.stablePathEquiv hConnected) hRow)

/-- **Every entry of the natural stable-source matrix is preserved.** -/
theorem matrix_map (iso : GeometricDatumIso first second) (hConnected : first.Connected)
    (path : StablePath first) (place : target₁.edges) :
    StableSourceMatrix.matrix second (iso.stablePathEquiv hConnected path)
        (iso.targetEdge place) =
      StableSourceMatrix.matrix first path place := by
  classical
  unfold StableSourceMatrix.matrix
  rw [iso.occurrences_map hConnected, Finset.sum_image]
  · exact Finset.sum_congr rfl fun edge _ ↦ by rw [iso.sourceEdgeIndex_map]
  · exact fun _ _ _ _ h ↦ iso.sourceEdgeEquiv.injective h

/-- **The induced dictionary of branch vertices.** -/
noncomputable def branchVertexEquiv (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) :
    StableGraphIncidence.BranchVertex first ≃ StableGraphIncidence.BranchVertex second :=
  iso.sourceVertexEquiv.subtypeEquiv fun vertex ↦ by
    rw [iso.nonDanglingValency_map hConnected]

/-- **Every incidence multiplicity is preserved**, counted with flags, so a
stable loop keeps its two incidences at one branch vertex. -/
theorem incidenceCount_map (iso : GeometricDatumIso first second) (hConnected : first.Connected)
    (vertex : first.SourceVertex) (path : StablePath first) :
    StablePathCount.incidenceCount first vertex path =
      StablePathCount.incidenceCount second (iso.sourceVertexEquiv vertex)
        (iso.stablePathEquiv hConnected path) := by
  classical
  unfold StablePathCount.incidenceCount
  apply Finset.card_bij (fun edge _ ↦ iso.nonDanglingEdgeEquiv hConnected edge)
  · intro edge hEdge
    simp only [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hEdge ⊢
    refine ⟨(iso.incident_map_iff edge.1 vertex).mpr hEdge.1, ?_⟩
    rw [← iso.stablePathEquiv_mk hConnected, hEdge.2]
  · intro left _ right _ hEq
    exact (iso.nonDanglingEdgeEquiv hConnected).injective hEq
  · intro edge hEdge
    obtain ⟨oldEdge, rfl⟩ := (iso.nonDanglingEdgeEquiv hConnected).surjective edge
    refine ⟨oldEdge, ?_, rfl⟩
    simp only [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hEdge ⊢
    refine ⟨(iso.incident_map_iff oldEdge.1 vertex).mp hEdge.1, ?_⟩
    apply (iso.stablePathEquiv hConnected).injective
    rw [iso.stablePathEquiv_mk hConnected]
    exact hEdge.2

/-- **The stable dictionary of the fibre's isomorphisms is constructed** from the
isomorphism of gluing data rather than carried as data. -/
noncomputable def graphEquivalence (iso : GeometricDatumIso first second)
    (hConnected : first.Connected) :
    StableGraphIncidence.Equivalence first second where
  vertex := iso.branchVertexEquiv hConnected
  row := iso.stablePathEquiv hConnected
  incidence vertex path := iso.incidenceCount_map hConnected vertex.1 path

/-! ### Functoriality of the induced stable dictionary

`branchVertexEquiv` and `stablePathEquiv` above are the literal occurrence
bijection -- an `Equiv.subtypeEquiv` of a bijection of pairs, and
`Quot.congr` of that -- but nothing above records how they compose.  The six
identities below are exactly what `MemberIso.refl`, `.symm` and `.trans`
(`Count.Fibre`) need to build the induced dictionary functorially;
`Equiv.ext` reduces each to a definitional unfolding, the stable-path ones
after one `Quot.ind`. -/

theorem branchVertexEquiv_refl (data : GluingDatum target₁ degree)
    (hConnected : data.Connected) :
    (GeometricDatumIso.refl data).branchVertexEquiv hConnected =
      Equiv.refl (StableGraphIncidence.BranchVertex data) :=
  Equiv.ext fun _ ↦ rfl

theorem stablePathEquiv_refl (data : GluingDatum target₁ degree)
    (hConnected : data.Connected) :
    (GeometricDatumIso.refl data).stablePathEquiv hConnected = Equiv.refl (StablePath data) := by
  refine Equiv.ext ?_
  refine Quot.ind ?_
  intro _
  rfl

theorem branchVertexEquiv_symm (iso : GeometricDatumIso first second)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    iso.symm.branchVertexEquiv hSecond = (iso.branchVertexEquiv hFirst).symm :=
  Equiv.ext fun _ ↦ rfl

theorem stablePathEquiv_symm (iso : GeometricDatumIso first second)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    iso.symm.stablePathEquiv hSecond = (iso.stablePathEquiv hFirst).symm := by
  refine Equiv.ext ?_
  refine Quot.ind ?_
  intro _
  rfl

theorem branchVertexEquiv_trans (left : GeometricDatumIso first second)
    (right : GeometricDatumIso second third)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    (left.trans right).branchVertexEquiv hFirst =
      (left.branchVertexEquiv hFirst).trans (right.branchVertexEquiv hSecond) :=
  Equiv.ext fun _ ↦ rfl

theorem stablePathEquiv_trans (left : GeometricDatumIso first second)
    (right : GeometricDatumIso second third)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    (left.trans right).stablePathEquiv hFirst =
      (left.stablePathEquiv hFirst).trans (right.stablePathEquiv hSecond) := by
  refine Equiv.ext ?_
  refine Quot.ind ?_
  intro _
  rfl

theorem hasPathEnds_map (iso : GeometricDatumIso first second) (hConnected : first.Connected)
    (hEnds : HasPathEnds first) : HasPathEnds second :=
  (iso.graphEquivalence hConnected).hasPathEnds hConnected hEnds

/-- Trivalence of the stable graph is preserved. -/
theorem trivalent_map (iso : GeometricDatumIso first second) (hConnected : first.Connected)
    (hTrivalent : ∀ vertex : first.SourceVertex, nonDanglingValency first vertex ≤ 3)
    (vertex : second.SourceVertex) : nonDanglingValency second vertex ≤ 3 := by
  obtain ⟨vertex, rfl⟩ := iso.sourceVertexEquiv.surjective vertex
  rw [iso.nonDanglingValency_map hConnected]
  exact hTrivalent vertex


/-! ### Agreement with the established strict dictionary -/

theorem sourceVertexEquiv_ofStrict (iso : Transport.DatumIso first second) :
    (ofStrict iso).sourceVertexEquiv = iso.sourceVertexEquiv := rfl

theorem sourceEdgeEquiv_ofStrict (iso : Transport.DatumIso first second) :
    (ofStrict iso).sourceEdgeEquiv = iso.sourceEdgeEquiv := rfl

theorem branchVertexEquiv_ofStrict (iso : Transport.DatumIso first second)
    (hConnected : first.Connected) :
    (ofStrict iso).branchVertexEquiv hConnected = iso.branchVertexEquiv hConnected := rfl

theorem stablePathEquiv_ofStrict (iso : Transport.DatumIso first second)
    (hConnected : first.Connected) :
    (ofStrict iso).stablePathEquiv hConnected = iso.stablePathEquiv hConnected := rfl

theorem graphEquivalence_ofStrict (iso : Transport.DatumIso first second)
    (hConnected : first.Connected) :
    (ofStrict iso).graphEquivalence hConnected = iso.graphEquivalence hConnected := rfl

/-! ### Agreement with the actual geometric target-transport dictionary -/

theorem sourceVertexEquiv_ofTargetIso (φ : CFGraphIso target₁ target₂)
    (data : GluingDatum target₁ degree) :
    (ofTargetIso φ data).sourceVertexEquiv = TargetRelabelPruning.sourceVertexEquiv φ data :=
  Equiv.ext fun _ ↦ rfl

theorem sourceEdgeEquiv_ofTargetIso (φ : CFGraphIso target₁ target₂)
    (data : GluingDatum target₁ degree) :
    (ofTargetIso φ data).sourceEdgeEquiv = TargetRelabelPruning.sourceEdgeEquiv φ data :=
  Equiv.ext fun _ ↦ rfl

theorem branchVertexEquiv_ofTargetIso (φ : CFGraphIso target₁ target₂)
    (data : GluingDatum target₁ degree) (hConnected : data.Connected) :
    (ofTargetIso φ data).branchVertexEquiv hConnected =
      TargetRelabelStable.branchVertexEquiv φ data hConnected :=
  Equiv.ext fun _ ↦ rfl

theorem stablePathEquiv_ofTargetIso (φ : CFGraphIso target₁ target₂)
    (data : GluingDatum target₁ degree) (hConnected : data.Connected) :
    (ofTargetIso φ data).stablePathEquiv hConnected =
      TargetRelabelStable.stablePathEquiv φ data hConnected := by
  refine Equiv.ext ?_
  refine Quot.ind ?_
  intro _
  rfl

theorem graphEquivalence_ofTargetIso (φ : CFGraphIso target₁ target₂)
    (data : GluingDatum target₁ degree) (hConnected : data.Connected) :
    (ofTargetIso φ data).graphEquivalence hConnected =
      TargetRelabelStable.graphEquivalence φ data hConnected := by
  unfold graphEquivalence TargetRelabelStable.graphEquivalence
  congr 1
  · exact branchVertexEquiv_ofTargetIso φ data hConnected
  · exact stablePathEquiv_ofTargetIso φ data hConnected

end DraismaVargas.Count.GeometricDatumIso
