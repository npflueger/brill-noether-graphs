module

public import DraismaVargasMarkedCount.MarkedCountGeneral.TypedFrame
public import DraismaVargas.LocalCases.LeafFacetNoReturn

@[expose] public section

/-!
# The image of a type-0 mark (the summand count of the dimension formula, for typed frames)

The content of `Drop.typeZero_image`.

**The count.** For a typed frame, Part I's dimension formula
(`GluingDatum.dimensionCorrection_of_target_genus_zero`) and the typed saturation give
`Σ_x (ch(x) + val(x) − 3) = Σⱼ (aⱼ − 1)` (`sum_targetExcess_eq_typeExcess`). Write
`f(x) = Σ_{j : x_j = x} (aⱼ − 1)` for the share of the right side at `x`. Then
`f(x) ≤ ch(x) + val(x) − 3` at every target vertex (`fibre_le_targetExcess`):

* at a vertex with no mark over it, the summand is `≥ 0`: a leaf has change `≥ 2`, because its
  column would vanish otherwise (`markedNoDanglingTargetFibres`), and a divalent vertex has
  change `≥ 1`, because otherwise its two columns would be equal (`markedColumn_eq_of_divalent`:
  the two occurrences through one sheet are consecutive
  along a **marked** row as long as no mark lies over the vertex);
* at a vertex over which some mark of positive type lies, the summand is
  `≥ Σ_{positive} (aⱼ − 1)`: the change is at least `Σ r(u_j)`, with `r(u_j) ≥ aⱼ`, and
  `r(u_j) ≥ aⱼ + 1` over a leaf (where `r = val(u_j) − 2 + m(u_j)` and `m(u_j) ≥ aⱼ + 1`, the
  second clause of (D4′));
* at any vertex the summand is `≥ −1`, with equality only at a divalent vertex of change `0`.

Since both sides sum to the same number, `f(x)` equals the summand everywhere. At the image of a
type-`0` mark this forces: no mark of positive type over it, no second mark over it, and summand
`−1`, i.e. a divalent vertex of change `0`, so `r = 0` at every source vertex over it
(`typeZero_image'`). The marked cubic core is used only to know that the marks are distinct
source vertices and that the core has a slot (so the target has an edge).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 1.  Nonsingularity of the marked matrix: leaves and divalent vertices -/

section Columns

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}
  {marks : Finset data.SourceVertex} {coordinate : Type*} [Fintype coordinate]
  [DecidableEq coordinate]

/-- **No target fibre is entirely dangling** when the marked matrix is nonsingular: the column of
such a target edge vanishes. -/
theorem markedNoDanglingTargetFibres (labelling : MarkedLabelling data marks coordinate)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    NoDanglingTargetFibres data := by
  classical
  intro place
  by_contra hNone
  apply hDet
  refine Matrix.det_eq_zero_of_column_eq_zero (labelling.targetEdge.symm place) fun row ↦ ?_
  rw [MarkedLabelling.matrix_eq, Equiv.apply_symm_apply]
  unfold markedMatrix
  refine Finset.sum_eq_zero fun edge hEdge ↦ ?_
  obtain ⟨⟨hSurvives, -⟩, hTarget⟩ := (mem_markedOccurrences _ _ edge).mp hEdge
  exact absurd ⟨edge, hTarget, hSurvives⟩ hNone

/-- Over a divalent target vertex of change `0` with no mark over it, the two occurrences through
one sheet lie on one **marked** row. -/
theorem markedRow_sourceEdge_eq_of_divalent (hValid : data.Valid) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (hZero : data.targetChange vertex = 0)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex)
    (sheet : Fin degree) (hNoMark : data.sourceEndpoint vertex sheet ∉ marks)
    (hFirstSurvives : ¬ IsDangling data (data.sourceEdge first sheet))
    (hSecondSurvives : ¬ IsDangling data (data.sourceEdge second sheet)) :
    markedRow marks (⟨data.sourceEdge first sheet, hFirstSurvives⟩ : NonDanglingEdge data) =
      markedRow marks ⟨data.sourceEdge second sheet, hSecondSurvives⟩ := by
  classical
  apply markedRow_eq_of_markedConsecutive
  have hDegree := vertex_degree_eq_two_of_divalent_targetChange_zero data hValid
    vertex hDivalent hZero (data.sourceEndpoint vertex sheet) rfl
  have hFirstIncident :=
    incident_sourceEdge_sourceEndpoint data vertex first hFirst sheet
  have hSecondIncident :=
    incident_sourceEdge_sourceEndpoint data vertex second hSecond sheet
  have hEdgeNe := sourceEdge_ne_of_target_ne data hNe sheet sheet
  refine ⟨fun hEqual ↦ hEdgeNe (congrArg Subtype.val hEqual),
    data.sourceEndpoint vertex sheet, hFirstIncident, hSecondIncident, ?_, hNoMark⟩
  have hFilter :
      ((Finset.univ : Finset data.SourceEdge).filter fun edge ↦
        ¬ IsDangling data edge ∧
          Incident data edge (data.sourceEndpoint vertex sheet)) =
        {data.sourceEdge first sheet, data.sourceEdge second sheet} := by
    apply Finset.Subset.antisymm
    · intro edge hEdge
      have hProperty := (Finset.mem_filter.mp hEdge).2
      rcases eq_of_incident_of_vertex_degree_eq_two data hEdgeNe hFirstIncident
        hSecondIncident hDegree hProperty.2 with hCase | hCase
      · simp [hCase]
      · simp [hCase]
    · intro edge hEdge
      rcases Finset.mem_insert.mp hEdge with hCase | hCase
      · rw [hCase]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hFirstSurvives, hFirstIncident⟩
      · rw [Finset.mem_singleton.mp hCase]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSecondSurvives, hSecondIncident⟩
  unfold nonDanglingValency
  convert (congrArg Finset.card hFilter).trans (Finset.card_pair hEdgeNe)

/-- An occurrence is the canonical occurrence above its own target edge through its own sheet. -/
theorem sourceEdge_self' (edge : data.SourceEdge) : data.sourceEdge edge.1.1 edge.1.2 = edge :=
  Subtype.ext (Prod.ext rfl edge.2)

/-- **Equal columns at a divalent vertex of change `0`**: over a divalent target vertex of change
`0` with no mark over it, the two columns of the natural marked matrix agree. -/
theorem markedColumn_eq_of_divalent (hValid : data.Valid) (vertex : target.V)
    (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (hZero : data.targetChange vertex = 0)
    (hNoMark : ∀ v ∈ marks, v.1.1 ≠ vertex)
    {first second : target.edges} (hNe : first ≠ second)
    (hFirst : first ∈ GluingDatum.incidentEdges vertex)
    (hSecond : second ∈ GluingDatum.incidentEdges vertex)
    (path : MarkedStablePath data marks) :
    markedMatrix data marks path first = markedMatrix data marks path second := by
  classical
  have hTransfer : ∀ (one two : target.edges),
      one ∈ GluingDatum.incidentEdges vertex →
      two ∈ GluingDatum.incidentEdges vertex → one ≠ two →
      ∀ edge ∈ markedOccurrences data marks path one,
        data.sourceEdge two edge.1.2 ∈ markedOccurrences data marks path two := by
    intro one two hOne hTwo hOneTwo edge hEdge
    obtain ⟨⟨hSurvives, hRow⟩, hTarget⟩ := (mem_markedOccurrences _ _ edge).mp hEdge
    have hSelf : data.sourceEdge one edge.1.2 = edge := by
      rw [← hTarget]
      exact sourceEdge_self' edge
    have hOneSurvives : ¬ IsDangling data (data.sourceEdge one edge.1.2) := by
      rw [hSelf]
      exact hSurvives
    have hTwoSurvives : ¬ IsDangling data (data.sourceEdge two edge.1.2) :=
      fun hDangling ↦ hOneSurvives
        ((isDangling_sourceEdge_iff_of_divalent_targetChange_zero data hValid
          vertex hDivalent hZero hOneTwo hOne hTwo edge.1.2).2 hDangling)
    have hNotMark : data.sourceEndpoint vertex edge.1.2 ∉ marks :=
      fun hMem ↦ hNoMark _ hMem rfl
    have hRowEq := markedRow_sourceEdge_eq_of_divalent hValid vertex hDivalent hZero hOneTwo
      hOne hTwo edge.1.2 hNotMark hOneSurvives hTwoSurvives
    refine (mem_markedOccurrences _ _ _).mpr ⟨⟨hTwoSurvives, ?_⟩, rfl⟩
    rw [← hRowEq,
      show (⟨data.sourceEdge one edge.1.2, hOneSurvives⟩ : NonDanglingEdge data) =
        ⟨edge, hSurvives⟩ from Subtype.ext hSelf]
    exact hRow
  unfold markedMatrix
  refine Finset.sum_nbij' (fun edge ↦ data.sourceEdge second edge.1.2)
    (fun edge ↦ data.sourceEdge first edge.1.2)
    (hTransfer first second hFirst hSecond hNe)
    (hTransfer second first hSecond hFirst (Ne.symm hNe)) ?_ ?_ ?_
  · intro edge hEdge
    exact sourceEdge_transport_left_inverse data hValid vertex hDivalent hZero
      first second hFirst hSecond edge
      ((mem_markedOccurrences _ _ edge).mp hEdge).2
  · intro edge hEdge
    exact sourceEdge_transport_left_inverse data hValid vertex hDivalent hZero
      second first hSecond hFirst edge
      ((mem_markedOccurrences _ _ edge).mp hEdge).2
  · intro edge hEdge
    have hTarget := ((mem_markedOccurrences _ _ edge).mp hEdge).2
    have hSelf : data.sourceEdge first edge.1.2 = edge := by
      rw [← hTarget]
      exact sourceEdge_self' edge
    have hFirstIndex := sourceEdgeIndex_eq_of_divalent_targetChange_zero data
      hValid vertex hDivalent hZero first hFirst edge.1.2
    rw [hSelf] at hFirstIndex
    have hSecondIndex :
        data.sourceEdgeIndex (data.sourceEdge second edge.1.2) =
          (data.vertexPartition vertex).blockCard edge.1.2 :=
      sourceEdgeIndex_eq_of_divalent_targetChange_zero data hValid vertex
        hDivalent hZero second hSecond edge.1.2
    rw [hFirstIndex, hSecondIndex]

/-- **A divalent target vertex with no mark over it has positive change**, when the marked matrix
is nonsingular. -/
theorem markedDivalentChangePositive (labelling : MarkedLabelling data marks coordinate)
    (hValid : data.Valid)
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0)
    (vertex : target.V) (hDivalent : (GluingDatum.incidentEdges vertex).card = 2)
    (hNoMark : ∀ v ∈ marks, v.1.1 ≠ vertex) :
    1 ≤ data.targetChange vertex := by
  classical
  by_contra hNotPositive
  have hNonneg := data.targetChange_nonneg hValid vertex
  have hZero : data.targetChange vertex = 0 := by omega
  obtain ⟨first, second, hNe, hPair⟩ := Finset.card_eq_two.mp hDivalent
  have hFirst : first ∈ GluingDatum.incidentEdges vertex := by
    rw [hPair]; simp
  have hSecond : second ∈ GluingDatum.incidentEdges vertex := by
    rw [hPair]; simp
  apply hDet
  refine Matrix.det_zero_of_column_eq
    (i := labelling.targetEdge.symm first) (j := labelling.targetEdge.symm second)
    (fun hEqual ↦ hNe (labelling.targetEdge.symm.injective hEqual)) fun row ↦ ?_
  rw [MarkedLabelling.matrix_eq, MarkedLabelling.matrix_eq, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact markedColumn_eq_of_divalent hValid vertex hDivalent hZero hNoMark hNe hFirst hSecond _

end Columns

/-! ## 2.  The change as a sum over the source vertices -/

section Change

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-- **The change at `x` is the sum of `r` over the source vertices over `x`.** -/
theorem targetChange_eq_sum (vertex : target.V) :
    data.targetChange vertex =
      ∑ X ∈ Finset.univ.filter fun X : data.SourceVertex ↦ X.1.1 = vertex,
        markRamification data X := by
  classical
  unfold GluingDatum.targetChange
  refine Finset.sum_bij (fun b _ ↦ (⟨(vertex, b.1), b.2⟩ : data.SourceVertex)) ?_ ?_ ?_ ?_
  · intro b _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  · intro b _ b' _ h
    exact Subtype.ext (congrArg (fun X : data.SourceVertex ↦ X.1.2) h)
  · intro X hX
    have hX : X.1.1 = vertex := (Finset.mem_filter.mp hX).2
    refine ⟨⟨X.1.2, hX ▸ X.2⟩, Finset.mem_univ _, ?_⟩
    exact Subtype.ext (Prod.ext hX.symm rfl)
  · intro b _
    rfl

/-- At a vertex of change `0`, every source vertex over it has `r = 0`. -/
theorem markRamification_eq_zero_of_targetChange_zero (hValid : data.Valid)
    (X : data.SourceVertex) (hZero : data.targetChange X.1.1 = 0) :
    markRamification data X = 0 :=
  localRamification_eq_zero_of_targetChange_zero data hValid X.1.1 hZero ⟨X.1.2, X.2⟩

/-- **Over a leaf, `r = val − 2 + m`.** -/
theorem markRamification_of_leaf (X : data.SourceVertex)
    (hLeaf : (GluingDatum.incidentEdges X.1.1).card = 1) :
    markRamification data X =
      vertex_degree data.sourceGraph X - 2 + (markIndex data X : ℤ) := by
  have h := localRamification_eq_vertex_degree data X
  rw [hLeaf] at h
  change markRamification data X = _ at h
  rw [h]
  unfold markIndex
  push_cast
  ring

/-- The surviving valency is at most the graph degree. -/
theorem nonDanglingValency_le_vertex_degree (X : data.SourceVertex) :
    (nonDanglingValency data X : ℤ) ≤ vertex_degree data.sourceGraph X := by
  rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge]
  exact_mod_cast LeafFacetNoReturn.nonDanglingValency_le_card_incidentSourceEdge data X

end Change

/-! ## 3.  The summand count -/

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

namespace TypedFrame

variable (κ : TypedFrame core mark types degree)

/-- **The dimension formula for a typed frame**: `Σ_x (ch(x) + val(x) − 3) = Σⱼ (aⱼ − 1)`. -/
theorem sum_targetExcess_eq_typeExcess :
    ∑ x : κ.target.V, κ.data.targetExcess x = typeExcess types := by
  have hDim := κ.data.dimensionCorrection_of_target_genus_zero κ.fullDim.targetGenus
  have hSat := κ.fullDim.saturated
  linarith

/-- The marks are distinct source vertices. -/
theorem markSource_injective (hc : IsMarkedCubic core mark) :
    Function.Injective κ.markSource := by
  intro i j h
  apply hc.injective
  rw [← κ.ident.vertex_mark i, ← κ.ident.vertex_mark j]
  congr 1
  exact Subtype.ext h

/-- A typed frame over a marked cubic core with a mark has a nontrivial target. -/
theorem nontrivial_target (hc : IsMarkedCubic core mark) (j : Fin k) :
    Nontrivial κ.target.V := by
  have hp : 0 < p := by
    rcases Nat.eq_zero_or_pos p with hp | hp
    · subst hp
      have h := hc.mark_degree j
      simp [Core.incidenceDegree] at h
    · exact hp
  let e : κ.target.edges := κ.fullDim.labelling.targetEdge ⟨0, hp⟩
  have hMem : (e : κ.target.V × κ.target.V) ∈ κ.target.edges := Multiset.coe_mem
  refine ⟨⟨(e : κ.target.V × κ.target.V).1, (e : κ.target.V × κ.target.V).2, fun h ↦ ?_⟩⟩
  apply κ.target.loopless (e : κ.target.V × κ.target.V).1
  have hPair : ((e : κ.target.V × κ.target.V).1, (e : κ.target.V × κ.target.V).1) =
      (e : κ.target.V × κ.target.V) := Prod.ext rfl h
  rw [hPair]
  exact hMem

/-- The share of the type excess at the target vertex `x`. -/
def fibreExcess (x : κ.target.V) : ℤ :=
  ∑ i ∈ Finset.univ.filter fun i ↦ (κ.markSource i).1.1 = x, ((types i : ℤ) - 1)

theorem sum_fibreExcess : ∑ x, κ.fibreExcess x = typeExcess types := by
  unfold fibreExcess typeExcess
  exact Finset.sum_fiberwise Finset.univ (fun i ↦ (κ.markSource i).1.1) _

/-- **The general lower bound**: every summand is `≥ −1`, with equality only at a divalent vertex
of change `0`; and every summand at a vertex with no mark over it is `≥ 0`. -/
theorem targetExcess_ge (hc : IsMarkedCubic core mark) (j : Fin k) (x : κ.target.V) :
    -1 ≤ κ.data.targetExcess x ∧
      (κ.data.targetExcess x = -1 →
        (GluingDatum.incidentEdges x).card = 2 ∧ κ.data.targetChange x = 0) ∧
      ((∀ i, (κ.markSource i).1.1 ≠ x) → 0 ≤ κ.data.targetExcess x) := by
  have := κ.nontrivial_target hc j
  have hPos := incidentEdges_card_pos_of_connected κ.fullDim.targetConnected x
  have hChange := κ.data.targetChange_nonneg κ.fullDim.valid x
  have hNoDangling := markedNoDanglingTargetFibres κ.fullDim.labelling κ.fullDim.det_ne_zero
  unfold GluingDatum.targetExcess
  by_cases hLeaf : (GluingDatum.incidentEdges x).card = 1
  · have h2 := targetChange_ge_two_of_target_leaf κ.data κ.fullDim.valid hNoDangling x hLeaf
    refine ⟨by omega, fun h ↦ by omega, fun _ ↦ by omega⟩
  · by_cases hDiv : (GluingDatum.incidentEdges x).card = 2
    · refine ⟨by omega, fun h ↦ ⟨hDiv, by omega⟩, fun hNo ↦ ?_⟩
      have h1 := markedDivalentChangePositive κ.fullDim.labelling κ.fullDim.valid
        κ.fullDim.det_ne_zero x hDiv (by
          intro v hv
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hv
          exact hNo i)
      omega
    · refine ⟨by omega, fun h ↦ by omega, fun _ ↦ by omega⟩

/-- **The bound at a vertex carrying a mark of positive type**: the summand is at least
`Σ (aⱼ − 1)` over the positive-type marks over it. -/
theorem targetExcess_ge_positive (hc : IsMarkedCubic core mark) (j : Fin k) (x : κ.target.V)
    (hP : (Finset.univ.filter fun i ↦ (κ.markSource i).1.1 = x ∧ 0 < types i).Nonempty) :
    ∑ i ∈ Finset.univ.filter (fun i ↦ (κ.markSource i).1.1 = x ∧ 0 < types i),
        ((types i : ℤ) - 1) ≤ κ.data.targetExcess x := by
  classical
  set P := Finset.univ.filter fun i ↦ (κ.markSource i).1.1 = x ∧ 0 < types i with hPdef
  have := κ.nontrivial_target hc j
  have hValPos := incidentEdges_card_pos_of_connected κ.fullDim.targetConnected x
  have hInj := κ.markSource_injective hc
  have hMemP : ∀ i ∈ P, (κ.markSource i).1.1 = x ∧ 0 < types i := fun i hi ↦
    (Finset.mem_filter.mp hi).2
  -- the change is at least the sum of `r` over the positive-type marks over `x`
  have hChangeGe : ∑ i ∈ P, markRamification κ.data (κ.markSource i) ≤
      κ.data.targetChange x := by
    rw [targetChange_eq_sum, ← Finset.sum_image (fun i _ i' _ h ↦ hInj h)]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun X _ _ ↦
      markRamification_nonneg κ.fullDim.valid X
    intro X hX
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hX
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hMemP i hi).1⟩
  have hTyped : ∀ i ∈ P, (types i : ℤ) ≤ markRamification κ.data (κ.markSource i) :=
    fun i _ ↦ (κ.typed i).1
  have hCard : 1 ≤ P.card := Finset.card_pos.mpr hP
  unfold GluingDatum.targetExcess
  by_cases hLeaf : (GluingDatum.incidentEdges x).card = 1
  · -- over a leaf, `r(u) = val(u) − 2 + m(u) ≥ a + 1`
    have hLeafGe : ∀ i ∈ P, (types i : ℤ) + 1 ≤ markRamification κ.data (κ.markSource i) := by
      intro i hi
      have hx := (hMemP i hi).1
      have hLeaf' : (GluingDatum.incidentEdges (κ.markSource i).1.1).card = 1 := by
        rw [hx]; exact hLeaf
      rw [markRamification_of_leaf κ.data _ hLeaf']
      have hVal := κ.fullDim.markValency (κ.markSource i) (mem_markSet κ.markSource i)
      have hDeg := nonDanglingValency_le_vertex_degree κ.data (κ.markSource i)
      have hIndex := (κ.typed i).2
      rw [hVal] at hDeg
      push_cast at hDeg
      have : ((types i + 1 : ℕ) : ℤ) ≤ (markIndex κ.data (κ.markSource i) : ℤ) := by
        exact_mod_cast hIndex
      push_cast at this
      linarith
    have hSum : ∑ i ∈ P, ((types i : ℤ) + 1) ≤ κ.data.targetChange x :=
      (Finset.sum_le_sum hLeafGe).trans hChangeGe
    have hSplit : ∑ i ∈ P, ((types i : ℤ) + 1) = ∑ i ∈ P, ((types i : ℤ) - 1) + 2 * P.card := by
      rw [show (2 * P.card : ℤ) = ∑ _i ∈ P, (2 : ℤ) by simp [mul_comm]]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hLeaf]
    have : (1 : ℤ) ≤ P.card := by exact_mod_cast hCard
    push_cast
    linarith
  · have hSum : ∑ i ∈ P, (types i : ℤ) ≤ κ.data.targetChange x :=
      (Finset.sum_le_sum hTyped).trans hChangeGe
    have hSplit : ∑ i ∈ P, (types i : ℤ) = ∑ i ∈ P, ((types i : ℤ) - 1) + P.card := by
      rw [show (P.card : ℤ) = ∑ _i ∈ P, (1 : ℤ) by simp]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    have hVal2 : 2 ≤ (GluingDatum.incidentEdges x).card := by omega
    have : (1 : ℤ) ≤ P.card := by exact_mod_cast hCard
    have hVal2' : (2 : ℤ) ≤ ((GluingDatum.incidentEdges x).card : ℤ) := by exact_mod_cast hVal2
    linarith

/-- **The share is at most the summand**, everywhere; at a vertex carrying a type-`0` mark,
equality forces it to be the only mark there, over a divalent vertex of change `0`. -/
theorem fibreExcess_le (hc : IsMarkedCubic core mark) (j : Fin k) (x : κ.target.V) :
    κ.fibreExcess x ≤ κ.data.targetExcess x ∧
      (∀ i, (κ.markSource i).1.1 = x → types i = 0 →
        κ.fibreExcess x = κ.data.targetExcess x →
          (GluingDatum.incidentEdges x).card = 2 ∧ κ.data.targetChange x = 0 ∧
            ∀ i', (κ.markSource i').1.1 = x → i' = i) := by
  classical
  set I := Finset.univ.filter fun i ↦ (κ.markSource i).1.1 = x with hIdef
  have hSplit : κ.fibreExcess x =
      ∑ i ∈ Finset.univ.filter (fun i ↦ (κ.markSource i).1.1 = x ∧ 0 < types i),
        ((types i : ℤ) - 1) - (I.filter fun i ↦ ¬ 0 < types i).card := by
    unfold fibreExcess
    rw [← Finset.sum_filter_add_sum_filter_not I (fun i ↦ 0 < types i)]
    have hPos : I.filter (fun i ↦ 0 < types i) =
        Finset.univ.filter (fun i ↦ (κ.markSource i).1.1 = x ∧ 0 < types i) := by
      rw [hIdef, Finset.filter_filter]
    have hZeroSum : ∑ i ∈ I.filter (fun i ↦ ¬ 0 < types i), ((types i : ℤ) - 1) =
        -((I.filter fun i ↦ ¬ 0 < types i).card : ℤ) := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have h0 : types i = 0 := by
        have := (Finset.mem_filter.mp hi).2
        omega
      rw [h0]
      simp
    rw [hPos, hZeroSum]
    ring
  obtain ⟨hGe, hEq, hNoMark⟩ := κ.targetExcess_ge hc j x
  by_cases hP : (Finset.univ.filter fun i ↦ (κ.markSource i).1.1 = x ∧ 0 < types i).Nonempty
  · have hBound := κ.targetExcess_ge_positive hc j x hP
    refine ⟨by rw [hSplit]; omega, fun i hi hi0 hFib ↦ ?_⟩
    exfalso
    have hMem : i ∈ I.filter fun i ↦ ¬ 0 < types i :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, by omega⟩
    have hCard : 1 ≤ (I.filter fun i ↦ ¬ 0 < types i).card := Finset.card_pos.mpr ⟨i, hMem⟩
    rw [hSplit] at hFib
    have : (1 : ℤ) ≤ (I.filter fun i ↦ ¬ 0 < types i).card := by exact_mod_cast hCard
    omega
  · have hPempty : Finset.univ.filter (fun i ↦ (κ.markSource i).1.1 = x ∧ 0 < types i) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hP
    rw [hPempty, Finset.sum_empty, zero_sub] at hSplit
    have hAll : I.filter (fun i ↦ ¬ 0 < types i) = I := by
      refine Finset.filter_true_of_mem fun i hi ↦ fun hpos ↦ hP ⟨i, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2, hpos⟩
    rw [hAll] at hSplit
    by_cases hI : I.Nonempty
    · have hCard : 1 ≤ I.card := Finset.card_pos.mpr hI
      refine ⟨by rw [hSplit]; omega, fun i hi _ hFib ↦ ?_⟩
      rw [hSplit] at hFib
      have hCard1 : I.card = 1 := by omega
      have hm1 : κ.data.targetExcess x = -1 := by rw [← hFib, hCard1]; rfl
      obtain ⟨hDiv, hZero⟩ := hEq hm1
      refine ⟨hDiv, hZero, fun i' hi' ↦ ?_⟩
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hCard1
      have h1 : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      have h2 : i' ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi'⟩
      rw [ha, Finset.mem_singleton] at h1 h2
      rw [h1, h2]
    · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
      rw [hIempty, Finset.card_empty] at hSplit
      have hNo : ∀ i, (κ.markSource i).1.1 ≠ x := by
        intro i hi
        have : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
        rw [hIempty] at this
        exact Finset.notMem_empty i this
      refine ⟨by rw [hSplit]; simpa using hNoMark hNo, fun i hi ↦ absurd hi (hNo i)⟩

/-- **The share equals the summand at every target vertex** (both sum to `Σ (aⱼ − 1)`). -/
theorem fibreExcess_eq (hc : IsMarkedCubic core mark) (j : Fin k) (x : κ.target.V) :
    κ.fibreExcess x = κ.data.targetExcess x := by
  have hLe : ∀ y ∈ (Finset.univ : Finset κ.target.V),
      κ.fibreExcess y ≤ κ.data.targetExcess y := fun y _ ↦ (κ.fibreExcess_le hc j y).1
  have hSum : ∑ y, κ.fibreExcess y = ∑ y, κ.data.targetExcess y := by
    rw [sum_fibreExcess, sum_targetExcess_eq_typeExcess]
  exact (Finset.sum_eq_sum_iff_of_le hLe).mp hSum x (Finset.mem_univ x)

end TypedFrame

/-- **The image of a type-`0` mark** (the summand count), in its strong form:
it is a divalent target vertex of change `0`, every source vertex over it has `r = 0`, and no
other mark lies over it. -/
theorem typeZero_image' (hc : IsMarkedCubic core mark) (κ : TypedFrame core mark types degree)
    (j : Fin k) (hj : types j = 0) :
    (GluingDatum.incidentEdges (κ.markSource j).1.1).card = 2 ∧
      κ.data.targetChange (κ.markSource j).1.1 = 0 ∧
      (∀ X : κ.data.SourceVertex, X.1.1 = (κ.markSource j).1.1 →
        markRamification κ.data X = 0) ∧
      ∀ i, (κ.markSource i).1.1 = (κ.markSource j).1.1 → i = j := by
  obtain ⟨hDiv, hZero, hOnly⟩ :=
    (κ.fibreExcess_le hc j _).2 j rfl hj (κ.fibreExcess_eq hc j _)
  refine ⟨hDiv, hZero, fun X hX ↦ ?_, hOnly⟩
  apply markRamification_eq_zero_of_targetChange_zero κ.data κ.fullDim.valid
  rw [hX]
  exact hZero

end DraismaVargas.Count.MarkedCountGeneral
