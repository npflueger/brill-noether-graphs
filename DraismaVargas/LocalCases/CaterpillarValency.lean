import DraismaVargas.LocalCases.CaterpillarSpine

/-!
# The pruned caterpillar source valencies

This file reads the leaf, stem and spine occurrence censuses back at source
vertices.  Singleton sheet vertices are entirely contained in dangling trees;
the central quotient vertices have surviving valency two at loop folds and
three at every attachment or spine junction.
-/

namespace DraismaVargas.LocalCases.CaterpillarValency

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.CaterpillarPruning
open DraismaVargas.LocalCases.CaterpillarSpine

/-! ## Singleton source vertices -/

theorem sourceEdge_eq_of_incident_sourceEndpoint_other
    {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
    (vertex : target.V) (sheet : Fin degree)
    (hBlock : (data.vertexPartition vertex).block sheet = {sheet})
    (edge : data.SourceEdge)
    (hIncident : Incident data edge (data.sourceEndpoint vertex sheet)) :
    edge = data.sourceEdge edge.1.1 sheet := by
  have hData := (incident_iff_target_mem_and_rel data edge
    (data.sourceEndpoint vertex sheet)).mp hIncident
  have hSheetMem : edge.1.2 ∈ (data.vertexPartition vertex).block sheet :=
    (SheetPartition.mem_block_iff _ _ _).mpr (by
      simpa only [GluingDatum.sourceEndpoint, SheetPartition.Rel,
        (data.vertexPartition vertex).repr_idem] using hData.2)
  rw [hBlock, Finset.mem_singleton] at hSheetMem
  calc
    edge = data.sourceEdge edge.1.1 edge.1.2 :=
      (DraismaVargas.LocalCases.W4StableSource.GluingDatum.sourceEdge_self
        data edge).symm
    _ = data.sourceEdge edge.1.1 sheet := congrArg _ hSheetMem

theorem partnerSheet_eq_pairIndex_of_incident
    {m : ℕ} {i : Fin (6 * m + 3)} {v : (catTree m).V}
    (hIncident : occ m i ∈ GluingDatum.incidentEdges v)
    (hPair : pairIndex (parentIndex (i.val + 1)) = pairIndex (i.val + 1)) :
    (partnerSheet m i).val = pairIndex v.val := by
  have hi := (mem_incidentEdges_occ m v i).mp hIncident
  rw [mem_incidentIndices] at hi
  simp only [partnerSheet_val]
  rcases hi with hi | hi
  · rw [← hi, hPair]
  · rw [← hi]

theorem local_spine_index_pairIndex {m : ℕ} (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) :
    pairIndex ((spineIndex m (localSpineQ m s)).val + 1) = s.val :=
  pairIndex_localSpine s hs0

theorem sourceEdge_occ_isDangling_of_incident_other
    {m : ℕ} {v : (catTree m).V} (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPair : s.val ≠ pairIndex v.val)
    (i : Fin (6 * m + 3))
    (hIncident : occ m i ∈ GluingDatum.incidentEdges v) :
    IsDangling (caterpillarDatum m)
      ((caterpillarDatum m).sourceEdge (occ m i) s) := by
  have hResidues : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by
    omega
  rcases hResidues with hLeaf | hSpine | hStemResidue
  · have hLeafClass : IsLeafEdge m i := Or.inl hLeaf
    apply (leafOccurrence_isDangling_iff hLeafClass s).mpr
    refine ⟨hs0, ?_⟩
    have hPair := pairIndex_parent_eq_of_leaf hLeafClass
    rw [partnerSheet_eq_pairIndex_of_incident hIncident hPair]
    exact hsPair
  · have hSpineClass : IsSpineEdge i := hSpine
    apply (spineOccurrence_isDangling_iff hSpineClass s).mpr
    refine ⟨hs0, ?_⟩
    intro hiLocal
    have hiEq : i = spineIndex m (localSpineQ m s) := by
      apply Fin.ext
      simp only [spineIndex_val, localSpineQ_val, localSpinePosition]
      omega
    subst i
    have hPair := pairIndex_parent m
      (spineIndex m (localSpineQ m s)).val (localSpine_isPair s)
    have hAtVertex := partnerSheet_eq_pairIndex_of_incident hIncident hPair
    rw [partnerSheet_val, local_spine_index_pairIndex s hs0] at hAtVertex
    exact hsPair hAtVertex
  · by_cases hLast : i.val = 6 * m + 2
    · have hLeafClass : IsLeafEdge m i := Or.inr hLast
      apply (leafOccurrence_isDangling_iff hLeafClass s).mpr
      refine ⟨hs0, ?_⟩
      have hPair := pairIndex_parent_eq_of_leaf hLeafClass
      rw [partnerSheet_eq_pairIndex_of_incident hIncident hPair]
      exact hsPair
    · have hStemClass : IsStemEdge m i := ⟨hStemResidue, hLast⟩
      apply (stemOccurrence_isDangling_iff hStemClass s).mpr
      refine ⟨hs0, ?_⟩
      have hPair := pairIndex_parent m i.val (pair_of_stem hStemClass)
      rw [partnerSheet_eq_pairIndex_of_incident hIncident hPair]
      exact hsPair

theorem nonDanglingValency_sourceEndpoint_other_eq_zero
    (m : ℕ) (v : (catTree m).V) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPair : s.val ≠ pairIndex v.val) :
    nonDanglingValency (caterpillarDatum m)
      ((caterpillarDatum m).sourceEndpoint v s) = 0 := by
  classical
  unfold nonDanglingValency
  rw [Finset.card_eq_zero]
  ext edge
  constructor
  · intro hEdge
    have hFilter := (Finset.mem_filter.mp hEdge).2
    have hBlock : ((caterpillarDatum m).vertexPartition v).block s = {s} := by
      rw [caterpillarDatum_vertexPartition, catVertexPart]
      exact CaterpillarSpine.block_pairPart_other m _ s hs0 hsPair
    have hEdgeEq := sourceEdge_eq_of_incident_sourceEndpoint_other
      (caterpillarDatum m) v s hBlock edge hFilter.2
    obtain ⟨i, hi⟩ := occ_surj m edge.1.1
    have hTargetIncident :=
      (incident_iff_target_mem_and_rel (caterpillarDatum m) edge
        ((caterpillarDatum m).sourceEndpoint v s)).mp hFilter.2
    have hTargetIncident' : edge.1.1 ∈ GluingDatum.incidentEdges v := by
      simpa only [GluingDatum.sourceEndpoint] using hTargetIncident.1
    have hDangling : IsDangling (caterpillarDatum m)
        ((caterpillarDatum m).sourceEdge (occ m i) s) := by
      apply sourceEdge_occ_isDangling_of_incident_other s hs0 hsPair i
      simpa only [hi] using hTargetIncident'
    exfalso
    apply hFilter.1
    rw [hEdgeEq, hi]
    exact hDangling
  · intro hEmpty
    simp at hEmpty

/-! ## Every surviving occurrence is one of the visible core occurrences -/

theorem stemOccurrence_partner_eq_main {m : ℕ}
    {i : Fin (6 * m + 3)} (hStem : IsStemEdge m i) :
    stemOccurrence m i (partnerSheet m i) = stemOccurrence m i 0 := by
  unfold stemOccurrence
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change ((caterpillarDatum m).edgePartition (occ m i)).Rel
    (partnerSheet m i) 0
  rw [caterpillarDatum_edgePartition,
    catEdgePart_of_pair m i (pair_of_stem hStem)]
  exact pairPart_rel_zero m _ _ rfl

/-- A surviving actual occurrence is visibly one of the two loop flags, the
unique paired stem occurrence, or the unique central spine occurrence. -/
theorem surviving_sourceEdge_classification {m : ℕ}
    (edge : (caterpillarDatum m).SourceEdge)
    (hSurvives : ¬ IsDangling (caterpillarDatum m) edge) :
    ∃ i : Fin (6 * m + 3), edge.1.1 = occ m i ∧
      ((IsLeafEdge m i ∧ (edge = loopFirst m i ∨ edge = loopSecond m i)) ∨
        (IsStemEdge m i ∧ edge = stemOccurrence m i 0) ∨
        (IsSpineEdge i ∧ edge = spineOccurrence m i 0)) := by
  obtain ⟨i, hi⟩ := occ_surj m edge.1.1
  let s : Fin (m + 2) := edge.1.2
  have hEdge : edge = (caterpillarDatum m).sourceEdge (occ m i) s := by
    calc
      edge = (caterpillarDatum m).sourceEdge edge.1.1 edge.1.2 :=
        (DraismaVargas.LocalCases.W4StableSource.GluingDatum.sourceEdge_self
          (caterpillarDatum m) edge).symm
      _ = (caterpillarDatum m).sourceEdge (occ m i) s := by rw [hi]
  refine ⟨i, hi, ?_⟩
  have hResidues : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by
    omega
  rcases hResidues with hLeaf | hSpine | hStemResidue
  · have hLeafClass : IsLeafEdge m i := Or.inl hLeaf
    left
    refine ⟨hLeafClass, ?_⟩
    have hNot := (not_congr (leafOccurrence_isDangling_iff hLeafClass s)).mp (by
      simpa only [leafOccurrence, hEdge] using hSurvives)
    by_cases hs0 : s.val = 0
    · left
      have hs : s = 0 := Fin.ext hs0
      simpa [loopFirst, leafOccurrence, hs] using hEdge
    · right
      have hsPartner : s.val = (partnerSheet m i).val := by omega
      have hs : s = partnerSheet m i := Fin.ext hsPartner
      simpa [loopSecond, leafOccurrence, hs] using hEdge
  · right; right
    have hSpineClass : IsSpineEdge i := hSpine
    refine ⟨hSpineClass, ?_⟩
    have hNot := (not_congr (spineOccurrence_isDangling_iff hSpineClass s)).mp (by
      simpa only [spineOccurrence, hEdge] using hSurvives)
    by_cases hs0 : s.val = 0
    · have hs : s = 0 := Fin.ext hs0
      simpa only [spineOccurrence, hs] using hEdge
    · have hiLocal : i.val = 6 * (s.val - 1) + 1 := by omega
      have hiEq : i = spineIndex m (localSpineQ m s) := by
        apply Fin.ext
        simp only [spineIndex_val, localSpineQ_val, localSpinePosition]
        omega
      subst i
      rw [hEdge]
      change spineOccurrence m (spineIndex m (localSpineQ m s)) s =
        spineOccurrence m (spineIndex m (localSpineQ m s)) 0
      exact localSpineOccurrence_eq_main s hs0
  · by_cases hLast : i.val = 6 * m + 2
    · have hLeafClass : IsLeafEdge m i := Or.inr hLast
      left
      refine ⟨hLeafClass, ?_⟩
      have hNot := (not_congr (leafOccurrence_isDangling_iff hLeafClass s)).mp (by
        simpa only [leafOccurrence, hEdge] using hSurvives)
      by_cases hs0 : s.val = 0
      · left
        have hs : s = 0 := Fin.ext hs0
        simpa [loopFirst, leafOccurrence, hs] using hEdge
      · right
        have hsPartner : s.val = (partnerSheet m i).val := by omega
        have hs : s = partnerSheet m i := Fin.ext hsPartner
        simpa [loopSecond, leafOccurrence, hs] using hEdge
    · right; left
      have hStemClass : IsStemEdge m i := ⟨hStemResidue, hLast⟩
      refine ⟨hStemClass, ?_⟩
      have hNot := (not_congr (stemOccurrence_isDangling_iff hStemClass s)).mp (by
        simpa only [stemOccurrence, hEdge] using hSurvives)
      by_cases hs0 : s.val = 0
      · have hs : s = 0 := Fin.ext hs0
        simpa only [stemOccurrence, hs] using hEdge
      · have hsPartner : s.val = (partnerSheet m i).val := by omega
        have hs : s = partnerSheet m i := Fin.ext hsPartner
        rw [hEdge, hs]
        change stemOccurrence m i (partnerSheet m i) = stemOccurrence m i 0
        exact stemOccurrence_partner_eq_main hStemClass

/-! ## The visible core stars -/

theorem loopFirst_incident_core_of_target {m : ℕ} {i : Fin (6 * m + 3)}
    {v : (catTree m).V}
    (hIncident : occ m i ∈ GluingDatum.incidentEdges v) :
    Incident (caterpillarDatum m) (loopFirst m i) (coreVertex m v) := by
  unfold loopFirst coreVertex
  exact incident_sourceEdge_sourceEndpoint (caterpillarDatum m) v (occ m i)
    hIncident 0

theorem loopSecond_incident_core_of_target {m : ℕ} {i : Fin (6 * m + 3)}
    {v : (catTree m).V} (hLeaf : IsLeafEdge m i)
    (hIncident : occ m i ∈ GluingDatum.incidentEdges v) :
    Incident (caterpillarDatum m) (loopSecond m i) (coreVertex m v) := by
  have hAtPartner := incident_sourceEdge_sourceEndpoint (caterpillarDatum m) v
    (occ m i) hIncident (partnerSheet m i)
  have hPair := pairIndex_parent_eq_of_leaf hLeaf
  have hPartner := partnerSheet_eq_pairIndex_of_incident hIncident hPair
  have hEndpoint : (caterpillarDatum m).sourceEndpoint v (partnerSheet m i) =
      coreVertex m v := by
    unfold coreVertex
    have hCanonical := sourceEndpoint_partner_eq_zero m v
    have hSheet : partnerSheet m i =
        ⟨pairIndex v.val, pairIndex_lt m v.val (by omega)⟩ := by
      apply Fin.ext
      exact hPartner
    simpa only [hSheet] using hCanonical
  rw [← hEndpoint]
  exact hAtPartner

theorem stemMain_incident_core_of_target {m : ℕ} {i : Fin (6 * m + 3)}
    {v : (catTree m).V}
    (hIncident : occ m i ∈ GluingDatum.incidentEdges v) :
    Incident (caterpillarDatum m) (stemOccurrence m i 0) (coreVertex m v) := by
  unfold stemOccurrence coreVertex
  exact incident_sourceEdge_sourceEndpoint (caterpillarDatum m) v (occ m i)
    hIncident 0

theorem spineMain_incident_core_of_target {m : ℕ} {i : Fin (6 * m + 3)}
    {v : (catTree m).V}
    (hIncident : occ m i ∈ GluingDatum.incidentEdges v) :
    Incident (caterpillarDatum m) (spineOccurrence m i 0) (coreVertex m v) := by
  unfold spineOccurrence coreVertex
  exact incident_sourceEdge_sourceEndpoint (caterpillarDatum m) v (occ m i)
    hIncident 0

/-- The complete visible surviving fibre over one target occurrence. -/
noncomputable def visibleOccurrences (m : ℕ) (i : Fin (6 * m + 3)) :
    Finset (caterpillarDatum m).SourceEdge :=
  if IsLeafEdge m i then {loopFirst m i, loopSecond m i}
  else if IsStemEdge m i then {stemOccurrence m i 0}
  else {spineOccurrence m i 0}

theorem isSpineEdge_of_not_leaf_not_stem {m : ℕ} {i : Fin (6 * m + 3)}
    (hLeaf : ¬ IsLeafEdge m i) (hStem : ¬ IsStemEdge m i) :
    IsSpineEdge i := by
  unfold IsLeafEdge IsStemEdge IsSpineEdge at *
  have hResidues : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2 := by
    omega
  rcases hResidues with hZero | hOne | hTwo
  · exact (hLeaf (Or.inl hZero)).elim
  · exact hOne
  · by_cases hLast : i.val = 6 * m + 2
    · exact (hLeaf (Or.inr hLast)).elim
    · exact (hStem ⟨hTwo, hLast⟩).elim

/-- At a central-sheet source vertex, the surviving star is exactly the
union of the visible leaf, stem and spine occurrences over its incident
target occurrences. -/
theorem nonDanglingIncident_core_eq_visible (m : ℕ) (v : (catTree m).V) :
    nonDanglingIncident (caterpillarDatum m) (coreVertex m v) =
      (incidentIndices m v).biUnion (visibleOccurrences m) := by
  classical
  ext edge
  constructor
  · intro hEdge
    have hData := (mem_nonDanglingIncident _ _ _).mp hEdge
    obtain ⟨i, hiTarget, hiClass⟩ :=
      surviving_sourceEdge_classification edge hData.1
    have hTarget := (incident_iff_target_mem_and_rel (caterpillarDatum m) edge
      (coreVertex m v)).mp hData.2
    have hiMem : occ m i ∈ GluingDatum.incidentEdges v := by
      have hiMemRaw := hTarget.1
      simp only [coreVertex, GluingDatum.sourceEndpoint] at hiMemRaw
      rw [hiTarget] at hiMemRaw
      exact hiMemRaw
    apply Finset.mem_biUnion.mpr
    refine ⟨i, (mem_incidentEdges_occ m v i).mp hiMem, ?_⟩
    rcases hiClass with ⟨hLeaf, hLoop⟩ | ⟨hStem, hMain⟩ | ⟨hSpine, hMain⟩
    · have hNotStem : ¬ IsStemEdge m i := by
        intro hBoth
        unfold IsLeafEdge at hLeaf
        unfold IsStemEdge at hBoth
        rcases hLeaf with hMod | hLast
        · omega
        · exact hBoth.2 hLast
      rcases hLoop with rfl | rfl <;>
        simp [visibleOccurrences, hLeaf]
    · have hNotLeaf : ¬ IsLeafEdge m i := by
        intro hBoth
        unfold IsLeafEdge at hBoth
        unfold IsStemEdge at hStem
        rcases hBoth with hMod | hLast
        · omega
        · exact hStem.2 hLast
      rw [hMain]
      simp [visibleOccurrences, hNotLeaf, hStem]
    · have hNotLeaf : ¬ IsLeafEdge m i := by
        intro hBoth
        unfold IsLeafEdge at hBoth
        unfold IsSpineEdge at hSpine
        rcases hBoth with hMod | hLast <;> omega
      have hNotStem : ¬ IsStemEdge m i := by
        intro hBoth
        unfold IsStemEdge at hBoth
        unfold IsSpineEdge at hSpine
        omega
      rw [hMain]
      simp [visibleOccurrences, hNotLeaf, hNotStem]
  · intro hEdge
    obtain ⟨i, hiIncident, hiVisible⟩ := Finset.mem_biUnion.mp hEdge
    have hIncident : occ m i ∈ GluingDatum.incidentEdges v :=
      (mem_incidentEdges_occ m v i).mpr hiIncident
    by_cases hLeaf : IsLeafEdge m i
    · rw [visibleOccurrences, if_pos hLeaf] at hiVisible
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiVisible
      rcases hiVisible with rfl | rfl
      · exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨loopFirst_survives hLeaf,
            loopFirst_incident_core_of_target hIncident⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨loopSecond_survives hLeaf,
            loopSecond_incident_core_of_target hLeaf hIncident⟩
    · by_cases hStem : IsStemEdge m i
      · rw [visibleOccurrences, if_neg hLeaf, if_pos hStem] at hiVisible
        simp only [Finset.mem_singleton] at hiVisible
        subst edge
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨stemMain_survives hStem,
            stemMain_incident_core_of_target hIncident⟩
      · rw [visibleOccurrences, if_neg hLeaf, if_neg hStem] at hiVisible
        simp only [Finset.mem_singleton] at hiVisible
        subst edge
        have hSpine := isSpineEdge_of_not_leaf_not_stem hLeaf hStem
        exact (mem_nonDanglingIncident _ _ _).mpr
          ⟨spineMain_survives hSpine,
            spineMain_incident_core_of_target hIncident⟩

theorem sourceEdge_target_eq_occ_of_mem_visibleOccurrences {m : ℕ}
    {i : Fin (6 * m + 3)} {edge : (caterpillarDatum m).SourceEdge}
    (hEdge : edge ∈ visibleOccurrences m i) : edge.1.1 = occ m i := by
  classical
  by_cases hLeaf : IsLeafEdge m i
  · rw [visibleOccurrences, if_pos hLeaf] at hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl <;>
      simp only [loopFirst, loopSecond, GluingDatum.sourceEdge_target]
  · by_cases hStem : IsStemEdge m i
    · rw [visibleOccurrences, if_neg hLeaf, if_pos hStem] at hEdge
      simp only [Finset.mem_singleton] at hEdge
      subst edge
      simp only [stemOccurrence, GluingDatum.sourceEdge_target]
    · rw [visibleOccurrences, if_neg hLeaf, if_neg hStem] at hEdge
      simp only [Finset.mem_singleton] at hEdge
      subst edge
      simp only [spineOccurrence, GluingDatum.sourceEdge_target]

theorem visibleOccurrences_pairwiseDisjoint (m : ℕ) (indices : Finset (Fin (6 * m + 3))) :
    Set.PairwiseDisjoint (indices : Set (Fin (6 * m + 3)))
      (visibleOccurrences m) := by
  classical
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro edge hiEdge hjEdge
  have hiTarget := sourceEdge_target_eq_occ_of_mem_visibleOccurrences hiEdge
  have hjTarget := sourceEdge_target_eq_occ_of_mem_visibleOccurrences hjEdge
  apply hij
  exact occ_injective m (hiTarget.symm.trans hjTarget)

theorem card_visibleOccurrences (m : ℕ) (i : Fin (6 * m + 3)) :
    (visibleOccurrences m i).card = if IsLeafEdge m i then 2 else 1 := by
  classical
  by_cases hLeaf : IsLeafEdge m i
  · rw [visibleOccurrences, if_pos hLeaf, if_pos hLeaf,
      Finset.card_pair (loopFirst_ne_loopSecond hLeaf)]
  · rw [visibleOccurrences, if_neg hLeaf, if_neg hLeaf]
    split_ifs <;> simp

/-- Numerical form of the exact central-sheet star census: a target leaf
occurrence contributes its two loop flags and every other incident target
occurrence contributes one surviving bridge/spine occurrence. -/
theorem nonDanglingValency_core_eq_sum (m : ℕ) (v : (catTree m).V) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m v) =
      ∑ i ∈ incidentIndices m v, if IsLeafEdge m i then 2 else 1 := by
  classical
  rw [← card_nonDanglingIncident, nonDanglingIncident_core_eq_visible,
    Finset.card_biUnion (visibleOccurrences_pairwiseDisjoint m (incidentIndices m v))]
  apply Finset.sum_congr rfl
  intro i _
  exact card_visibleOccurrences m i

theorem nonDanglingValency_core_root (m : ℕ) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m (rootTarget m)) = 3 := by
  rw [nonDanglingValency_core_eq_sum,
    incidentIndices_root m (rootTarget m) rfl]
  simp [IsLeafEdge]

theorem nonDanglingValency_core_leaf {m : ℕ} (v : (catTree m).V)
    (hv : v.val % 3 = 1) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m v) = 2 := by
  rw [nonDanglingValency_core_eq_sum, incidentIndices_leaf m v hv]
  have hLeaf : IsLeafEdge m
      (⟨v.val - 1, by have := v.isLt; omega⟩ : Fin (6 * m + 3)) := by
    left
    change (v.val - 1) % 3 = 0
    omega
  simp [hLeaf]

theorem nonDanglingValency_core_lastLeaf {m : ℕ} (v : (catTree m).V)
    (hv : v.val = 6 * m + 3) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m v) = 2 := by
  rw [nonDanglingValency_core_eq_sum, incidentIndices_lastLeaf m v hv]
  have hLeaf : IsLeafEdge m
      (⟨6 * m + 2, by omega⟩ : Fin (6 * m + 3)) := Or.inr rfl
  simp [hLeaf]

theorem nonDanglingValency_core_stem {m : ℕ} (v : (catTree m).V)
    (hmod : v.val % 3 = 0) (hlo : 3 ≤ v.val) (hhi : v.val ≤ 6 * m) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m v) = 3 := by
  rw [nonDanglingValency_core_eq_sum,
    incidentIndices_stem m v hmod hlo hhi]
  let stem : Fin (6 * m + 3) := ⟨v.val - 1, by omega⟩
  let leaf : Fin (6 * m + 3) := ⟨v.val, by omega⟩
  have hStemNotLeaf : ¬ IsLeafEdge m stem := by
    intro hLeaf
    rcases hLeaf with hMod | hLast
    · change (v.val - 1) % 3 = 0 at hMod
      omega
    · have hVal : v.val - 1 = 6 * m + 2 := by simpa [stem] using hLast
      omega
  have hLeaf : IsLeafEdge m leaf := by
    left
    exact hmod
  have hNe : stem ≠ leaf := by
    intro h
    have := congrArg Fin.val h
    simp only [stem, leaf] at this
    omega
  simp [stem, leaf, hStemNotLeaf, hLeaf, hNe]

theorem nonDanglingValency_core_junction {m : ℕ} (v : (catTree m).V)
    (hmod : v.val % 3 = 2) (hhi : v.val + 1 ≤ 6 * m) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m v) = 3 := by
  rw [nonDanglingValency_core_eq_sum,
    incidentIndices_junction m v hmod hhi]
  let left : Fin (6 * m + 3) := ⟨v.val - 1, by omega⟩
  let stem : Fin (6 * m + 3) := ⟨v.val, by omega⟩
  let right : Fin (6 * m + 3) := ⟨v.val + 2, by omega⟩
  have hLeftNotLeaf : ¬ IsLeafEdge m left := by
    intro hLeaf
    rcases hLeaf with hMod | hLast
    · change (v.val - 1) % 3 = 0 at hMod
      omega
    · have hVal : v.val - 1 = 6 * m + 2 := by simpa [left] using hLast
      omega
  have hStemNotLeaf : ¬ IsLeafEdge m stem := by
    intro hLeaf
    rcases hLeaf with hMod | hLast
    · change v.val % 3 = 0 at hMod
      omega
    · have hVal : v.val = 6 * m + 2 := by simpa [stem] using hLast
      omega
  have hRightNotLeaf : ¬ IsLeafEdge m right := by
    intro hLeaf
    rcases hLeaf with hMod | hLast
    · change (v.val + 2) % 3 = 0 at hMod
      omega
    · have hVal : v.val + 2 = 6 * m + 2 := by simpa [right] using hLast
      omega
  have hLeftStem : left ≠ stem := by
    intro h
    have := congrArg Fin.val h
    simp only [left, stem] at this
    omega
  have hLeftRight : left ≠ right := by
    intro h
    have := congrArg Fin.val h
    simp only [left, right] at this
    omega
  have hStemRight : stem ≠ right := by
    intro h
    have := congrArg Fin.val h
    simp only [stem, right] at this
    omega
  simp [left, stem, right, hLeftNotLeaf, hStemNotLeaf, hRightNotLeaf,
    hLeftStem, hLeftRight, hStemRight]

theorem nonDanglingValency_core_lastStem {m : ℕ} (v : (catTree m).V)
    (hv : v.val = 6 * m + 2) :
    nonDanglingValency (caterpillarDatum m) (coreVertex m v) = 3 := by
  rw [nonDanglingValency_core_eq_sum, incidentIndices_lastStem m v hv]
  let spine : Fin (6 * m + 3) := ⟨6 * m + 1, by omega⟩
  let leaf : Fin (6 * m + 3) := ⟨6 * m + 2, by omega⟩
  have hSpineNotLeaf : ¬ IsLeafEdge m spine := by
    intro hLeaf
    rcases hLeaf with hMod | hLast
    · change (6 * m + 1) % 3 = 0 at hMod
      omega
    · have hVal := hLast
      simp only [spine] at hVal
      omega
  have hLeaf : IsLeafEdge m leaf := Or.inr rfl
  have hNe : spine ≠ leaf := by
    intro h
    have := congrArg Fin.val h
    simp only [spine, leaf] at this
    omega
  simp [spine, leaf, hSpineNotLeaf, hLeaf, hNe]

/-! ## Global trivalence and the complete nd2 locus -/

/-- Every quotient-source vertex is either the central representative or a
singleton sheet representative away from the local partner. -/
theorem sourceVertex_eq_core_or_other (m : ℕ)
    (x : (caterpillarDatum m).SourceVertex) :
    x = coreVertex m x.1.1 ∨
      (x.1.2.val ≠ 0 ∧ x.1.2.val ≠ pairIndex x.1.1.val) := by
  by_cases hs0 : x.1.2.val = 0
  · left
    calc
      x = (caterpillarDatum m).sourceEndpoint x.1.1 x.1.2 :=
        ((caterpillarDatum m).sourceEndpoint_self x).symm
      _ = coreVertex m x.1.1 := by
        unfold coreVertex
        congr 1
        exact Fin.ext hs0
  · right
    refine ⟨hs0, ?_⟩
    have hFixed : (pairPart m (pairIndex x.1.1.val)).repr x.1.2 = x.1.2 := by
      have hProperty := x.property
      change (catVertexPart m x.1.1).repr x.1.2 = x.1.2 at hProperty
      simpa only [catVertexPart] using hProperty
    exact (pairPart_fixed_iff m (pairIndex x.1.1.val)
      (pairIndex_pos x.1.1.val) x.1.2).mp hFixed

/-- The pruned caterpillar source is trivalent.  Junctions have four literal
flags before pruning, but the singleton slope-one occurrence is absent from
this surviving valency. -/
theorem nonDanglingValency_le_three (m : ℕ)
    (x : (caterpillarDatum m).SourceVertex) :
    nonDanglingValency (caterpillarDatum m) x ≤ 3 := by
  rcases sourceVertex_eq_core_or_other m x with hCore | hOther
  · rw [hCore]
    rcases vertexClass m x.1.1 with hRoot | hLeaf | hStem | hLastLeaf |
        hJunction | hLastStem
    · rw [show x.1.1 = rootTarget m from Fin.ext hRoot,
        nonDanglingValency_core_root]
    · rw [nonDanglingValency_core_leaf x.1.1 hLeaf]
      omega
    · rw [nonDanglingValency_core_stem x.1.1 hStem.1 hStem.2.1 hStem.2.2]
    · rw [nonDanglingValency_core_lastLeaf x.1.1 hLastLeaf]
      omega
    · rw [nonDanglingValency_core_junction x.1.1 hJunction.1 hJunction.2]
    · rw [nonDanglingValency_core_lastStem x.1.1 hLastStem]
  · have hSelf := (caterpillarDatum m).sourceEndpoint_self x
    rw [← hSelf,
      nonDanglingValency_sourceEndpoint_other_eq_zero m x.1.1 x.1.2
        hOther.1 hOther.2]
    omega

/-- A central nd2 vertex is exactly a folded leaf tip. -/
theorem eq_foldVertex_of_nonDanglingValency_eq_two {m : ℕ}
    (x : (caterpillarDatum m).SourceVertex)
    (hx : nonDanglingValency (caterpillarDatum m) x = 2) :
    ∃ i : Fin (6 * m + 3), IsLeafEdge m i ∧ x = foldVertex m i := by
  rcases sourceVertex_eq_core_or_other m x with hCore | hOther
  · rw [hCore] at hx ⊢
    rcases vertexClass m x.1.1 with hRoot | hLeaf | hStem | hLastLeaf |
        hJunction | hLastStem
    · rw [show x.1.1 = rootTarget m from Fin.ext hRoot,
        nonDanglingValency_core_root] at hx
      omega
    · let i : Fin (6 * m + 3) := ⟨x.1.1.val - 1, by
        have := x.1.1.isLt
        omega⟩
      have hiLeaf : IsLeafEdge m i := by
        left
        change (x.1.1.val - 1) % 3 = 0
        omega
      refine ⟨i, hiLeaf, ?_⟩
      unfold coreVertex foldVertex
      congr 1
      apply Fin.ext
      simp only [leafTarget_val, i]
      omega
    · rw [nonDanglingValency_core_stem x.1.1 hStem.1 hStem.2.1 hStem.2.2] at hx
      omega
    · let i : Fin (6 * m + 3) := ⟨6 * m + 2, by omega⟩
      refine ⟨i, Or.inr rfl, ?_⟩
      unfold coreVertex foldVertex
      congr 1
      apply Fin.ext
      simp only [leafTarget_val, i, hLastLeaf]
    · rw [nonDanglingValency_core_junction x.1.1 hJunction.1 hJunction.2] at hx
      omega
    · rw [nonDanglingValency_core_lastStem x.1.1 hLastStem] at hx
      omega
  · have hSelf := (caterpillarDatum m).sourceEndpoint_self x
    rw [← hSelf,
      nonDanglingValency_sourceEndpoint_other_eq_zero m x.1.1 x.1.2
        hOther.1 hOther.2] at hx
    omega

theorem sourceEdge_target_eq_occ_of_incident_fold {m : ℕ}
    {i : Fin (6 * m + 3)} (hLeaf : IsLeafEdge m i)
    (edge : (caterpillarDatum m).SourceEdge)
    (hIncident : Incident (caterpillarDatum m) edge (foldVertex m i)) :
    edge.1.1 = occ m i := by
  have hTarget := (incident_iff_target_mem_and_rel (caterpillarDatum m) edge
    (foldVertex m i)).mp hIncident
  obtain ⟨j, hj⟩ := occ_surj m edge.1.1
  rw [hj]
  apply congrArg (occ m)
  apply Fin.ext
  have hjMem : j ∈ incidentIndices m (leafTarget m i) := by
    apply (mem_incidentEdges_occ m (leafTarget m i) j).mp
    simpa only [foldVertex_target, hj] using hTarget.1
  rcases hLeaf with hMod | hLast
  · have hTargetMod : (leafTarget m i).val % 3 = 1 := by
      simp only [leafTarget_val]
      omega
    rw [incidentIndices_leaf m (leafTarget m i) hTargetMod,
      Finset.mem_singleton] at hjMem
    have hVal := congrArg Fin.val hjMem
    simp only [leafTarget_val] at hVal
    omega
  · have hTargetLast : (leafTarget m i).val = 6 * m + 3 := by
      simp only [leafTarget_val, hLast]
    rw [incidentIndices_lastLeaf m (leafTarget m i) hTargetLast,
      Finset.mem_singleton] at hjMem
    have hVal := congrArg Fin.val hjMem
    exact hVal.trans hLast.symm

/-- Consecutiveness in the caterpillar source never crosses a target
occurrence: its nd2 witness is a leaf fold, whose two surviving flags lie over
that one occurrence. -/
theorem target_eq_of_consecutive {m : ℕ}
    (first second : NonDanglingEdge (caterpillarDatum m))
    (h : Consecutive (caterpillarDatum m) first second) :
    first.1.1.1 = second.1.1.1 := by
  obtain ⟨_, vertex, hFirst, hSecond, hValency⟩ := h
  obtain ⟨i, hLeaf, hVertex⟩ :=
    eq_foldVertex_of_nonDanglingValency_eq_two vertex hValency
  rw [hVertex] at hFirst hSecond
  exact (sourceEdge_target_eq_occ_of_incident_fold hLeaf first.1 hFirst).trans
    (sourceEdge_target_eq_occ_of_incident_fold hLeaf second.1 hSecond).symm

end DraismaVargas.LocalCases.CaterpillarValency
