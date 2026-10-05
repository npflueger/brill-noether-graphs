module

public import DraismaVargas.LocalCases.CaterpillarPruning

@[expose] public section

/-!
# The spine census of the caterpillar seed

The target tree of the caterpillar seed (`Infrastructure.CaterpillarTree`) has
a spine, the path from `u₁` through the junctions `p_i` to `u_g`.  This file
decides which source occurrences of the caterpillar gluing datum over the
spine survive pruning: the central sheet survives every spine edge, a nonzero sheet
`s` survives exactly on its own slope-two spine edge `6(s-1)+1`, where it is
the central occurrence, and every other spine occurrence dangles
(`spineOccurrence_isDangling_iff`).  The proof propagates danglingness along
the spine through the singleton junctions, one three-edge step at a time,
starting from the two boundary steps.  `CaterpillarValency` reads this census
back at source vertices.
-/

namespace DraismaVargas.LocalCases.CaterpillarSpine

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarDatum
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.DanglingSideStructure
open DraismaVargas.LocalCases.CaterpillarPruning

/-- The target occurrences on the central path. -/
def IsSpineEdge (i : Fin (6 * m + 3)) : Prop := i.val % 3 = 1

instance (i : Fin (6 * m + 3)) : Decidable (IsSpineEdge i) := by
  unfold IsSpineEdge
  infer_instance

/-- An actual occurrence over a target spine edge. -/
noncomputable def spineOccurrence (m : ℕ) (i : Fin (6 * m + 3))
    (s : Fin (m + 2)) : (caterpillarDatum m).SourceEdge :=
  (caterpillarDatum m).sourceEdge (occ m i) s

def spineLeftVertex (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).SourceVertex :=
  coreVertex m (catParent m i)

def spineRightVertex (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).SourceVertex :=
  coreVertex m i.succ

theorem sourceEnds_spineMain (m : ℕ) (i : Fin (6 * m + 3)) :
    (caterpillarDatum m).sourceEnds (spineOccurrence m i 0) =
      (spineLeftVertex m i, spineRightVertex m i) := by
  unfold spineOccurrence
  rw [sourceEnds_sourceEdge]
  rfl

theorem spineLeft_reaches_loop {m : ℕ} {i : Fin (6 * m + 3)}
    (hSpine : IsSpineEdge i) :
    ∃ leaf : Fin (6 * m + 3), IsLeafEdge m leaf ∧
      ReachP (caterpillarDatum m).sourceGraph
        (fun vertex ↦ vertex ≠ spineRightVertex m i)
        (spineLeftVertex m i) (loopBaseVertex m leaf) := by
  have hiLo : 1 ≤ i.val := by
    unfold IsSpineEdge at hSpine
    omega
  by_cases hFirst : i.val = 1
  · let leaf : Fin (6 * m + 3) := ⟨0, by omega⟩
    refine ⟨leaf, Or.inl rfl, ?_⟩
    have hVertex : spineLeftVertex m i = loopBaseVertex m leaf := by
      unfold spineLeftVertex loopBaseVertex coreVertex leaf
      congr 1
      apply Fin.ext
      simp only [catParent_val]
      norm_num [hFirst, parentIndex]
    rw [hVertex]
    exact reachP_refl _ _
  · have hiMore : 4 ≤ i.val := by
      unfold IsSpineEdge at hSpine
      omega
    let stem : Fin (6 * m + 3) := ⟨i.val - 2, by
      have := i.isLt
      omega⟩
    have hStem : IsStemEdge m stem := by
      constructor
      · simp only [stem]
        unfold IsSpineEdge at hSpine
        omega
      · simp only [stem]
        have := i.isLt
        omega
    let leaf := stemLeafIndex m stem hStem
    refine ⟨leaf, stemLeafIndex_isLeaf hStem, ?_⟩
    have hStart : spineLeftVertex m i = coreVertex m (catParent m stem) := by
      unfold spineLeftVertex
      congr 1
      apply Fin.ext
      simp only [catParent_val, stem]
      unfold IsSpineEdge at hSpine
      unfold parentIndex
      split_ifs <;> omega
    have hFinish : loopBaseVertex m leaf = coreVertex m stem.succ := by
      unfold leaf loopBaseVertex coreVertex stemLeafIndex
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      change parentIndex (stem.val + 1 + 1) = stem.val + 1
      have hMod := hStem.1
      unfold parentIndex
      split_ifs <;> omega
    rw [hStart, hFinish]
    refine reachP_single (coreStep_pos m stem) ?_
    intro hEq
    have hTarget := congrArg
      (fun vertex : (caterpillarDatum m).SourceVertex ↦ vertex.1.1.val) hEq
    change stem.succ.val = i.succ.val at hTarget
    simp only [Fin.val_succ, stem] at hTarget
    omega

theorem spineRight_reaches_loop {m : ℕ} {i : Fin (6 * m + 3)}
    (hSpine : IsSpineEdge i) :
    ∃ leaf : Fin (6 * m + 3), IsLeafEdge m leaf ∧
      ReachP (caterpillarDatum m).sourceGraph
        (fun vertex ↦ vertex ≠ spineLeftVertex m i)
        (spineRightVertex m i) (loopBaseVertex m leaf) := by
  by_cases hLast : i.val = 6 * m + 1
  · let leaf : Fin (6 * m + 3) := ⟨6 * m + 2, by omega⟩
    refine ⟨leaf, Or.inr rfl, ?_⟩
    have hVertex : spineRightVertex m i = loopBaseVertex m leaf := by
      unfold spineRightVertex loopBaseVertex coreVertex leaf
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      change i.val + 1 = parentIndex (6 * m + 2 + 1)
      rw [hLast]
      simp only [parentIndex]
      split_ifs <;> omega
    rw [hVertex]
    exact reachP_refl _ _
  · let stem : Fin (6 * m + 3) := ⟨i.val + 1, by
      have := i.isLt
      unfold IsSpineEdge at hSpine
      omega⟩
    have hStem : IsStemEdge m stem := by
      constructor
      · simp only [stem]
        unfold IsSpineEdge at hSpine
        omega
      · simp only [stem]
        omega
    let leaf := stemLeafIndex m stem hStem
    refine ⟨leaf, stemLeafIndex_isLeaf hStem, ?_⟩
    have hStart : spineRightVertex m i = coreVertex m (catParent m stem) := by
      unfold spineRightVertex
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ, catParent_val, stem]
      unfold IsSpineEdge at hSpine
      unfold parentIndex
      split_ifs <;> omega
    have hFinish : loopBaseVertex m leaf = coreVertex m stem.succ := by
      unfold leaf loopBaseVertex coreVertex stemLeafIndex
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      change parentIndex (stem.val + 1 + 1) = stem.val + 1
      have hMod := hStem.1
      unfold parentIndex
      split_ifs <;> omega
    rw [hStart, hFinish]
    refine reachP_single (coreStep_pos m stem) ?_
    intro hEq
    have hTarget := congrArg
      (fun vertex : (caterpillarDatum m).SourceVertex ↦ vertex.1.1.val) hEq
    change stem.succ.val = (catParent m i).val at hTarget
    simp only [Fin.val_succ, stem, catParent_val] at hTarget
    unfold IsSpineEdge at hSpine
    unfold parentIndex at hTarget
    split_ifs at hTarget <;> omega

/-- Every central-sheet spine occurrence survives: each side reaches the
parallel loop of its adjacent lollipop without crossing the spine edge. -/
theorem spineMain_survives {m : ℕ} {i : Fin (6 * m + 3)}
    (hSpine : IsSpineEdge i) :
    ¬ IsDangling (caterpillarDatum m) (spineOccurrence m i 0) := by
  obtain ⟨leftLeaf, hLeftLeaf, hLeftReach⟩ := spineLeft_reaches_loop hSpine
  obtain ⟨rightLeaf, hRightLeaf, hRightReach⟩ := spineRight_reaches_loop hSpine
  apply not_isDangling_of_active_reaches (caterpillarDatum m)
    (spineOccurrence m i 0) (sourceEnds_spineMain m i)
    (firstAnchor := loopBaseVertex m leftLeaf)
    (secondAnchor := loopBaseVertex m rightLeaf)
  · exact nonDanglingValency_loopBase_ne_zero hLeftLeaf
  · exact nonDanglingValency_loopBase_ne_zero hRightLeaf
  · exact hLeftReach
  · exact hRightReach

/-! ## Singleton vertices and dangling propagation -/

theorem block_pairPart_other (m j : ℕ) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsj : s.val ≠ j) :
    (pairPart m j).block s = {s} := by
  ext t
  rw [SheetPartition.mem_block_iff, SheetPartition.rel_iff,
    pairPart_repr, pairPart_repr, ite_eq_right hsj]
  by_cases ht : t.val = j
  · rw [ite_eq_left ht, Finset.mem_singleton]
    constructor
    · intro h
      have : s.val = 0 := by simpa using congrArg Fin.val h
      exact (hs0 this).elim
    · intro h
      have : s.val = j := by simpa [h] using ht
      exact (hsj this).elim
  · rw [ite_eq_right ht, Finset.mem_singleton]
    exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩

/-- Above a singleton sheet block, actual incidence has the same cardinality
as target incidence. -/
theorem card_incidentSourceEdge_sourceEndpoint_other (m : ℕ)
    (v : (catTree m).V) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPair : s.val ≠ pairIndex v.val) :
    Fintype.card (IncidentSourceEdge (caterpillarDatum m)
      ((caterpillarDatum m).sourceEndpoint v s)) =
      (GluingDatum.incidentEdges v).card := by
  rw [card_incidentSourceEdge_eq_sum_blockCountWithin]
  have hrepr : (catVertexPart m v).repr s = s := by
    unfold catVertexPart
    exact pairPart_repr_of_ne m _ s hsPair
  simp only [GluingDatum.sourceEndpoint]
  rw [caterpillarDatum_vertexPartition, hrepr]
  calc
    (∑ edge ∈ GluingDatum.incidentEdges v,
        ((caterpillarDatum m).edgePartition edge).blockCountWithin
          ((caterpillarDatum m).vertexPartition v) s) =
        ∑ _edge ∈ GluingDatum.incidentEdges v, 1 := by
      apply Finset.sum_congr rfl
      intro edge _
      apply SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
      rw [caterpillarDatum_vertexPartition, catVertexPart]
      exact block_pairPart_other m _ s hs0 hsPair
    _ = (GluingDatum.incidentEdges v).card := by simp

/-- At a three-valent singleton source vertex, if two of the three actual
occurrences dangle, so does the third: otherwise surviving valency is one. -/
theorem isDangling_of_card_three_of_two_dangling
    {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
    (hConnected : data.Connected) (vertex : data.SourceVertex)
    (edge first second : data.SourceEdge)
    (hEdge : Incident data edge vertex) (hFirst : Incident data first vertex)
    (hSecond : Incident data second vertex)
    (hEF : edge ≠ first) (hES : edge ≠ second) (hFS : first ≠ second)
    (hCard : Fintype.card (IncidentSourceEdge data vertex) = 3)
    (hFirstDangling : IsDangling data first)
    (hSecondDangling : IsDangling data second) : IsDangling data edge := by
  classical
  by_contra hEdgeSurvives
  let e : IncidentSourceEdge data vertex := ⟨edge, hEdge⟩
  let f : IncidentSourceEdge data vertex := ⟨first, hFirst⟩
  let s : IncidentSourceEdge data vertex := ⟨second, hSecond⟩
  have hef : e ≠ f := fun h ↦ hEF (congrArg Subtype.val h)
  have hes : e ≠ s := fun h ↦ hES (congrArg Subtype.val h)
  have hfs : f ≠ s := fun h ↦ hFS (congrArg Subtype.val h)
  have hPairCard : ({e, f, s} : Finset (IncidentSourceEdge data vertex)).card = 3 := by
    simp [hef, hes, hfs]
  have hAll : ({e, f, s} : Finset (IncidentSourceEdge data vertex)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hPairCard]
    exact hCard.symm
  have hOthers : ∀ other : data.SourceEdge, other ≠ edge →
      Incident data other vertex → IsDangling data other := by
    intro other hOtherNe hOtherInc
    let o : IncidentSourceEdge data vertex := ⟨other, hOtherInc⟩
    have ho : o ∈ ({e, f, s} : Finset (IncidentSourceEdge data vertex)) := by
      rw [hAll]
      exact Finset.mem_univ _
    simp only [Finset.mem_insert, Finset.mem_singleton] at ho
    rcases ho with ho | ho | ho
    · exact (hOtherNe (congrArg Subtype.val ho)).elim
    · have : other = first := congrArg Subtype.val ho
      simpa [this] using hFirstDangling
    · have : other = second := congrArg Subtype.val ho
      simpa [this] using hSecondDangling
  apply NonDanglingValency.nonDanglingValency_ne_one data hConnected vertex
  unfold nonDanglingValency
  have hFilter : (Finset.univ.filter fun other : data.SourceEdge ↦
      ¬ IsDangling data other ∧ Incident data other vertex) = {edge} := by
    ext other
    constructor
    · intro h
      obtain ⟨hOther, hInc⟩ := (Finset.mem_filter.mp h).2
      apply Finset.mem_singleton.mpr
      by_contra hNe
      exact hOther (hOthers other hNe hInc)
    · intro h
      have hEq := Finset.mem_singleton.mp h
      subst other
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hEdgeSurvives, hEdge⟩
  rw [hFilter, Finset.card_singleton]

/-! ## The local three-edge step along the spine -/

def spineIndex (m : ℕ) (q : Fin (2 * m + 1)) : Fin (6 * m + 3) :=
  ⟨3 * q.val + 1, by
    have := q.isLt
    omega⟩

@[simp] theorem spineIndex_val (m : ℕ) (q : Fin (2 * m + 1)) :
    (spineIndex m q).val = 3 * q.val + 1 := rfl

theorem spineIndex_isSpine (m : ℕ) (q : Fin (2 * m + 1)) :
    IsSpineEdge (spineIndex m q) := by
  unfold IsSpineEdge
  simp only [spineIndex_val]
  omega

def junctionTarget (m : ℕ) (q : Fin (2 * m)) : (catTree m).V :=
  ⟨3 * q.val + 2, by
    have := q.isLt
    omega⟩

def junctionStemIndex (m : ℕ) (q : Fin (2 * m)) : Fin (6 * m + 3) :=
  ⟨3 * q.val + 2, by
    have := q.isLt
    omega⟩

def junctionLeftIndex (m : ℕ) (q : Fin (2 * m)) : Fin (6 * m + 3) :=
  spineIndex m ⟨q.val, by omega⟩

def junctionRightIndex (m : ℕ) (q : Fin (2 * m)) : Fin (6 * m + 3) :=
  spineIndex m ⟨q.val + 1, by omega⟩

def junctionSourceVertex (m : ℕ) (q : Fin (2 * m)) (s : Fin (m + 2)) :
    (caterpillarDatum m).SourceVertex :=
  (caterpillarDatum m).sourceEndpoint (junctionTarget m q) s

theorem junctionStem_isStem (m : ℕ) (q : Fin (2 * m)) :
    IsStemEdge m (junctionStemIndex m q) := by
  constructor
  · simp only [junctionStemIndex]
    omega
  · simp only [junctionStemIndex]
    have := q.isLt
    omega

theorem junction_partner_eq (m : ℕ) (q : Fin (2 * m)) :
    (partnerSheet m (junctionStemIndex m q)).val =
      pairIndex (junctionTarget m q).val := by
  simp only [partnerSheet_val, junctionStemIndex, junctionTarget]
  unfold pairIndex lolli
  omega

theorem junctionLeft_incident (m : ℕ) (q : Fin (2 * m))
    (s : Fin (m + 2)) :
    Incident (caterpillarDatum m)
      (spineOccurrence m (junctionLeftIndex m q) s)
      (junctionSourceVertex m q s) := by
  unfold Incident spineOccurrence junctionSourceVertex junctionLeftIndex
  rw [sourceEnds_sourceEdge]
  right
  congr 1

theorem junctionStem_incident (m : ℕ) (q : Fin (2 * m))
    (s : Fin (m + 2)) :
    Incident (caterpillarDatum m)
      (stemOccurrence m (junctionStemIndex m q) s)
      (junctionSourceVertex m q s) := by
  unfold Incident stemOccurrence junctionSourceVertex
  rw [sourceEnds_sourceEdge]
  left
  change (caterpillarDatum m).sourceEndpoint
      (catParent m (junctionStemIndex m q)) s =
    (caterpillarDatum m).sourceEndpoint (junctionTarget m q) s
  congr 1
  apply Fin.ext
  simp only [catParent_val, junctionStemIndex, junctionTarget]
  unfold parentIndex
  split_ifs <;> omega

theorem junctionRight_incident (m : ℕ) (q : Fin (2 * m))
    (s : Fin (m + 2)) :
    Incident (caterpillarDatum m)
      (spineOccurrence m (junctionRightIndex m q) s)
      (junctionSourceVertex m q s) := by
  unfold Incident spineOccurrence junctionSourceVertex junctionRightIndex
  rw [sourceEnds_sourceEdge]
  left
  change (caterpillarDatum m).sourceEndpoint
      (catParent m (junctionRightIndex m q)) s =
    (caterpillarDatum m).sourceEndpoint (junctionTarget m q) s
  congr 1
  apply Fin.ext
  simp only [catParent_val, junctionRightIndex, spineIndex_val, junctionTarget]
  unfold parentIndex
  split_ifs <;> omega

theorem junction_occurrences_pairwise_ne (m : ℕ) (q : Fin (2 * m))
    (s : Fin (m + 2)) :
    spineOccurrence m (junctionLeftIndex m q) s ≠
        stemOccurrence m (junctionStemIndex m q) s ∧
      spineOccurrence m (junctionLeftIndex m q) s ≠
        spineOccurrence m (junctionRightIndex m q) s ∧
      stemOccurrence m (junctionStemIndex m q) s ≠
        spineOccurrence m (junctionRightIndex m q) s := by
  have target_ne_of_index_ne : ∀ {a b : Fin (6 * m + 3)}, a ≠ b →
      (caterpillarDatum m).sourceEdge (occ m a) s ≠
        (caterpillarDatum m).sourceEdge (occ m b) s := by
    intro a b hab hEq
    have hTarget := congrArg
      (fun edge : (caterpillarDatum m).SourceEdge ↦ edge.1.1) hEq
    simp only [GluingDatum.sourceEdge_target] at hTarget
    exact hab (occ_injective m hTarget)
  constructor
  · exact target_ne_of_index_ne (by
      intro h
      have := congrArg Fin.val h
      simp only [junctionLeftIndex, spineIndex_val, junctionStemIndex] at this
      omega)
  constructor
  · exact target_ne_of_index_ne (by
      intro h
      have := congrArg Fin.val h
      simp only [junctionLeftIndex, junctionRightIndex, spineIndex_val] at this
      omega)
  · exact target_ne_of_index_ne (by
      intro h
      have := congrArg Fin.val h
      simp only [junctionStemIndex, junctionRightIndex, spineIndex_val] at this
      omega)

theorem card_incidentSourceEdge_junction_other (m : ℕ) (q : Fin (2 * m))
    (s : Fin (m + 2)) (hs0 : s.val ≠ 0)
    (hsPair : s.val ≠ pairIndex (junctionTarget m q).val) :
    Fintype.card (IncidentSourceEdge (caterpillarDatum m)
      (junctionSourceVertex m q s)) = 3 := by
  unfold junctionSourceVertex
  rw [card_incidentSourceEdge_sourceEndpoint_other m (junctionTarget m q) s hs0 hsPair]
  apply card_incidentEdges_three m (junctionTarget m q)
    (a := junctionLeftIndex m q) (b := junctionStemIndex m q)
    (c := junctionRightIndex m q)
  · intro h
    have := congrArg Fin.val h
    simp only [junctionLeftIndex, spineIndex_val, junctionStemIndex] at this
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [junctionLeftIndex, junctionRightIndex, spineIndex_val] at this
    omega
  · intro h
    have := congrArg Fin.val h
    simp only [junctionStemIndex, junctionRightIndex, spineIndex_val] at this
    omega
  · apply incidentIndices_junction
    · simp only [junctionTarget]
      omega
    · simp only [junctionTarget]
      have := q.isLt
      omega

/-- Propagate danglingness one step to the right through a singleton
junction; the third incident occurrence is the already-pruned stem. -/
theorem spine_dangles_next {m : ℕ} (q : Fin (2 * m)) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0)
    (hsPair : s.val ≠ pairIndex (junctionTarget m q).val)
    (hLeft : IsDangling (caterpillarDatum m)
      (spineOccurrence m (junctionLeftIndex m q) s)) :
    IsDangling (caterpillarDatum m)
      (spineOccurrence m (junctionRightIndex m q) s) := by
  rcases junction_occurrences_pairwise_ne m q s with ⟨hLS, hLR, hSR⟩
  apply isDangling_of_card_three_of_two_dangling
    (caterpillarDatum m) (caterpillarDatum_connected m)
    (junctionSourceVertex m q s)
    (spineOccurrence m (junctionRightIndex m q) s)
    (spineOccurrence m (junctionLeftIndex m q) s)
    (stemOccurrence m (junctionStemIndex m q) s)
  · exact junctionRight_incident m q s
  · exact junctionLeft_incident m q s
  · exact junctionStem_incident m q s
  · exact hLR.symm
  · exact hSR.symm
  · exact hLS
  · exact card_incidentSourceEdge_junction_other m q s hs0 hsPair
  · exact hLeft
  · apply (stemOccurrence_isDangling_iff (junctionStem_isStem m q) s).mpr
    exact ⟨hs0, by rw [junction_partner_eq]; exact hsPair⟩

/-- The symmetric one-step propagation toward the left. -/
theorem spine_dangles_previous {m : ℕ} (q : Fin (2 * m))
    (s : Fin (m + 2)) (hs0 : s.val ≠ 0)
    (hsPair : s.val ≠ pairIndex (junctionTarget m q).val)
    (hRight : IsDangling (caterpillarDatum m)
      (spineOccurrence m (junctionRightIndex m q) s)) :
    IsDangling (caterpillarDatum m)
      (spineOccurrence m (junctionLeftIndex m q) s) := by
  rcases junction_occurrences_pairwise_ne m q s with ⟨hLS, hLR, hSR⟩
  apply isDangling_of_card_three_of_two_dangling
    (caterpillarDatum m) (caterpillarDatum_connected m)
    (junctionSourceVertex m q s)
    (spineOccurrence m (junctionLeftIndex m q) s)
    (spineOccurrence m (junctionRightIndex m q) s)
    (stemOccurrence m (junctionStemIndex m q) s)
  · exact junctionLeft_incident m q s
  · exact junctionRight_incident m q s
  · exact junctionStem_incident m q s
  · exact hLR
  · exact hLS
  · exact hSR.symm
  · exact card_incidentSourceEdge_junction_other m q s hs0 hsPair
  · exact hRight
  · apply (stemOccurrence_isDangling_iff (junctionStem_isStem m q) s).mpr
    exact ⟨hs0, by rw [junction_partner_eq]; exact hsPair⟩

/-! ## The two boundary steps -/

def firstSpineIndex (m : ℕ) : Fin (6 * m + 3) := spineIndex m 0

def firstLeafIndex (m : ℕ) : Fin (6 * m + 3) := ⟨0, by omega⟩

def rootTarget (m : ℕ) : (catTree m).V := ⟨0, by omega⟩

def rootSourceVertex (m : ℕ) (s : Fin (m + 2)) :
    (caterpillarDatum m).SourceVertex :=
  (caterpillarDatum m).sourceEndpoint (rootTarget m) s

theorem firstLeaf_incident_root (m : ℕ) (s : Fin (m + 2)) :
    Incident (caterpillarDatum m)
      (leafOccurrence m (firstLeafIndex m) s) (rootSourceVertex m s) := by
  unfold Incident leafOccurrence rootSourceVertex firstLeafIndex rootTarget
  rw [sourceEnds_sourceEdge]
  left
  congr 1

theorem firstSpine_incident_root (m : ℕ) (s : Fin (m + 2)) :
    Incident (caterpillarDatum m)
      (spineOccurrence m (firstSpineIndex m) s) (rootSourceVertex m s) := by
  unfold Incident spineOccurrence rootSourceVertex firstSpineIndex rootTarget
  rw [sourceEnds_sourceEdge]
  left
  change (caterpillarDatum m).sourceEndpoint
      (catParent m (spineIndex m 0)) s =
    (caterpillarDatum m).sourceEndpoint ⟨0, by omega⟩ s
  congr 1

theorem firstLeaf_ne_firstSpine (m : ℕ) (s : Fin (m + 2)) :
    leafOccurrence m (firstLeafIndex m) s ≠
      spineOccurrence m (firstSpineIndex m) s := by
  intro h
  have hTarget := congrArg
    (fun edge : (caterpillarDatum m).SourceEdge ↦ edge.1.1) h
  simp only [leafOccurrence, spineOccurrence,
    GluingDatum.sourceEdge_target] at hTarget
  have hIndex := occ_injective m hTarget
  have := congrArg Fin.val hIndex
  norm_num [firstLeafIndex, firstSpineIndex, spineIndex] at this

theorem card_incidentSourceEdge_root_other (m : ℕ) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPair : s.val ≠ 1) :
    Fintype.card (IncidentSourceEdge (caterpillarDatum m)
      (rootSourceVertex m s)) = 2 := by
  unfold rootSourceVertex
  have hPairIndex : pairIndex (rootTarget m).val = 1 := by
    norm_num [rootTarget, pairIndex, lolli]
  rw [card_incidentSourceEdge_sourceEndpoint_other m (rootTarget m) s hs0
    (by rw [hPairIndex]; exact hsPair)]
  apply card_incidentEdges_two m (rootTarget m)
    (a := firstLeafIndex m) (b := firstSpineIndex m)
  · intro h
    have := congrArg Fin.val h
    norm_num [firstLeafIndex, firstSpineIndex, spineIndex] at this
  · apply incidentIndices_root
    rfl

theorem firstSpine_dangles_other (m : ℕ) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPair : s.val ≠ 1) :
    IsDangling (caterpillarDatum m)
      (spineOccurrence m (firstSpineIndex m) s) := by
  have hLeaf : IsLeafEdge m (firstLeafIndex m) := Or.inl rfl
  have hLeafPartner : (partnerSheet m (firstLeafIndex m)).val = 1 := by
    norm_num [partnerSheet, firstLeafIndex, pairIndex, lolli]
  apply isDangling_of_incident_of_vertex_degree_eq_two
    (caterpillarDatum m) (firstLeaf_ne_firstSpine m s)
    (firstLeaf_incident_root m s) (firstSpine_incident_root m s)
  · rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge,
      card_incidentSourceEdge_root_other m s hs0 hsPair]
    norm_num
  · apply (leafOccurrence_isDangling_iff hLeaf s).mpr
    exact ⟨hs0, by rw [hLeafPartner]; exact hsPair⟩

def lastSpineIndex (m : ℕ) : Fin (6 * m + 3) :=
  spineIndex m ⟨2 * m, by omega⟩

def lastLeafIndex (m : ℕ) : Fin (6 * m + 3) := ⟨6 * m + 2, by omega⟩

def lastStemTarget (m : ℕ) : (catTree m).V := ⟨6 * m + 2, by omega⟩

def lastStemSourceVertex (m : ℕ) (s : Fin (m + 2)) :
    (caterpillarDatum m).SourceVertex :=
  (caterpillarDatum m).sourceEndpoint (lastStemTarget m) s

theorem lastSpine_incident_lastStem (m : ℕ) (s : Fin (m + 2)) :
    Incident (caterpillarDatum m)
      (spineOccurrence m (lastSpineIndex m) s)
      (lastStemSourceVertex m s) := by
  unfold Incident spineOccurrence lastStemSourceVertex lastSpineIndex
  rw [sourceEnds_sourceEdge]
  right
  change (caterpillarDatum m).sourceEndpoint (lastSpineIndex m).succ s =
    (caterpillarDatum m).sourceEndpoint (lastStemTarget m) s
  congr 1
  apply Fin.ext
  simp only [Fin.val_succ, lastSpineIndex, spineIndex_val, lastStemTarget]
  omega

theorem lastLeaf_incident_lastStem (m : ℕ) (s : Fin (m + 2)) :
    Incident (caterpillarDatum m)
      (leafOccurrence m (lastLeafIndex m) s)
      (lastStemSourceVertex m s) := by
  unfold Incident leafOccurrence lastStemSourceVertex lastLeafIndex lastStemTarget
  rw [sourceEnds_sourceEdge]
  left
  change (caterpillarDatum m).sourceEndpoint
      (catParent m ⟨6 * m + 2, by omega⟩) s =
    (caterpillarDatum m).sourceEndpoint ⟨6 * m + 2, by omega⟩ s
  congr 1
  apply Fin.ext
  simp only [catParent_val]
  unfold parentIndex
  split_ifs <;> omega

theorem lastSpine_ne_lastLeaf (m : ℕ) (s : Fin (m + 2)) :
    spineOccurrence m (lastSpineIndex m) s ≠
      leafOccurrence m (lastLeafIndex m) s := by
  intro h
  have hTarget := congrArg
    (fun edge : (caterpillarDatum m).SourceEdge ↦ edge.1.1) h
  simp only [leafOccurrence, spineOccurrence,
    GluingDatum.sourceEdge_target] at hTarget
  have hIndex := occ_injective m hTarget
  have := congrArg Fin.val hIndex
  norm_num [lastLeafIndex, lastSpineIndex, spineIndex] at this
  omega

theorem card_incidentSourceEdge_lastStem_other (m : ℕ) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPair : s.val ≠ m + 1) :
    Fintype.card (IncidentSourceEdge (caterpillarDatum m)
      (lastStemSourceVertex m s)) = 2 := by
  unfold lastStemSourceVertex
  have hPairIndex : pairIndex (lastStemTarget m).val = m + 1 := by
    simp only [lastStemTarget]
    unfold pairIndex lolli
    omega
  rw [card_incidentSourceEdge_sourceEndpoint_other m (lastStemTarget m) s hs0
    (by rw [hPairIndex]; exact hsPair)]
  apply card_incidentEdges_two m (lastStemTarget m)
    (a := lastSpineIndex m) (b := lastLeafIndex m)
  · intro h
    have := congrArg Fin.val h
    norm_num [lastSpineIndex, lastLeafIndex, spineIndex] at this
    omega
  · have hSpine : lastSpineIndex m = ⟨6 * m + 1, by omega⟩ := by
      apply Fin.ext
      simp only [lastSpineIndex, spineIndex_val]
      omega
    have hLeaf : lastLeafIndex m = ⟨6 * m + 2, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hSpine, hLeaf]
    exact incidentIndices_lastStem m (lastStemTarget m) rfl

theorem lastSpine_dangles_other (m : ℕ) (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) (hsPair : s.val ≠ m + 1) :
    IsDangling (caterpillarDatum m)
      (spineOccurrence m (lastSpineIndex m) s) := by
  have hLeaf : IsLeafEdge m (lastLeafIndex m) := Or.inr rfl
  have hLeafPartner : (partnerSheet m (lastLeafIndex m)).val = m + 1 := by
    simp only [partnerSheet_val, lastLeafIndex]
    unfold pairIndex lolli
    omega
  apply isDangling_of_incident_of_vertex_degree_eq_two
    (caterpillarDatum m) (lastSpine_ne_lastLeaf m s).symm
    (lastLeaf_incident_lastStem m s) (lastSpine_incident_lastStem m s)
  · rw [vertex_degree_sourceGraph_eq_card_incidentSourceEdge,
      card_incidentSourceEdge_lastStem_other m s hs0 hsPair]
    norm_num
  · apply (leafOccurrence_isDangling_iff hLeaf s).mpr
    exact ⟨hs0, by rw [hLeafPartner]; exact hsPair⟩

/-! ## Propagation from the boundaries to the paired spine block -/

/-- The unique slope-two spine position whose occurrence block pairs sheet
`s` with the central sheet. -/
def localSpinePosition (s : Fin (m + 2)) : ℕ := 2 * (s.val - 1)

theorem localSpinePosition_le (s : Fin (m + 2)) :
    localSpinePosition s ≤ 2 * m := by
  unfold localSpinePosition
  have := s.isLt
  omega

theorem spineIndex_dangles_of_lt_local {m : ℕ} (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) : ∀ (q : Fin (2 * m + 1)),
    q.val < localSpinePosition s →
      IsDangling (caterpillarDatum m) (spineOccurrence m (spineIndex m q) s) := by
  intro q
  let go : ∀ n : ℕ, (hn : n < 2 * m + 1) → n < localSpinePosition s →
      IsDangling (caterpillarDatum m)
        (spineOccurrence m (spineIndex m ⟨n, hn⟩) s) := by
    intro n
    induction n with
    | zero =>
        intro hn hLocal
        have hsOne : s.val ≠ 1 := by
          intro hs
          unfold localSpinePosition at hLocal
          omega
        simpa [firstSpineIndex] using firstSpine_dangles_other m s hs0 hsOne
    | succ n ih =>
        intro hn hLocal
        have hnInternal : n < 2 * m := by omega
        let junction : Fin (2 * m) := ⟨n, hnInternal⟩
        have hPrevious := ih (by omega) (by omega)
        have hsPair : s.val ≠ pairIndex (junctionTarget m junction).val := by
          intro hEq
          unfold localSpinePosition at hLocal
          simp only [junctionTarget, junction] at hEq
          unfold pairIndex lolli at hEq
          omega
        have hNext := spine_dangles_next junction s hs0 hsPair (by
          simpa [junctionLeftIndex, junction] using hPrevious)
        simpa [junctionRightIndex, junction] using hNext
  exact go q.val q.isLt

theorem spineIndex_dangles_of_local_lt {m : ℕ} (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) : ∀ (q : Fin (2 * m + 1)),
    localSpinePosition s < q.val →
      IsDangling (caterpillarDatum m) (spineOccurrence m (spineIndex m q) s) := by
  intro q hLocal
  let go : ∀ d : ℕ, (hd : d ≤ 2 * m) →
      localSpinePosition s < 2 * m - d →
      IsDangling (caterpillarDatum m)
        (spineOccurrence m
          (spineIndex m ⟨2 * m - d, by omega⟩) s) := by
    intro d
    induction d with
    | zero =>
        intro hd hLocalLast
        have hsLast : s.val ≠ m + 1 := by
          intro hs
          unfold localSpinePosition at hLocalLast
          omega
        simpa [lastSpineIndex] using lastSpine_dangles_other m s hs0 hsLast
    | succ d ih =>
        intro hd hCurrent
        have hdPrev : d ≤ 2 * m := by omega
        have hCurrentPos : 0 < 2 * m - (d + 1) := by
          have hNonneg := Nat.zero_le (localSpinePosition s)
          omega
        let junction : Fin (2 * m) := ⟨2 * m - (d + 1), by omega⟩
        have hNext := ih hdPrev (by omega)
        have hsPair : s.val ≠ pairIndex (junctionTarget m junction).val := by
          intro hEq
          unfold localSpinePosition at hCurrent
          simp only [junctionTarget, junction] at hEq
          unfold pairIndex lolli at hEq
          omega
        have hNext' : IsDangling (caterpillarDatum m)
            (spineOccurrence m (junctionRightIndex m junction) s) := by
          convert hNext using 1
          congr 3
          apply Fin.ext
          simp only [junctionRightIndex, spineIndex_val, junction]
          omega
        have hPrevious := spine_dangles_previous junction s hs0 hsPair hNext'
        simpa [junctionLeftIndex, junction] using hPrevious
  have hd : 2 * m - q.val ≤ 2 * m := Nat.sub_le _ _
  have hAt := go (2 * m - q.val) hd (by
    have hq := q.isLt
    omega)
  convert hAt using 1
  congr 3
  apply Fin.ext
  simp only
  have hq := q.isLt
  omega

/-! ## Exact spine-fibre census -/

def localSpineQ (m : ℕ) (s : Fin (m + 2)) : Fin (2 * m + 1) :=
  ⟨localSpinePosition s, by
    have := localSpinePosition_le s
    omega⟩

theorem localSpineQ_val (m : ℕ) (s : Fin (m + 2)) :
    (localSpineQ m s).val = localSpinePosition s := rfl

theorem localSpine_isPair {m : ℕ} (s : Fin (m + 2)) :
    IsPairEdge m (spineIndex m (localSpineQ m s)).val := by
  left
  simp only [spineIndex_val, localSpineQ_val, localSpinePosition]
  omega

theorem pairIndex_localSpine {m : ℕ} (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) :
    pairIndex ((spineIndex m (localSpineQ m s)).val + 1) = s.val := by
  simp only [spineIndex_val, localSpineQ_val, localSpinePosition]
  unfold pairIndex lolli
  omega

/-- On its unique slope-two spine edge, the partner sheet names the literal
central occurrence. -/
theorem localSpineOccurrence_eq_main {m : ℕ} (s : Fin (m + 2))
    (hs0 : s.val ≠ 0) :
    spineOccurrence m (spineIndex m (localSpineQ m s)) s =
      spineOccurrence m (spineIndex m (localSpineQ m s)) 0 := by
  unfold spineOccurrence
  apply Subtype.ext
  apply Prod.ext
  · rfl
  change ((caterpillarDatum m).edgePartition
    (occ m (spineIndex m (localSpineQ m s)))).Rel s 0
  rw [caterpillarDatum_edgePartition,
    catEdgePart_of_pair m _ (localSpine_isPair s),
    pairIndex_localSpine s hs0]
  exact pairPart_rel_zero m s.val s rfl

/-- **Exact normalized spine-fibre census.**  For nonzero sheet `s`, every
spine occurrence dangles except at the unique slope-two position
`2(s-1)`, where it is the central occurrence. -/
theorem spineIndexOccurrence_isDangling_iff {m : ℕ}
    (q : Fin (2 * m + 1)) (s : Fin (m + 2)) :
    IsDangling (caterpillarDatum m) (spineOccurrence m (spineIndex m q) s) ↔
      s.val ≠ 0 ∧ q.val ≠ localSpinePosition s := by
  constructor
  · intro hDangling
    constructor
    · intro hs0
      have hs : s = 0 := Fin.ext hs0
      subst s
      exact spineMain_survives (spineIndex_isSpine m q) hDangling
    · intro hq
      have hs0 : s.val ≠ 0 := by
        intro hs
        have hsFin : s = 0 := Fin.ext hs
        subst s
        exact spineMain_survives (spineIndex_isSpine m q) hDangling
      have hqFin : q = localSpineQ m s := Fin.ext hq
      subst q
      exact spineMain_survives (spineIndex_isSpine m (localSpineQ m s))
        (localSpineOccurrence_eq_main s hs0 ▸ hDangling)
  · rintro ⟨hs0, hq⟩
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · exact spineIndex_dangles_of_lt_local s hs0 q hlt
    · exact spineIndex_dangles_of_local_lt s hs0 q hgt

theorem exists_spineIndex_of_isSpine {m : ℕ} {i : Fin (6 * m + 3)}
    (hSpine : IsSpineEdge i) :
    ∃ q : Fin (2 * m + 1), i = spineIndex m q := by
  let q : Fin (2 * m + 1) := ⟨(i.val - 1) / 3, by
    have hi := i.isLt
    unfold IsSpineEdge at hSpine
    omega⟩
  refine ⟨q, ?_⟩
  apply Fin.ext
  simp only [spineIndex_val, q]
  unfold IsSpineEdge at hSpine
  omega

/-- **Exact source-facing spine census.**  The central sheet survives every
spine edge.  A nonzero sheet survives exactly on its own slope-two spine
edge `6(s-1)+1`; every other actual spine occurrence is dangling. -/
theorem spineOccurrence_isDangling_iff {m : ℕ}
    {i : Fin (6 * m + 3)} (hSpine : IsSpineEdge i) (s : Fin (m + 2)) :
    IsDangling (caterpillarDatum m) (spineOccurrence m i s) ↔
      s.val ≠ 0 ∧ i.val ≠ 6 * (s.val - 1) + 1 := by
  obtain ⟨q, rfl⟩ := exists_spineIndex_of_isSpine hSpine
  rw [spineIndexOccurrence_isDangling_iff]
  simp only [spineIndex_val, localSpinePosition]
  constructor
  · rintro ⟨hs0, hq⟩
    exact ⟨hs0, by omega⟩
  · rintro ⟨hs0, hi⟩
    exact ⟨hs0, by omega⟩

end DraismaVargas.LocalCases.CaterpillarSpine
