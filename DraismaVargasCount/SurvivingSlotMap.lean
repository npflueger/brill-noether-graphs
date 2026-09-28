import DraismaVargasCount.RowSlotMap

/-!
# One actual map from surviving source vertices to the request graph

Branch vertices use the member's existing core labels. Every surviving
divalent vertex has a unique address inside one actual ordered row; its
image uses the constructed integral row map.
-/

namespace DraismaVargas.Count.SurvivingSlotMap

open DraismaVargas.Infrastructure GluingDatum
open DraismaVargas.LocalCases W4StableSource FullDimensionalSource
open StableGraphIncidence
open RowWalk RowPosition RowRealizedPosition RowSlotOrientation RowSlotMap RowVertexEnumeration
open Utilities.Certificate.SubdivisionGraph

variable {target : CFGraph.{0}} {degree : ℕ} {data : GluingDatum target degree}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- A literal occurrence of an interior vertex in an actual stable row. -/
def InteriorAddress (fd : FullDimensionalSourcePresentation data coordinate) :=
  Σ path : StablePath data, Fin ((orderedRow fd.pathEnds path).length - 1)

noncomputable def addressVertex (fd : FullDimensionalSourcePresentation data coordinate)
    (address : InteriorAddress fd) : data.SourceVertex :=
  rowVertex fd address.1 (address.2.val + 1)

theorem addressVertex_valency (fd : FullDimensionalSourcePresentation data coordinate)
    (address : InteriorAddress fd) : nonDanglingValency data (addressVertex fd address) = 2 :=
  rowVertex_valency fd address.1 (by have := address.2.isLt; omega)

theorem addressVertex_injective (fd : FullDimensionalSourcePresentation data coordinate) :
    Function.Injective (addressVertex fd) := by
  rintro ⟨first, i⟩ ⟨second, j⟩ hEq
  change rowVertex fd first (i.val + 1) = rowVertex fd second (j.val + 1) at hEq
  have hPath := row_eq_of_interior_eq fd first second
    (by have := i.isLt; omega) (by have := j.isLt; omega) hEq
  subst second
  have hIndex := interior_injective fd first hEq
  subst j
  rfl

theorem exists_address (fd : FullDimensionalSourcePresentation data coordinate)
    (vertex : data.SourceVertex) (hValency : nonDanglingValency data vertex = 2) :
    ∃ address : InteriorAddress fd, addressVertex fd address = vertex := by
  obtain ⟨first, _, _, hSurvives, hIncident, _, _⟩ :=
    exists_pair_of_nonDanglingValency_two hValency
  let edge : NonDanglingEdge data := ⟨first, hSurvives⟩
  obtain ⟨i, hI⟩ := exists_interior_index fd edge.stablePath hValency
    (show OnRow data edge.stablePath first from ⟨hSurvives, rfl⟩) hIncident
  exact ⟨⟨edge.stablePath, i⟩, hI⟩

/-- The source's divalent surviving vertices, with their proved unique row
addresses. No enumeration or exhaustion field is postulated. -/
noncomputable def addressEquiv (fd : FullDimensionalSourcePresentation data coordinate) :
    InteriorAddress fd ≃ {vertex : data.SourceVertex // nonDanglingValency data vertex = 2} :=
  Equiv.ofBijective (fun address ↦ ⟨addressVertex fd address, addressVertex_valency fd address⟩)
    ⟨fun _ _ h ↦ addressVertex_injective fd (congrArg Subtype.val h), by
      rintro ⟨vertex, hValency⟩
      obtain ⟨address, hAddress⟩ := exists_address fd vertex hValency
      exact ⟨address, Subtype.ext hAddress⟩⟩

variable {n p : ℕ} (spec : Spec n p)
  (member : FibreMember spec.core (fun slot ↦ (spec.length slot : ℚ)) degree)
  (hClosed : member.Closed)

/-- The canonical image of one literal source interior address. -/
noncomputable def addressPoint (address : InteriorAddress member.fullDim) :
    (spec.scale (memberScale member) (memberScale_pos member)).Vertex :=
  rowPoint spec member hClosed (member.ident.row address.1) (address.2.val + 1)

/-- A single map on all surviving source vertices. Pendant vertices are not
silently assigned a location: extending across them is explicit retraction. -/
noncomputable def survivingPoint
    (vertex : {v : member.data.SourceVertex // 0 < nonDanglingValency member.data v}) :
    (spec.scale (memberScale member) (memberScale_pos member)).Vertex := by
  classical
  exact if hBranch : 3 ≤ nonDanglingValency member.data vertex.1 then
    (spec.scale (memberScale member) (memberScale_pos member)).coreVertex
      (member.ident.vertex ⟨vertex.1, hBranch⟩)
  else
    addressPoint spec member hClosed
      ((addressEquiv member.fullDim).symm ⟨vertex.1, by
        have hNotOne := NonDanglingValency.nonDanglingValency_ne_one member.data
          member.fullDim.connected vertex.1
        have := vertex.2
        omega⟩)

theorem survivingPoint_branch (branch : BranchVertex member.data) :
    survivingPoint spec member hClosed ⟨branch.1, by have := branch.2; omega⟩ =
      (spec.scale (memberScale member) (memberScale_pos member)).coreVertex
        (member.ident.vertex branch) := by
  classical
  simp only [survivingPoint, dif_pos branch.2]
  rfl

theorem survivingPoint_address (address : InteriorAddress member.fullDim) :
    survivingPoint spec member hClosed
      ⟨addressVertex member.fullDim address, by rw [addressVertex_valency]; omega⟩ =
        addressPoint spec member hClosed address := by
  classical
  have hNotBranch : ¬ 3 ≤ nonDanglingValency member.data
      (addressVertex member.fullDim address) := by rw [addressVertex_valency]; omega
  rw [survivingPoint, dif_neg hNotBranch]
  congr 1
  exact (addressEquiv member.fullDim).symm_apply_apply address


/-- Every vertex on the actual row, including its two ends, survives pruning. -/
theorem rowVertex_survives (fd : FullDimensionalSourcePresentation data coordinate)
    (path : StablePath data) (j : ℕ) (hj : j ≤ (orderedRow fd.pathEnds path).length) :
    0 < nonDanglingValency data (rowVertex fd path j) := by
  by_cases hZero : j = 0
  · subst j
    have h := start_branch fd path
    omega
  by_cases hFull : j = (orderedRow fd.pathEnds path).length
  · subst j
    have h := finish_branch fd path
    omega
  have hPred : j - 1 + 1 = j := by omega
  have hVal := rowVertex_valency fd path (j := j - 1) (by omega)
  rw [hPred] at hVal
  omega

/-- The single surviving-vertex map agrees with every constructed row map,
at endpoints and interior positions alike. -/
theorem survivingPoint_rowVertex (slot : Fin p) (j : ℕ)
    (hj : j ≤ (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length) :
    survivingPoint spec member hClosed
      ⟨rowVertex member.fullDim (member.ident.row.symm slot) j,
        rowVertex_survives member.fullDim _ j hj⟩ =
      rowPoint spec member hClosed slot j := by
  by_cases hZero : j = 0
  · subst j
    rw [rowPoint_zero]
    exact survivingPoint_branch spec member hClosed
      (startBranch member.fullDim (member.ident.row.symm slot))
  by_cases hFull : j = (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length
  · subst j
    rw [rowPoint_full]
    exact survivingPoint_branch spec member hClosed
      (finishBranch member.fullDim (member.ident.row.symm slot))
  have hPred : j - 1 + 1 = j := by omega
  let address : InteriorAddress member.fullDim :=
    ⟨member.ident.row.symm slot, ⟨j - 1, by omega⟩⟩
  have h := survivingPoint_address spec member hClosed address
  simpa only [addressVertex, addressPoint, address, hPred, Equiv.apply_symm_apply] using h



/-- A literal slot-interior image remembers which requested slot it lies on. -/
theorem slot_eq_of_rowPoint_eq_interior (first second : Fin p) (j : ℕ)
    (offset : Fin ((spec.scale (memberScale member) (memberScale_pos member)).length second - 1))
    (hEq : rowPoint spec member hClosed first j =
      (spec.scale (memberScale member) (memberScale_pos member)).interiorVertex second offset) :
    first = second := by
  unfold rowPoint Spec.pathVertex at hEq
  split_ifs at hEq with hZero hFull
  · simp only [Spec.coreVertex, Spec.interiorVertex, reduceCtorEq] at hEq
  · simp only [Spec.coreVertex, Spec.interiorVertex, reduceCtorEq] at hEq
  · exact congrArg Sigma.fst (Sum.inr.inj hEq)

/-- Exact inverse image of a request-slot interior under the single actual
source map. This is produced from the row enumeration, not assumed. -/
theorem survivingPoint_eq_interior_iff
    (vertex : {v : member.data.SourceVertex // 0 < nonDanglingValency member.data v})
    (slot : Fin p)
    (offset : Fin ((spec.scale (memberScale member) (memberScale_pos member)).length slot - 1)) :
    survivingPoint spec member hClosed vertex =
      (spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset ↔
    ∃ i : Fin ((orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length - 1),
      vertex.1 = rowVertex member.fullDim (member.ident.row.symm slot) (i.val + 1) ∧
      rowPoint spec member hClosed slot (i.val + 1) =
        (spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset := by
  classical
  constructor
  · intro hEq
    by_cases hBranch : 3 ≤ nonDanglingValency member.data vertex.1
    · rw [survivingPoint, dif_pos hBranch] at hEq
      simp only [Spec.coreVertex, Spec.interiorVertex, reduceCtorEq] at hEq
    · have hValency : nonDanglingValency member.data vertex.1 = 2 := by
        have := NonDanglingValency.nonDanglingValency_ne_one member.data
          member.fullDim.connected vertex.1
        have := vertex.2
        omega
      let address := (addressEquiv member.fullDim).symm ⟨vertex.1, hValency⟩
      have hAddress : addressVertex member.fullDim address = vertex.1 :=
        congrArg Subtype.val ((addressEquiv member.fullDim).apply_symm_apply ⟨vertex.1, hValency⟩)
      have hPoint : addressPoint spec member hClosed address =
          (spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset := by
        have hSurvive := survivingPoint_address spec member hClosed address
        have hVertex : (⟨addressVertex member.fullDim address,
            by rw [addressVertex_valency]; omega⟩ :
            {v : member.data.SourceVertex // 0 < nonDanglingValency member.data v}) = vertex :=
          Subtype.ext hAddress
        rw [hVertex] at hSurvive
        exact hSurvive.symm.trans hEq
      have hSlot := slot_eq_of_rowPoint_eq_interior spec member hClosed
        (member.ident.row address.1) slot (address.2.val + 1) offset hPoint
      have hPath : address.1 = member.ident.row.symm slot :=
        (member.ident.row.eq_symm_apply).mpr hSlot
      obtain ⟨path, i⟩ := address
      dsimp only at hPath
      subst path
      exact ⟨i, hAddress.symm, by
        simpa only [addressPoint, Equiv.apply_symm_apply] using hPoint⟩
  · rintro ⟨i, hVertex, hPoint⟩
    have hi : i.val + 1 ≤ (orderedRow member.fullDim.pathEnds (member.ident.row.symm slot)).length :=
      by have := i.isLt; omega
    have hSurvive := survivingPoint_rowVertex spec member hClosed slot (i.val + 1) hi
    have hVertex' : vertex =
        ⟨rowVertex member.fullDim (member.ident.row.symm slot) (i.val + 1),
          rowVertex_survives member.fullDim _ _ hi⟩ := Subtype.ext hVertex
    rw [hVertex']
    exact hSurvive.trans hPoint



/-- The actual finite pushforward of the canonical pendant-retracted fibre
along the single surviving-source map. Unlike the interior-only arithmetic
divisor, this definition retains every core coefficient. -/
noncomputable def survivingDivisor (root : member.target.V) :
    CFDiv (spec.scale (memberScale member) (memberScale_pos member)).graph := by
  classical
  exact fun point ↦
    ∑ vertex : {v : member.data.SourceVertex // 0 < nonDanglingValency member.data v},
      if survivingPoint spec member hClosed vertex = point then
        PendantRetraction.retractedFibre root (PendantRetraction.retractVertex vertex.1) else 0

/-- Exact coefficient identification with the arithmetic interior row pushforward
`orientedInteriorRowPushforward`. Core chips are retained by `survivingDivisor` but play no
role at an interior point; all zero-length collisions are included. -/
theorem survivingDivisor_interior (root : member.target.V) (slot : Fin p)
    (offset : Fin ((spec.scale (memberScale member) (memberScale_pos member)).length slot - 1)) :
    survivingDivisor spec member hClosed root
      ((spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset) =
    orientedInteriorRowPushforward spec member hClosed root (memberReverse spec member)
      ((spec.scale (memberScale member) (memberScale_pos member)).interiorVertex slot offset) := by
  classical
  rw [interiorRowPushforward_eq_row_sum]
  unfold survivingDivisor
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun i _ ↦
    (⟨rowVertex member.fullDim (member.ident.row.symm slot) (i.val + 1),
      rowVertex_survives member.fullDim _ _ (by have := i.isLt; omega)⟩ :
      {v : member.data.SourceVertex // 0 < nonDanglingValency member.data v})) ?_ ?_ ?_ ?_
  · intro i hi
    have hPoint := (Finset.mem_filter.mp hi).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [survivingPoint_rowVertex spec member hClosed slot (i.val + 1)
      (by have := i.isLt; omega)]
    exact hPoint
  · intro i _ j _ hEq
    exact interior_injective member.fullDim (member.ident.row.symm slot) (congrArg Subtype.val hEq)
  · intro vertex hVertex
    obtain ⟨i, hSource, hPoint⟩ := (survivingPoint_eq_interior_iff spec member hClosed
      vertex slot offset).mp (Finset.mem_filter.mp hVertex).2
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hPoint⟩, Subtype.ext hSource.symm⟩
  · intro i _
    rfl

/-- The full actual surviving-source pushforward satisfies the per-slot moment divisibility:
`2 ^ a` divides every slot moment when it divides the member scale. No term or coefficient
assumptions enter. -/
theorem survivingDivisor_slotMoment (root : member.target.V)
    (hInternal : ¬ IsLeafVertex member.target root) (hOdd : Odd member.oddMult)
    (a : ℕ) (hScale : 2 ^ a ∣ memberScale member) (slot : Fin p) :
    ((2 ^ a : ℕ) : ℤ) ∣ InteriorFiring.slotMoment
      (spec.scale (memberScale member) (memberScale_pos member))
      (survivingDivisor spec member hClosed root) slot := by
  have hMoment : InteriorFiring.slotMoment
      (spec.scale (memberScale member) (memberScale_pos member))
      (survivingDivisor spec member hClosed root) slot =
      InteriorFiring.slotMoment
      (spec.scale (memberScale member) (memberScale_pos member))
      (orientedInteriorRowPushforward spec member hClosed root (memberReverse spec member)) slot := by
    unfold InteriorFiring.slotMoment
    apply Finset.sum_congr rfl
    intro offset _
    rw [survivingDivisor_interior]
  rw [hMoment]
  exact orientedInteriorRowPushforward_slotMoment spec member hClosed hOdd hInternal
    (memberReverse spec member) a hScale slot


end DraismaVargas.Count.SurvivingSlotMap

