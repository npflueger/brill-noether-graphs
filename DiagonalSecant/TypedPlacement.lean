module

public import DiagonalSecant.TypedRows
public import DraismaVargasCount.DegeneratePlacement

@[expose] public section

/-!
# Placing a typed frame on a target subdivision it only partly fills

The marked twin of
the public `DegeneratePlacement`, statement for statement, with `FibreMember` replaced by a typed
frame `κ : TypedFrame B.core mark types degree` closed at a natural-number request
`y : Fin Q → ℕ`, and the unmarked row layer by `TypedRows`.

Only one thing changes in substance: a **mark** is a marked branch vertex (`MarkedBranchVertex`)
of surviving valency two, and it is placed, like every marked branch vertex, at the big core
vertex carrying its own label, `B.coreVertex (κ.ident.vertex ⟨u_G, _⟩)`; by
`MarkedCoreIdentification.vertex_mark` that label is `mark j`. The interior vertices of the
marked rows (surviving valency two, not marks) are placed at their oriented offsets along the
slot, exactly as in the public placement. The datum-level layers, `CanonicalSurvivor` (the
pendant retraction's representative) and `PendantDivisorTransport.push`, are reused verbatim, as
are the datum-free path-position lemmas of `DegeneratePlacement` §4 (`pathVertex_interior`,
`pathVertex_eq_interior_iff`, `slot_eq_of_pathVertex_eq_interior`).

Nothing here is about rank, and no member is produced; the odd-denominator receipt of the
interior coefficients is `TypedMoments`.
-/

namespace DiagonalSecant.TypedPlacement

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.PendantRetraction DraismaVargas.Count.CanonicalSurvivor
open DiagonalSecant.TypedRows
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.ExplicitPotential (Core)

variable {N Q m degree : ℕ} {mark : Fin m → Fin N} {types : Fin m → ℕ}

/-! ## 1.  The realization of a closed typed frame at a natural request -/

section Realization

variable {core : Core N Q} (y : Fin Q → ℕ) (κ : TypedFrame core mark types degree)

/-- The coordinates of `κ` at the request `y`, read as rationals. -/
noncomputable def coords : Fin Q → ℚ := κ.coordsAt fun e ↦ (y e : ℚ)

/-- Closedness at `y`: every coordinate nonnegative. -/
def Closed : Prop := ∀ col, 0 ≤ coords y κ col

/-- The target-edge lengths of `κ` at `y`. -/
noncomputable def targetLength (edge : κ.target.edges) : ℚ :=
  coords y κ (κ.fullDim.labelling.targetEdge.symm edge)

/-- **The common scale** of the realization: the common denominator of the target lengths and
of the source lengths `z / index` (`GluingDatum.rationalRealizationScale`). The twin of
`RowRealizedPosition.memberScale`. -/
noncomputable def scale : ℕ := κ.data.rationalRealizationScale (targetLength y κ)

theorem scale_pos : 0 < scale y κ := κ.data.rationalRealizationScale_pos _

variable (hClosed : Closed y κ)

/-- **The canonical closed-cone integral realization** of `κ` at `y`
(`RowRealizedPosition.memberRealization`). -/
noncomputable def realization : κ.data.NonnegativeIntegralRealization :=
  NonnegativeIntegralRealization.ofNonnegativeRational κ.data (targetLength y κ)
    (fun _ ↦ hClosed _)

/-- The actual row of the slot `e`. -/
abbrev rowOf (e : Fin Q) : MarkedStablePath κ.data (markSet κ.markSource) := κ.ident.row.symm e

theorem integralPrefix_cast (e : Fin Q) (j : ℕ) :
    (integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e) j : ℚ) =
      (scale y κ : ℚ) * prefixPosition κ.fullDim (coords y κ) (rowOf κ e) j :=
  TypedRows.integralPrefix_cast κ.fullDim (coords y κ) hClosed _ _

/-- **The full prefix of the actual row of `e` is the scaled request `y e`**: the matrix row is
`(A z) (row path) = y (slot …)` (`MarkedFrameBase.mulVec_coordsAt`), and `κ.slot` reads the
matrix row of `κ.ident.row.symm e` as `e`. -/
theorem integralPrefix_full (e : Fin Q) :
    integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e)
      (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length = scale y κ * y e := by
  have h := integralPrefix_cast y κ hClosed e (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length
  rw [prefixPosition_full] at h
  have hrow : κ.matrix.mulVec (coords y κ) (κ.fullDim.labelling.row (rowOf κ e)) = (y e : ℚ) := by
    rw [coords, MarkedFrameBase.mulVec_coordsAt]
    simp only [MarkedFrameBase.slot, rowOf, Equiv.trans_apply, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply]
  have h' : (integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e)
      (orderedRow κ.fullDim.pathEnds (rowOf κ e)).length : ℚ) = (scale y κ : ℚ) * (y e : ℚ) := by
    rw [h]
    exact congrArg (fun t ↦ (scale y κ : ℚ) * t) hrow
  exact_mod_cast h'

end Realization

/-! ## 2.  Orientation of a row against its slot -/

section Orientation

variable {core : Core N Q} (κ : TypedFrame core mark types degree)

/-- **The two ends of the actual row of a slot are the slot's two labels**, in one of the two
orders (`DegeneratePlacement.endpoints`). Needs only `κ.ident` and looplessness of the core. -/
theorem endpoints (hLoopless : ∀ e : Fin Q, core.tail e ≠ core.head e) (e : Fin Q) :
    (κ.ident.vertex (startBranch κ.fullDim (rowOf κ e)) = core.tail e ∧
      κ.ident.vertex (finishBranch κ.fullDim (rowOf κ e)) = core.head e) ∨
    (κ.ident.vertex (startBranch κ.fullDim (rowOf κ e)) = core.head e ∧
      κ.ident.vertex (finishBranch κ.fullDim (rowOf κ e)) = core.tail e) := by
  classical
  have hEndpoint (label : Fin N) (hLabel : label = core.tail e ∨ label = core.head e) :
      label = κ.ident.vertex (startBranch κ.fullDim (rowOf κ e)) ∨
      label = κ.ident.vertex (finishBranch κ.fullDim (rowOf κ e)) := by
    have hPos : 0 < markedIncidenceCount κ.data (markSet κ.markSource)
        (κ.ident.vertex.symm label).1 (rowOf κ e) := by
      rw [κ.ident.incidence, Equiv.apply_symm_apply]
      unfold coreIncidence
      rcases hLabel with rfl | rfl <;> split_ifs <;> omega
    rw [markedIncidenceCount, Finset.card_pos] at hPos
    obtain ⟨edge, hEdge⟩ := hPos
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges] at hEdge
    rcases branch_incident_eq_endpoint κ.fullDim (rowOf κ e) (κ.ident.vertex.symm label)
        ⟨edge.2, hEdge.2⟩ hEdge.1 with h | h
    · exact Or.inl (by
        simpa only [Equiv.apply_symm_apply] using congrArg κ.ident.vertex (Subtype.ext h))
    · exact Or.inr (by
        simpa only [Equiv.apply_symm_apply] using congrArg κ.ident.vertex (Subtype.ext h))
  have hTail := hEndpoint (core.tail e) (Or.inl rfl)
  have hHead := hEndpoint (core.head e) (Or.inr rfl)
  have hNe := hLoopless e
  rcases hTail with hTail | hTail <;> rcases hHead with hHead | hHead
  · exact False.elim (hNe (hTail.trans hHead.symm))
  · exact Or.inl ⟨hTail.symm, hHead.symm⟩
  · exact Or.inr ⟨hHead.symm, hTail.symm⟩
  · exact False.elim (hNe (hTail.trans hHead.symm))

/-- `true` when the actual row runs against its slot's stored orientation. -/
noncomputable def reverse (e : Fin Q) : Bool :=
  decide (κ.ident.vertex (startBranch κ.fullDim (rowOf κ e)) ≠ core.tail e)

theorem reverse_endpoints (hLoopless : ∀ e : Fin Q, core.tail e ≠ core.head e) (e : Fin Q) :
    κ.ident.vertex (startBranch κ.fullDim (rowOf κ e)) =
        (if reverse κ e then core.head e else core.tail e) ∧
    κ.ident.vertex (finishBranch κ.fullDim (rowOf κ e)) =
        (if reverse κ e then core.tail e else core.head e) := by
  classical
  rcases endpoints κ hLoopless e with ⟨hStart, hFinish⟩ | ⟨hStart, hFinish⟩
  · have hRev : reverse κ e = false := by
      unfold reverse
      exact decide_eq_false (not_not.mpr hStart)
    simp only [hRev, Bool.false_eq_true, ↓reduceIte, hStart, hFinish, and_self]
  · have hRev : reverse κ e = true := by
      unfold reverse
      exact decide_eq_true (by rw [hStart]; exact (hLoopless e).symm)
    simp only [hRev, ↓reduceIte, hStart, hFinish, and_self]

end Orientation

/-! ## 2b.  The pullback fibre -/

section Fibre

variable {core : Core N Q} (κ : TypedFrame core mark types degree)

/-- The literal pullback-fibre weight over a target vertex. -/
noncomputable def fibre (root : κ.target.V) : CFDiv κ.data.sourceGraph :=
  fun vertex ↦ if vertex.1.1 = root then
    ((κ.data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) else 0

theorem fibre_nonneg (root : κ.target.V) (vertex : κ.data.SourceVertex) :
    0 ≤ fibre κ root vertex := by
  unfold fibre
  split_ifs <;> positivity

/-- The weight of a mark in the fibre over its own image is its local degree. -/
theorem fibre_mark (j : Fin m) :
    fibre κ (κ.markSource j).1.1 (κ.markSource j) = (markIndex κ.data (κ.markSource j) : ℤ) := by
  unfold fibre markIndex
  rw [ite_eq_left rfl]

end Fibre

/-! ## 3.  The placement -/

section Placement

variable (B : Spec N Q) (y : Fin Q → ℕ) (κ : TypedFrame B.core mark types degree)
  (hClosed : Closed y κ)

/-- The base point for the pendant retraction: the core is nonempty, and every core vertex is
the label of a marked branch vertex, of positive surviving valency (`≥ 3`, or a mark of
valency two by `markValency`). -/
theorem surviving_nonempty :
    ∃ vertex : κ.data.SourceVertex, 0 < nonDanglingValency κ.data vertex := by
  refine ⟨(κ.ident.vertex.symm ⟨0, B.core_nonempty⟩).1, ?_⟩
  rcases (κ.ident.vertex.symm ⟨0, B.core_nonempty⟩).2 with h | h
  · omega
  · rw [κ.fullDim.markValency _ h]; omega

/-- Every marked branch vertex has positive surviving valency. -/
theorem markedBranch_pos (branch : MarkedBranchVertex κ.data (markSet κ.markSource)) :
    0 < nonDanglingValency κ.data branch.1 := by
  rcases branch.2 with h | h
  · omega
  · rw [κ.fullDim.markValency _ h]; omega

variable (hFit : ∀ e : Fin Q, scale y κ * y e ≤ B.length e)

include hFit in
theorem integralPrefix_le (e : Fin Q) (j : ℕ) :
    integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e) j ≤ B.length e := by
  have hLe := integralPrefix_le_full κ.fullDim (realization y κ hClosed) (rowOf κ e) j
  rw [integralPrefix_full y κ hClosed e] at hLe
  exact hLe.trans (hFit e)

/-- The integral distance from the slot's **tail** at which the `j`-th vertex of the actual row
of `e` is placed, reflected when the row runs against the slot. -/
noncomputable def offsetVal (e : Fin Q) (j : ℕ) : ℕ :=
  if reverse κ e then
    B.length e - integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e) j
  else
    integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e) j

include hFit in
theorem offsetVal_le (e : Fin Q) (j : ℕ) : offsetVal B y κ hClosed e j ≤ B.length e := by
  have := integralPrefix_le B y κ hClosed hFit e j
  unfold offsetVal
  split_ifs <;> omega

/-- The placement as a path position of `B`. -/
noncomputable def position (e : Fin Q) (j : ℕ) : B.PathPosition e :=
  ⟨offsetVal B y κ hClosed e j, by have := offsetVal_le B y κ hClosed hFit e j; omega⟩

@[simp] theorem position_val (e : Fin Q) (j : ℕ) :
    (position B y κ hClosed hFit e j).val = offsetVal B y κ hClosed e j := rfl

/-- The placement as a vertex of `B`. -/
noncomputable def point (e : Fin Q) (j : ℕ) : B.Vertex :=
  B.pathVertex e (position B y κ hClosed hFit e j)

/-- The image of one literal interior row address. -/
noncomputable def addressPoint (address : InteriorAddress κ.fullDim) : B.Vertex :=
  point B y κ hClosed hFit (κ.ident.row address.1) (address.2.val + 1)

/-- **The map on surviving source vertices.** Marked branch vertices (surviving valency `≥ 3`,
or marks) go to the big core vertex of their own label; every other surviving vertex has
valency two, is not a mark, and goes to its unique interior row address. -/
noncomputable def survivingPoint
    (vertex : {v : κ.data.SourceVertex // 0 < nonDanglingValency κ.data v}) : B.Vertex := by
  classical
  exact if hBranch : 3 ≤ nonDanglingValency κ.data vertex.1 ∨ vertex.1 ∈ markSet κ.markSource then
    B.coreVertex (κ.ident.vertex ⟨vertex.1, hBranch⟩)
  else
    addressPoint B y κ hClosed hFit
      ((addressEquiv κ.fullDim).symm ⟨vertex.1, by
        have hNotOne := NonDanglingValency.nonDanglingValency_ne_one κ.data κ.fullDim.valid.1
          vertex.1
        have := vertex.2
        push Not at hBranch
        exact ⟨by omega, hBranch.2⟩⟩)

theorem survivingPoint_branch (branch : MarkedBranchVertex κ.data (markSet κ.markSource)) :
    survivingPoint B y κ hClosed hFit ⟨branch.1, markedBranch_pos B κ branch⟩ =
      B.coreVertex (κ.ident.vertex branch) := by
  classical
  simp only [survivingPoint, dite_eq_left branch.2]
  rfl

theorem survivingPoint_address (address : InteriorAddress κ.fullDim) :
    survivingPoint B y κ hClosed hFit
      ⟨addressVertex κ.fullDim address, by rw [addressVertex_valency]; omega⟩ =
        addressPoint B y κ hClosed hFit address := by
  classical
  have hNotBranch : ¬ (3 ≤ nonDanglingValency κ.data (addressVertex κ.fullDim address) ∨
      addressVertex κ.fullDim address ∈ markSet κ.markSource) := by
    rw [addressVertex_valency]
    push Not
    exact ⟨by omega, addressVertex_notMem κ.fullDim address⟩
  rw [survivingPoint, dite_eq_right hNotBranch]
  congr 1
  exact (addressEquiv κ.fullDim).symm_apply_apply address

/-- The map on **every** source vertex, pendant vertices included, through the canonical
surviving representative of the pendant retraction class. -/
noncomputable def sourcePoint (vertex : κ.data.SourceVertex) : B.Vertex :=
  survivingPoint B y κ hClosed hFit
    (representative κ.fullDim.valid.1 (surviving_nonempty B κ) vertex)

theorem sourcePoint_of_retract {first second : κ.data.SourceVertex}
    (hEq : retractVertex first = retractVertex second) :
    sourcePoint B y κ hClosed hFit first = sourcePoint B y κ hClosed hFit second := by
  unfold sourcePoint
  refine congrArg _ (Subtype.ext ?_)
  exact congrArg Subtype.val
    ((representative_eq_iff κ.fullDim.valid.1 (surviving_nonempty B κ) first _).mpr
      (hEq.trans (representative_class κ.fullDim.valid.1 (surviving_nonempty B κ) second)))

theorem sourcePoint_survivor
    (vertex : {v : κ.data.SourceVertex // 0 < nonDanglingValency κ.data v}) :
    sourcePoint B y κ hClosed hFit vertex.1 = survivingPoint B y κ hClosed hFit vertex := by
  unfold sourcePoint
  rw [representative_fixes κ.fullDim.valid.1 (surviving_nonempty B κ) vertex]

/-- A marked branch vertex is placed at the big core vertex of its label. -/
theorem sourcePoint_branch (branch : MarkedBranchVertex κ.data (markSet κ.markSource)) :
    sourcePoint B y κ hClosed hFit branch.1 = B.coreVertex (κ.ident.vertex branch) :=
  (sourcePoint_survivor B y κ hClosed hFit ⟨branch.1, markedBranch_pos B κ branch⟩).trans
    (survivingPoint_branch B y κ hClosed hFit branch)

/-- **A mark is placed at the big core vertex of the mark** (`vertex_mark`). -/
theorem sourcePoint_mark (j : Fin m) :
    sourcePoint B y κ hClosed hFit (κ.markSource j) = B.coreVertex (mark j) := by
  rw [sourcePoint_branch B y κ hClosed hFit ⟨κ.markSource j, Or.inr (mem_markSet κ.markSource j)⟩,
    κ.ident.vertex_mark j]

/-- **The big-side divisor**: the finite pushforward of the pullback fibre along the placement. -/
noncomputable def divisor (root : κ.target.V) : CFDiv B.graph :=
  PendantDivisorTransport.push (G := κ.data.sourceGraph) (H := B.graph)
    (sourcePoint B y κ hClosed hFit) (fibre κ root)

theorem divisor_apply (root : κ.target.V) (v : B.Vertex) :
    divisor B y κ hClosed hFit root v =
      ∑ raw : κ.data.SourceVertex,
        if sourcePoint B y κ hClosed hFit raw = v then fibre κ root raw else 0 := rfl

theorem divisor_effective (root : κ.target.V) : effective (divisor B y κ hClosed hFit root) :=
  PendantDivisorTransport.push_effective _ (fibre_nonneg κ root)

theorem divisor_degree (root : κ.target.V) :
    deg (divisor B y κ hClosed hFit root) = (degree : ℤ) :=
  (PendantDivisorTransport.push_degree (G := κ.data.sourceGraph) (H := B.graph)
    (sourcePoint B y κ hClosed hFit) (fibre κ root)).trans
      (κ.data.sum_sourceVertex_localDegree_over root)

/-! ### The fibre of the placement over an interior vertex -/

/-- Every surviving source vertex is a marked branch vertex or an interior row address. -/
theorem survivor_cases
    (vertex : {v : κ.data.SourceVertex // 0 < nonDanglingValency κ.data v}) :
    (∃ b : MarkedBranchVertex κ.data (markSet κ.markSource), vertex.1 = b.1) ∨
      (∃ a : InteriorAddress κ.fullDim, vertex.1 = addressVertex κ.fullDim a) := by
  classical
  by_cases hBranch : 3 ≤ nonDanglingValency κ.data vertex.1 ∨ vertex.1 ∈ markSet κ.markSource
  · exact Or.inl ⟨⟨vertex.1, hBranch⟩, rfl⟩
  · push Not at hBranch
    have hNotOne := NonDanglingValency.nonDanglingValency_ne_one κ.data κ.fullDim.valid.1 vertex.1
    have hTwo : nonDanglingValency κ.data vertex.1 = 2 := by have := vertex.2; omega
    obtain ⟨a, ha⟩ := exists_address κ.fullDim vertex.1 hTwo hBranch.2
    exact Or.inr ⟨a, ha.symm⟩

/-- **The fibre of the placement over an interior vertex** is the retraction class of the row
occurrences of its slot placed there (`DegeneratePlacement.sourcePoint_eq_interior_iff`). -/
theorem sourcePoint_eq_interior_iff (e : Fin Q) (o : Fin (B.length e - 1))
    (raw : κ.data.SourceVertex) :
    sourcePoint B y κ hClosed hFit raw = B.interiorVertex e o ↔
      ∃ i : Fin ((orderedRow κ.fullDim.pathEnds (rowOf κ e)).length - 1),
        retractVertex raw =
          retractVertex (rowVertex κ.fullDim.pathEnds (rowOf κ e) (i.val + 1)) ∧
        offsetVal B y κ hClosed e (i.val + 1) = o.val + 1 := by
  classical
  constructor
  · intro h
    have hRep := representative_class κ.fullDim.valid.1 (surviving_nonempty B κ) raw
    rcases survivor_cases B κ (representative κ.fullDim.valid.1 (surviving_nonempty B κ) raw)
      with ⟨b, hb⟩ | ⟨a, ha⟩
    · have hCore : sourcePoint B y κ hClosed hFit raw = B.coreVertex (κ.ident.vertex b) := by
        have hEq : representative κ.fullDim.valid.1 (surviving_nonempty B κ) raw =
            ⟨b.1, markedBranch_pos B κ b⟩ := Subtype.ext hb
        unfold sourcePoint
        rw [hEq, survivingPoint_branch]
      rw [hCore] at h
      exact absurd h (by simp [Spec.coreVertex, Spec.interiorVertex])
    · have hAddr : sourcePoint B y κ hClosed hFit raw = addressPoint B y κ hClosed hFit a := by
        have hEq : representative κ.fullDim.valid.1 (surviving_nonempty B κ) raw =
            ⟨addressVertex κ.fullDim a, by rw [addressVertex_valency]; omega⟩ := Subtype.ext ha
        unfold sourcePoint
        rw [hEq, survivingPoint_address]
      rw [hAddr] at h
      obtain ⟨path, index⟩ := a
      simp only [addressPoint, point] at h
      have hSlot : κ.ident.row path = e := DegeneratePlacement.slot_eq_of_pathVertex_eq_interior B h
      have hPath : path = rowOf κ e := by
        rw [rowOf, ← hSlot, Equiv.symm_apply_apply]
      subst hPath
      refine ⟨index, hRep.trans (congrArg retractVertex ha), ?_⟩
      rw [Equiv.apply_symm_apply] at h
      exact (DegeneratePlacement.pathVertex_eq_interior_iff B e _ o).mp h
  · rintro ⟨i, hClass, hOffset⟩
    have hSurv : 0 < nonDanglingValency κ.data (addressVertex κ.fullDim
        (⟨rowOf κ e, i⟩ : InteriorAddress κ.fullDim)) := by
      have := addressVertex_valency κ.fullDim (⟨rowOf κ e, i⟩ : InteriorAddress κ.fullDim)
      omega
    have hStep : sourcePoint B y κ hClosed hFit
        (addressVertex κ.fullDim (⟨rowOf κ e, i⟩ : InteriorAddress κ.fullDim)) =
        addressPoint B y κ hClosed hFit ⟨rowOf κ e, i⟩ :=
      (sourcePoint_survivor B y κ hClosed hFit ⟨_, hSurv⟩).trans
        (survivingPoint_address B y κ hClosed hFit _)
    calc sourcePoint B y κ hClosed hFit raw
        = sourcePoint B y κ hClosed hFit
            (addressVertex κ.fullDim (⟨rowOf κ e, i⟩ : InteriorAddress κ.fullDim)) :=
          sourcePoint_of_retract B y κ hClosed hFit hClass
      _ = addressPoint B y κ hClosed hFit ⟨rowOf κ e, i⟩ := hStep
      _ = B.interiorVertex e o := by
          show point B y κ hClosed hFit (κ.ident.row (κ.ident.row.symm e)) (i.val + 1) =
            B.interiorVertex e o
          rw [Equiv.apply_symm_apply]
          show B.pathVertex e (position B y κ hClosed hFit e (i.val + 1)) = _
          rw [DegeneratePlacement.pathVertex_eq_interior_iff]
          exact hOffset

include hFit in
theorem offsetVal_eq_iff (e : Fin Q) (o : Fin (B.length e - 1)) (j : ℕ) :
    offsetVal B y κ hClosed e j = o.val + 1 ↔
      integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e) j =
        (if reverse κ e then B.length e - (o.val + 1) else o.val + 1) := by
  have hPrefix := integralPrefix_le B y κ hClosed hFit e j
  have hBound := o.isLt
  unfold offsetVal
  split_ifs <;> omega

/-- **The coefficient of the big-side divisor at an interior vertex** is the collision
coefficient of the actual row at the oriented offset (`DegeneratePlacement.divisor_interior`). -/
theorem divisor_interior (root : κ.target.V) (e : Fin Q) (o : Fin (B.length e - 1)) :
    divisor B y κ hClosed hFit root (B.interiorVertex e o) =
      collisionCoefficient κ.fullDim (realization y κ hClosed) root (rowOf κ e)
        (if reverse κ e then B.length e - (o.val + 1) else o.val + 1) := by
  classical
  rw [divisor_apply, collisionCoefficient_eq_raw_fibre_sum]
  refine Finset.sum_congr rfl fun raw _ ↦ ?_
  have hCond : (sourcePoint B y κ hClosed hFit raw = B.interiorVertex e o) ↔
      (∃ i : Fin ((orderedRow κ.fullDim.pathEnds (rowOf κ e)).length - 1),
        retractVertex raw =
            retractVertex (rowVertex κ.fullDim.pathEnds (rowOf κ e) (i.val + 1)) ∧
          integralPrefix κ.fullDim (realization y κ hClosed) (rowOf κ e) (i.val + 1) =
            (if reverse κ e then B.length e - (o.val + 1) else o.val + 1)) := by
    rw [sourcePoint_eq_interior_iff]
    exact exists_congr fun i ↦
      and_congr_right fun _ ↦ offsetVal_eq_iff B y κ hClosed hFit e o (i.val + 1)
  by_cases hRoot : raw.1.1 = root
  · simp only [fibre, hRoot, ite_true, true_and]
    by_cases hHit : sourcePoint B y κ hClosed hFit raw = B.interiorVertex e o
    · rw [ite_eq_left hHit, ite_eq_left (hCond.mp hHit)]
    · rw [ite_eq_right hHit, ite_eq_right fun hx ↦ hHit (hCond.mpr hx)]
  · simp only [fibre, hRoot, ite_false, false_and, ite_false, ite_self]

end Placement

end DiagonalSecant.TypedPlacement
