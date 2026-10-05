import GenusSixExistence.BrillNoetherRank.Tripod.GluingLayout
import GenusSixExistence.BrillNoetherRank.Tripod.GluingPieceIdent
import DraismaVargasCount.RowWalk
import DraismaVargas.LocalCases.OrientedTraversal
import DraismaVargas.LocalCases.TraversalPresentation

/-!
# The three stages of the gluing, as layouts

The generic layouts of `GluingLayout` at the member `ψ` and a placement `π`:

* **stage zero** (`exists_layout₀`): the stable paths of `ψ` as oriented chains from the tail
  vertex of their slot to its head vertex, along `orderedRow`;
* **the bridge** (`pieceLabels_of_labelData`): label data at the third stage, on
  `refine₃ ψ.data π`, are piece labels of the glued old paths with the requested lengths;
* **the transport** (`labelData₃_of_gluing`): an open gluing gives label data at the third stage,
  with positive lengths.

`GluingPositivity.exists_pieceLabels` and `GluingWellDefined.placement_forced` are assembled from
these here (`Chains.exists_pieceLabels_of_open`, `Chains.placement_forced'`). Prose:
`Research/genus-six-brill-noether-rank.md`, §5.2 (Positivity and change-minimality) and §5.5 (The
bijection, "Well defined").
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount (incidenceCount)
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.OrientedTraversal (walkVertex walkVertex_incident walkVertex_succ_incident
  walkVertex_ne_succ walkVertex_succ_valency walkVertex_length walkVertex_succ walkVertex_zero)
open DraismaVargas.Count.RowWalk (orderedRow startVertex startEdge mem_orderedRow_iff orderedRow_nodup
  orderedRow_chain startEdge_isPathEnd startEdge_stablePath startEdge_mem_orderedRow
  orderedRow_head?)
open Utilities.Certificate.ExplicitPotential (Core)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion
open GenusSixExistence.Tripod.Gadget

namespace Chains

/-! ## 1. Stage zero: the stable paths of a member as oriented chains -/

section Stage0

variable {n p : ℕ} {core : Core n p} {yG : Fin p → ℚ} {d : ℕ}

/-- The branch vertices of a member, by their labels. -/
def V₀ (ψ : FibreMember core yG d) : Fin n → ψ.data.SourceVertex :=
  fun a ↦ (ψ.ident.vertex.symm a).1

theorem V₀_injective (ψ : FibreMember core yG d) : Function.Injective (V₀ ψ) := fun _ _ h ↦
  ψ.ident.vertex.symm.injective (Subtype.ext h)

theorem V₀_vertex (ψ : FibreMember core yG d) (b : BranchVertex ψ.data) :
    V₀ ψ (ψ.ident.vertex b) = b.1 := by
  unfold V₀; rw [Equiv.symm_apply_apply]

theorem notMem_range_V₀ (ψ : FibreMember core yG d) {v : ψ.data.SourceVertex}
    (hv : nonDanglingValency ψ.data v = 2) : v ∉ Set.range (V₀ ψ) := by
  rintro ⟨a, rfl⟩
  have := (ψ.ident.vertex.symm a).2
  unfold V₀ at hv
  omega

theorem nonDanglingValency_pos_of_incident {S : CFGraph} {k : ℕ} {E : GluingDatum S k}
    {x : E.SourceEdge} (hx : ¬ IsDangling E x) {v : E.SourceVertex} (hv : Incident E x v) :
    0 < nonDanglingValency E v := by
  rw [← StablePathCount.card_incidentEdges]
  exact Finset.card_pos.mpr ⟨⟨x, hx⟩, (StablePathCount.mem_incidentEdges _ _ _).mpr hv⟩

variable (ψ : FibreMember core yG d) (P : StablePath ψ.data)

/-- The ordered walk of a stable path of `ψ`, as oriented edges. -/
def walkOE : List (OEdge ψ.data) :=
  List.ofFn fun k : Fin (orderedRow ψ.fullDim.pathEnds P).length ↦
    ((orderedRow ψ.fullDim.pathEnds P)[k],
      walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds P) (startVertex ψ.fullDim.pathEnds P) k,
      walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds P) (startVertex ψ.fullDim.pathEnds P)
        (k + 1))

theorem length_walkOE : (walkOE ψ P).length = (orderedRow ψ.fullDim.pathEnds P).length := by
  simp [walkOE]

theorem getElem_walkOE {k : ℕ} (hk : k < (walkOE ψ P).length) :
    (walkOE ψ P)[k] = ((orderedRow ψ.fullDim.pathEnds P)[k]'(by
        rwa [length_walkOE] at hk),
      walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds P) (startVertex ψ.fullDim.pathEnds P) k,
      walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds P) (startVertex ψ.fullDim.pathEnds P)
        (k + 1)) := by
  simp [walkOE]

theorem map_fst_walkOE : (walkOE ψ P).map Prod.fst = orderedRow ψ.fullDim.pathEnds P := by
  simp only [walkOE, List.map_ofFn]
  exact List.ofFn_getElem

theorem row_nodup : (orderedRow ψ.fullDim.pathEnds P).Nodup := orderedRow_nodup _ P

theorem row_survives : ∀ edge ∈ orderedRow ψ.fullDim.pathEnds P, ¬ IsDangling ψ.data edge :=
  fun edge h ↦ ((mem_orderedRow_iff _ P edge).mp h).survives

theorem row_start : ∀ h : 0 < (orderedRow ψ.fullDim.pathEnds P).length,
    IsPathEnd ψ.data (orderedRow ψ.fullDim.pathEnds P)[0] (startVertex ψ.fullDim.pathEnds P) :=
  fun h ↦ DraismaVargas.Count.RowPosition.orderedRow_start ψ.fullDim P h

theorem good_walkOE : ∀ c ∈ walkOE ψ P, Good ψ.data c := by
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hc
  rw [getElem_walkOE]
  have hk' : k < (orderedRow ψ.fullDim.pathEnds P).length := by rwa [length_walkOE] at hk
  refine ⟨row_survives ψ P _ (List.getElem_mem hk'), ?_, walkVertex_succ_incident hk',
    (walkVertex_ne_succ hk').symm⟩
  exact walkVertex_incident (row_nodup ψ P) (row_survives ψ P) (orderedRow_chain _ P)
    (row_start ψ P) hk'

theorem isChain_walkOE : (walkOE ψ P).IsChain (Link ψ.data (V₀ ψ)) := by
  rw [List.isChain_iff_getElem]
  intro k hk
  rw [getElem_walkOE, getElem_walkOE]
  have hk' : k + 1 < (orderedRow ψ.fullDim.pathEnds P).length := by rwa [length_walkOE] at hk
  have hv := walkVertex_succ_valency (row_nodup ψ P) (row_survives ψ P) (orderedRow_chain _ P)
    (row_start ψ P) hk'
  exact ⟨rfl, hv, notMem_range_V₀ ψ hv⟩

theorem row_ne_nil : orderedRow ψ.fullDim.pathEnds P ≠ [] :=
  List.ne_nil_of_mem (startEdge_mem_orderedRow _ P)

theorem walkOE_ne_nil : walkOE ψ P ≠ [] := by
  intro h
  have := congrArg List.length h
  rw [length_walkOE] at this
  exact row_ne_nil ψ P (List.eq_nil_of_length_eq_zero this)

theorem head_walkOE :
    ((walkOE ψ P).head (walkOE_ne_nil ψ P)).2.1 = startVertex ψ.fullDim.pathEnds P := by
  rw [List.head_eq_getElem, getElem_walkOE]
  rfl

theorem last_walkOE :
    ((walkOE ψ P).getLast (walkOE_ne_nil ψ P)).2.2 =
      walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds P) (startVertex ψ.fullDim.pathEnds P)
        (orderedRow ψ.fullDim.pathEnds P).length := by
  rw [List.getLast_eq_getElem, getElem_walkOE]
  have hpos : 0 < (orderedRow ψ.fullDim.pathEnds P).length :=
    List.length_pos_of_ne_nil (row_ne_nil ψ P)
  show walkVertex _ _ _ ((walkOE ψ P).length - 1 + 1) = _
  rw [length_walkOE, Nat.sub_add_cancel hpos]

/-- The start of the walk is a branch vertex. -/
theorem three_le_start : 3 ≤ nonDanglingValency ψ.data (startVertex ψ.fullDim.pathEnds P) := by
  have hpos : 0 < (orderedRow ψ.fullDim.pathEnds P).length :=
    List.length_pos_of_ne_nil (row_ne_nil ψ P)
  have hend := row_start ψ P hpos
  have h0 := nonDanglingValency_pos_of_incident
    (row_survives ψ P _ (List.getElem_mem hpos)) hend.1
  have h1 := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _
    ψ.fullDim.valid.1 (startVertex ψ.fullDim.pathEnds P)
  have h2 := hend.2
  omega

/-- The end of the walk is a branch vertex. -/
theorem three_le_finish :
    3 ≤ nonDanglingValency ψ.data (walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds P)
      (startVertex ψ.fullDim.pathEnds P) (orderedRow ψ.fullDim.pathEnds P).length) := by
  set row := orderedRow ψ.fullDim.pathEnds P with hrow
  set st := startVertex ψ.fullDim.pathEnds P with hst
  have hpos : 0 < row.length := List.length_pos_of_ne_nil (row_ne_nil ψ P)
  have hlast : row.length - 1 < row.length := by omega
  have hinc : Incident ψ.data row[row.length - 1]
      (walkVertex ψ.data row st row.length) := by
    have := walkVertex_succ_incident (data := ψ.data) (start := st) hlast
    rwa [Nat.sub_add_cancel hpos] at this
  have h0 := nonDanglingValency_pos_of_incident (row_survives ψ P _ (List.getElem_mem hlast)) hinc
  have h1 := DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _
    ψ.fullDim.valid.1 (walkVertex ψ.data row st row.length)
  suffices h2 : nonDanglingValency ψ.data (walkVertex ψ.data row st row.length) ≠ 2 by omega
  obtain ⟨finish, hfin⟩ := DraismaVargas.LocalCases.TraversalPresentation.exists_isPathEnd_getLast
    (DraismaVargas.LocalCases.TraversalPresentation.traverseInvariant_empty
      (startEdge ψ.fullDim.pathEnds P).2 (startEdge_isPathEnd ψ.fullDim.pathEnds P))
  have hfin2 : ∀ last ∈ row.getLast?, IsPathEnd ψ.data last finish := hfin
  have hfin' : ∀ h : 0 < row.length, IsPathEnd ψ.data row[row.length - 1] finish := by
    intro h
    have := hfin2 _ (List.getLast_mem_getLast? (row_ne_nil ψ P))
    rwa [List.getLast_eq_getElem] at this
  by_cases hor : 2 ≤ row.length ∨ finish ≠ st
  · rw [walkVertex_length (row_nodup ψ P) (row_survives ψ P) (orderedRow_chain _ P)
      (row_start ψ P) hfin' (row_ne_nil ψ P) hor]
    exact (hfin' hpos).2
  · -- a single edge with both ends at one path end: its far end is a path end too
    push Not at hor
    have hlen : row.length = 1 := by omega
    intro h2
    have hx := row_survives ψ P _ (List.getElem_mem hlast)
    obtain ⟨o, ⟨hone, hond, hoinc⟩, -⟩ :=
      exists_unique_other_of_nonDanglingValency_eq_two ψ.data h2 hx hinc
    have hcons : Consecutive ψ.data ⟨o, hond⟩ ⟨_, hx⟩ :=
      ⟨fun h ↦ hone (congrArg Subtype.val h), _, hoinc, hinc, h2⟩
    have hmem : o ∈ row := by
      rw [hrow, mem_orderedRow_iff]
      refine ⟨hond, ?_⟩
      rw [stablePath_eq_of_consecutive hcons]
      exact ((mem_orderedRow_iff _ P _).mp (List.getElem_mem hlast)).2
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hmem
    apply hone
    congr 1
    omega

/-- The incidences of a walk at a branch vertex are those of the core. -/
theorem sum_incident_walkOE (b : Fin n) :
    ((walkOE ψ P).map fun c ↦ if Incident ψ.data c.1 (V₀ ψ b) then (1 : ℕ) else 0).sum =
      coreIncidence core b (ψ.ident.row P) := by
  classical
  have hnd : ((walkOE ψ P).map Prod.fst).Nodup := by rw [map_fst_walkOE]; exact row_nodup ψ P
  rw [show ((walkOE ψ P).map fun c ↦ if Incident ψ.data c.1 (V₀ ψ b) then (1 : ℕ) else 0).sum =
    ∑ z : NonDanglingEdge ψ.data, if z.1 ∈ (walkOE ψ P).map Prod.fst then
      (if Incident ψ.data z.1 (V₀ ψ b) then 1 else 0) else 0 from
    (sum_mem_list _ (good_walkOE ψ P) hnd
      (fun e ↦ if Incident ψ.data e (V₀ ψ b) then (1 : ℕ) else 0)).symm]
  have h := ψ.ident.incidence (ψ.ident.vertex.symm b) (ψ.ident.row P)
  rw [Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
  change incidenceCount ψ.data (V₀ ψ b) P = _ at h
  rw [← h]
  have hset : StablePathCount.incidentEdges ψ.data (V₀ ψ b) =
      Finset.univ.filter fun z : NonDanglingEdge ψ.data ↦ Incident ψ.data z.1 (V₀ ψ b) := by
    ext z
    simp only [StablePathCount.mem_incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold incidenceCount
  rw [hset, Finset.filter_filter, Finset.card_filter]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hiff : z.1 ∈ (walkOE ψ P).map Prod.fst ↔ z.stablePath = P := by
    rw [map_fst_walkOE, mem_orderedRow_iff]
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨z.2, h⟩⟩
  by_cases h1 : z.stablePath = P
  · rw [if_pos (hiff.mpr h1)]
    by_cases h2 : Incident ψ.data z.1 (V₀ ψ b)
    · rw [if_pos h2, if_pos ⟨h2, h1⟩]
    · rw [if_neg h2, if_neg (fun h ↦ h2 h.1)]
  · rw [if_neg (fun h ↦ h1 (hiff.mp h)), if_neg (fun h ↦ h1 h.2)]

/-- **The orientation of a walk**: it runs from the tail vertex of its slot to the head vertex,
or the other way round. -/
theorem orient (i : Fin p) :
    (startVertex ψ.fullDim.pathEnds (ψ.ident.row.symm i) = V₀ ψ (core.tail i) ∧
      walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds (ψ.ident.row.symm i))
        (startVertex ψ.fullDim.pathEnds (ψ.ident.row.symm i))
        (orderedRow ψ.fullDim.pathEnds (ψ.ident.row.symm i)).length = V₀ ψ (core.head i)) ∨
    (startVertex ψ.fullDim.pathEnds (ψ.ident.row.symm i) = V₀ ψ (core.head i) ∧
      walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds (ψ.ident.row.symm i))
        (startVertex ψ.fullDim.pathEnds (ψ.ident.row.symm i))
        (orderedRow ψ.fullDim.pathEnds (ψ.ident.row.symm i)).length = V₀ ψ (core.tail i)) := by
  set P := ψ.ident.row.symm i with hP
  set st := startVertex ψ.fullDim.pathEnds P with hst
  set fin := walkVertex ψ.data (orderedRow ψ.fullDim.pathEnds P) st
    (orderedRow ψ.fullDim.pathEnds P).length with hfin
  obtain ⟨a, ha⟩ : ∃ a, st = V₀ ψ a :=
    ⟨_, (V₀_vertex ψ ⟨st, three_le_start ψ P⟩).symm⟩
  obtain ⟨a', ha'⟩ : ∃ a', fin = V₀ ψ a' :=
    ⟨_, (V₀_vertex ψ ⟨fin, three_le_finish ψ P⟩).symm⟩
  have key : ∀ b, (if a = b then 1 else 0) + (if a' = b then 1 else 0) =
      (if core.tail i = b then 1 else 0) + (if core.head i = b then (1 : ℕ) else 0) := by
    intro b
    have h1 := sum_incident_chain _ (isChain_walkOE ψ P) (good_walkOE ψ P) (walkOE_ne_nil ψ P)
      ⟨b, rfl⟩ ((head_walkOE ψ P).trans ha) ((last_walkOE ψ P).trans ha')
    rw [sum_incident_walkOE, show ψ.ident.row P = i by rw [hP, Equiv.apply_symm_apply]] at h1
    simp only [(V₀_injective ψ).eq_iff] at h1
    unfold coreIncidence at h1
    exact h1.symm
  have hor : (a = core.tail i ∧ a' = core.head i) ∨ (a = core.head i ∧ a' = core.tail i) := by
    by_cases h1 : a = core.tail i
    · left
      refine ⟨h1, ?_⟩
      have k := key (core.head i)
      rw [if_pos (rfl : core.head i = core.head i)] at k
      subst h1
      by_contra hne
      rw [if_neg hne] at k
      omega
    · right
      have k := key a
      rw [if_pos (rfl : a = a), if_neg (Ne.symm h1)] at k
      have hha : core.head i = a := by
        by_contra hc
        rw [if_neg hc] at k
        omega
      refine ⟨hha.symm, ?_⟩
      have k' := key (core.tail i)
      rw [if_neg h1, if_pos (rfl : core.tail i = core.tail i), hha, if_neg h1] at k'
      by_contra hne
      rw [if_neg hne] at k'
      omega
  rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    exact ⟨ha.trans (congrArg _ h1), ha'.trans (congrArg _ h2)⟩
  · right
    exact ⟨ha.trans (congrArg _ h1), ha'.trans (congrArg _ h2)⟩

theorem sum_srcLen_walkOE (w : ψ.target.edges → ℚ) :
    ((walkOE ψ P).map fun c ↦ srcLen ψ.data w c.1).sum =
      ∑ x : NonDanglingEdge ψ.data, if x.stablePath = P then srcLen ψ.data w x.1 else 0 := by
  classical
  have hnd : ((walkOE ψ P).map Prod.fst).Nodup := by rw [map_fst_walkOE]; exact row_nodup ψ P
  rw [← sum_mem_list _ (good_walkOE ψ P) hnd]
  refine Finset.sum_congr rfl fun z _ ↦ ?_
  have hiff : z.1 ∈ (walkOE ψ P).map Prod.fst ↔ z.stablePath = P := by
    rw [map_fst_walkOE, mem_orderedRow_iff]
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨z.2, h⟩⟩
  by_cases h1 : z.stablePath = P
  · rw [if_pos (hiff.mpr h1), if_pos h1]
  · rw [if_neg (fun h ↦ h1 (hiff.mp h)), if_neg h1]

/-- **Stage zero**: the stable paths of `ψ` as a layout of `G̃`, under any non-negative target
lengths along which every stable path has its requested length. -/
theorem exists_layout₀ (w : ψ.target.edges → ℚ) (hw : ∀ e, 0 ≤ w e)
    (hlen : ∀ i, (∑ x : NonDanglingEdge ψ.data,
      if ψ.ident.row x.stablePath = i then srcLen ψ.data w x.1 else 0) = yG i) :
    ∃ L : Layout ψ.data core (V₀ ψ) yG,
      L.lab = (fun x ↦ ψ.ident.row x.stablePath) ∧ L.w = w := by
  classical
  set Pi : Fin p → StablePath ψ.data := fun i ↦ ψ.ident.row.symm i with hPi
  set ok : Fin p → Prop := fun i ↦ startVertex ψ.fullDim.pathEnds (Pi i) = V₀ ψ (core.tail i)
    with hok
  set ch : Fin p → List (OEdge ψ.data) := fun i ↦
    if ok i then walkOE ψ (Pi i) else revChain (walkOE ψ (Pi i)) with hch
  have hmemrow : ∀ (x : NonDanglingEdge ψ.data) i,
      x.1 ∈ orderedRow ψ.fullDim.pathEnds (Pi i) ↔ ψ.ident.row x.stablePath = i := by
    intro x i
    rw [mem_orderedRow_iff]
    constructor
    · rintro ⟨_, h⟩
      show ψ.ident.row x.stablePath = i
      rw [show x.stablePath = Pi i from h, hPi, Equiv.apply_symm_apply]
    · intro h
      refine ⟨x.2, ?_⟩
      show x.stablePath = ψ.ident.row.symm i
      rw [← h, Equiv.symm_apply_apply]
  have hne : ∀ i, ch i ≠ [] := by
    intro i
    simp only [hch]
    split_ifs
    · exact walkOE_ne_nil ψ _
    · exact revChain_ne_nil (walkOE_ne_nil ψ _)
  refine ⟨{
    lab := fun x ↦ ψ.ident.row x.stablePath
    w := w
    w_nonneg := hw
    chain := ch
    good := ?_
    mem := ?_
    nodup := ?_
    link := ?_
    ne_nil := hne
    head := ?_
    last := ?_
    sum := ?_ }, rfl, rfl⟩
  · intro i c hc
    simp only [hch] at hc
    split_ifs at hc
    · exact good_walkOE ψ _ c hc
    · exact good_revChain (good_walkOE ψ _) c hc
  · intro x i
    simp only [hch]
    split_ifs
    · rw [map_fst_walkOE]; exact hmemrow x i
    · rw [map_fst_revChain, map_fst_walkOE, List.mem_reverse]; exact hmemrow x i
  · intro i
    simp only [hch]
    split_ifs
    · rw [map_fst_walkOE]; exact row_nodup ψ _
    · rw [map_fst_revChain, map_fst_walkOE, List.nodup_reverse]; exact row_nodup ψ _
  · intro i
    simp only [hch]
    split_ifs
    · exact isChain_walkOE ψ _
    · exact isChain_revChain (isChain_walkOE ψ _)
  · intro i
    by_cases h : ok i
    · rw [head_congr' (show ch i = walkOE ψ (Pi i) by simp only [hch, if_pos h]) (hne i)
        (walkOE_ne_nil ψ _), head_walkOE]
      exact h
    · rw [head_congr' (show ch i = revChain (walkOE ψ (Pi i)) by simp only [hch, if_neg h])
        (hne i)
        (revChain_ne_nil (walkOE_ne_nil ψ _)), head_revChain (walkOE_ne_nil ψ _), last_walkOE]
      rcases orient ψ i with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 h
      · exact h2
  · intro i
    by_cases h : ok i
    · rw [getLast_congr' (show ch i = walkOE ψ (Pi i) by simp only [hch, if_pos h]) (hne i)
        (walkOE_ne_nil ψ _), last_walkOE]
      rcases orient ψ i with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · -- a loop slot: both ends are one vertex
        have hth : core.head i = core.tail i := V₀_injective ψ (h1.symm.trans h)
        rw [h2, hth]
    · rw [getLast_congr' (show ch i = revChain (walkOE ψ (Pi i)) by simp only [hch, if_neg h])
        (hne i)
        (revChain_ne_nil (walkOE_ne_nil ψ _)), last_revChain (walkOE_ne_nil ψ _), head_walkOE]
      rcases orient ψ i with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 h
      · exact h1
  · intro i
    have hs := sum_srcLen_walkOE ψ (Pi i) w
    have hs' : (∑ x : NonDanglingEdge ψ.data,
        if x.stablePath = Pi i then srcLen ψ.data w x.1 else 0) = yG i := by
      rw [← hlen i]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      have hiff : x.stablePath = Pi i ↔ ψ.ident.row x.stablePath = i := by
        rw [hPi, Equiv.eq_symm_apply]
      by_cases h1 : x.stablePath = Pi i
      · rw [if_pos h1, if_pos (hiff.mp h1)]
      · rw [if_neg h1, if_neg (fun h ↦ h1 (hiff.mpr h))]
    simp only [hch]
    split_ifs
    · rw [hs, hs']
    · rw [sum_revChain, hs, hs']

end Stage0

/-! ## 2. Label data at the third stage and the glued datum -/

section Glued

variable {T : CFGraph} {d : ℕ} {D : GluingDatum T d} {π : Placement T d} (hD : D.Connected)
  (hT : graph_connected T) (hπ : π.NonDangling D)

include hD hT hπ in
/-- **The incidences of a glued old path at an old vertex** are counted in `refine₃ D π`, when
no arm at the vertex lies on the path. -/
theorem incidenceCount_oldVertex₃ (x : (refine₃ D π).SourceVertex)
    (Q : StablePath (glueDatum D π))
    (hQ : ∀ k, x = markR₃ D π k → ∀ a : NonDanglingEdge (glueDatum D π),
      a.1 = π.armSourceEdge D k → a.stablePath ≠ Q) :
    incidenceCount (glueDatum D π) (oldVertex₃ D π x) Q =
      (Finset.univ.filter fun z : NonDanglingEdge (refine₃ D π) ↦
        Incident _ z.1 x ∧ CutPaths.gluedPath D π hD hT hπ z = Q).card := by
  classical
  unfold incidenceCount
  symm
  refine Finset.card_bij (fun z _ ↦ CutPaths.liftND D π hD hT hπ z) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges]
    exact ⟨(incident_liftSE_oldVertex₃ D π _ x).mpr hz.1, hz.2⟩
  · intro z₁ _ z₂ _ h
    exact CutPaths.liftND_injective D π hD hT hπ h
  · intro a ha
    rw [Finset.mem_filter, StablePathCount.mem_incidentEdges] at ha
    rcases Onto.isOld_or_arm_of_incident_oldVertex₃ hD hT a ha.1 with hold | ⟨k, hk, harm⟩
    · obtain ⟨z, rfl⟩ := CutPaths.eq_liftND_of_isOld hD hT hπ hold
      refine ⟨z, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(incident_liftSE_oldVertex₃ D π _ x).mp ha.1, ha.2⟩
    · exact absurd ha.2 (hQ k hk a harm)

include hD hT hπ in
/-- The arm at a mark is not on a glued old path. -/
theorem arm_stablePath_ne (k : Fin 3) (a : NonDanglingEdge (glueDatum D π))
    (ha : a.1 = π.armSourceEdge D k) (z : NonDanglingEdge (refine₃ D π)) :
    a.stablePath ≠ CutPaths.gluedPath D π hD hT hπ z := by
  have : a = ⟨_, (hairpin_not_isDangling D π hD hT k).1⟩ := Subtype.ext ha
  rw [this]
  exact (CutPaths.gluedPath_ne_hairpin hD hT hπ z k).symm

variable {m q : ℕ} {C : Core m q} {V : Fin m → (refine₃ D π).SourceVertex} {yM : Fin q → ℚ}

include hD hT hπ in
/-- **Label data are constant along a glued old path**, when every interior vertex outside the
marks is outside the named vertices. -/
theorem LabelData.lab_eq_of_gluedPath_eq (R : LabelData (refine₃ D π) C V yM)
    (hinner : ∀ x, nonDanglingValency (refine₃ D π) x = 2 → (∀ k, x ≠ markR₃ D π k) →
      x ∉ Set.range V)
    {z z' : NonDanglingEdge (refine₃ D π)}
    (h : CutPaths.gluedPath D π hD hT hπ z = CutPaths.gluedPath D π hD hT hπ z') :
    R.lab z = R.lab z' := by
  let P : NonDanglingEdge (glueDatum D π) → Prop := fun a ↦
    ∀ z₁, a = CutPaths.liftND D π hD hT hπ z₁ → R.lab z₁ = R.lab z
  have hclosed : ∀ a b : NonDanglingEdge (glueDatum D π), Consecutive _ a b → P a → P b := by
    intro a b hab hPa z₂ hb
    obtain ⟨hne, v, hav, hbv, hval⟩ := hab
    have hcons : Consecutive _ b a := ⟨fun h ↦ hne h.symm, v, hbv, hav, hval⟩
    have hbold : CutPaths.IsOld D π b := hb ▸ CutPaths.isOld_liftND hD hT hπ z₂
    obtain ⟨z₁, hz₁⟩ := CutPaths.eq_liftND_of_isOld hD hT hπ
      (CutPaths.isOld_of_consecutive hD hT hπ hcons hbold)
    have hlab₁ : R.lab z₁ = R.lab z := hPa z₁ hz₁
    rw [hz₁] at hav
    rw [hb] at hbv
    rcases sourceVertex_cases_glue D π v with ⟨x, rfl⟩ | ⟨u, rfl⟩ | ⟨k, j, rfl⟩
    · have h₁ := (incident_liftSE_oldVertex₃ D π _ x).mp hav
      have h₂ := (incident_liftSE_oldVertex₃ D π _ x).mp hbv
      have hm : ∀ k, x ≠ markR₃ D π k := by
        intro k hk
        rw [nonDanglingValency_oldVertex₃ D π hD hT hπ, hk, sum_mark_eq_one, markR₃,
          π.nonDanglingValency_markR₃ D hD hπ k] at hval
        omega
      rw [nonDanglingValency_oldVertex₃ D π hD hT hπ, sum_mark_eq_zero D π hm, add_zero] at hval
      exact (R.const z₁ z₂ x h₁ h₂ ⟨hval, hinner x hval hm⟩).symm.trans hlab₁
    · exact absurd hav (not_incident_liftSE_newVertex D π z₁.1 u)
    · exact absurd hav (not_incident_liftSE_tip D π z₁.1 k j)
  have hiff := eqvGen_iff_of_closed hclosed ((stablePath_eq_iff _ _).mp h)
  exact ((hiff.mp fun z₁ h₁ ↦ by rw [CutPaths.liftND_injective D π hD hT hπ h₁]) z' rfl).symm

end Glued

section Bridge

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {yG : Fin p → ℚ}
  {ψ : FibreMember core yG (2 + 2)} {π : Placement ψ.target (2 + 2)} (hπ : π.NonDangling ψ.data)
  {V₃ : Fin (n + 1 + 1 + 1) → (refine₃ ψ.data π).SourceVertex}
  (hVold : ∀ v, V₃ (PieceIdent.mOld v) = oldSV₃ ψ.data π (V₀ ψ v))
  (hVmark : ∀ k, V₃ (markVertex n k) = markR₃ ψ.data π k)

theorem fin_cases_marked (a : Fin (n + 1 + 1 + 1)) :
    (∃ v, a = PieceIdent.mOld v) ∨ ∃ k, a = markVertex n k := by
  by_cases h : a.val < n
  · exact Or.inl ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  · exact Or.inr ⟨⟨a.val - n, by omega⟩, Fin.ext (by simp only [markVertex]; omega)⟩

include hVold hVmark in
theorem inner_of_marks (x : (refine₃ ψ.data π).SourceVertex)
    (hx : nonDanglingValency (refine₃ ψ.data π) x = 2) (hm : ∀ k, x ≠ markR₃ ψ.data π k) :
    x ∉ Set.range V₃ := by
  rintro ⟨a, rfl⟩
  rcases fin_cases_marked a with ⟨v, rfl⟩ | ⟨k, rfl⟩
  · rw [hVold] at hx
    have h3 := (ψ.ident.vertex.symm v).2
    have := CutPaths.nonDanglingValency_lift₃V (π := π) ψ.fullDim.valid.1 (V₀ ψ v)
    change nonDanglingValency (refine₃ ψ.data π) (CutPaths.lift₃V ψ.data π (V₀ ψ v)) = 2 at hx
    rw [this] at hx
    unfold V₀ at hx
    omega
  · exact hm k (hVmark k)

variable {yM : Fin (p + 1 + 1 + 1) → ℚ}
  (R : LabelData (refine₃ ψ.data π) (markedCore core s) V₃ yM)

include hVold hVmark in
/-- **The bridge**: label data at the third stage, merging back to the rows of `ψ`, are piece
labels of the glued old paths, along whose lengths each has the requested length of its label. -/
theorem pieceLabels_of_labelData
    (hmerge : ∀ z, mergeOne s.first (mergeOne s.second (mergeOne s.third (R.lab z))) =
      ψ.ident.row (parentND₃ z).stablePath)
    (hsurj : ∀ i, ∃ z, R.lab z = i) :
    ∃ lab : StablePath (glueDatum ψ.data π) → Fin (p + 1 + 1 + 1),
      PieceIdent.PieceLabels s ψ hπ lab ∧
      ∀ z₀ : NonDanglingEdge (refine₃ ψ.data π),
        (∑ z : NonDanglingEdge (refine₃ ψ.data π),
          if CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z =
            CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z₀
          then R.w z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 else 0) =
          yM (lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1
            ψ.fullDim.targetConnected hπ z₀)) := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  set gp := CutPaths.gluedPath ψ.data π hD hT hπ with hgp
  have hinner := inner_of_marks hVold hVmark
  have hconst : ∀ z z', gp z = gp z' → R.lab z = R.lab z' := fun z z' h ↦
    R.lab_eq_of_gluedPath_eq hD hT hπ hinner h
  set lab : StablePath (glueDatum ψ.data π) → Fin (p + 1 + 1 + 1) := fun Q ↦
    if h : ∃ z, gp z = Q then R.lab h.choose else 0 with hlab
  have hlab_gp : ∀ z, lab (gp z) = R.lab z := by
    intro z
    have h : ∃ z', gp z' = gp z := ⟨z, rfl⟩
    simp only [hlab, dif_pos h]
    exact hconst _ _ h.choose_spec
  -- the glued old paths are as many as the labels, so the labels tell them apart
  have hcard := CutPaths.card_image_gluedPath hD hT hπ ψ.fullDim.targetGenus ψ.fullDim.trivalent
    ψ.fullDim.pathEnds
  have hP : Fintype.card (StablePath ψ.data) = p := by
    rw [Fintype.card_congr ψ.ident.row, Fintype.card_fin]
  have himg : (Finset.univ.image gp).image lab = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    obtain ⟨z, hz⟩ := hsurj i
    exact Finset.mem_image.mpr ⟨gp z, Finset.mem_image_of_mem _ (Finset.mem_univ _),
      by rw [hlab_gp, hz]⟩
  have hinj : Set.InjOn lab (Finset.univ.image gp : Set _) := by
    apply Finset.card_image_iff.mp
    rw [himg, Finset.card_univ, Fintype.card_fin, hgp, hcard, hP]
  have hiff : ∀ z z', gp z = gp z' ↔ R.lab z = R.lab z' := by
    intro z z'
    refine ⟨hconst z z', fun h ↦ hinj ?_ ?_ (by rw [hlab_gp, hlab_gp, h])⟩
    · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  -- the incidences at the old vertices and at the marks
  have hcount : ∀ (a : Fin (n + 1 + 1 + 1)) (z : NonDanglingEdge (refine₃ ψ.data π)),
      (∀ k, V₃ a = markR₃ ψ.data π k → ∀ b : NonDanglingEdge (glueDatum ψ.data π),
        b.1 = π.armSourceEdge ψ.data k → b.stablePath ≠ gp z) →
      incidenceCount (glueDatum ψ.data π) (oldVertex₃ ψ.data π (V₃ a)) (gp z) =
        coreIncidence (markedCore core s) a (lab (gp z)) := by
    intro a z hQ
    rw [incidenceCount_oldVertex₃ hD hT hπ _ _ hQ, hlab_gp, ← R.inc a (R.lab z)]
    congr 1
    ext z'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_congr_right fun _ ↦ hiff z' z
  refine ⟨lab, ⟨fun z z' h ↦ (hiff z z').mpr (by rwa [hlab_gp, hlab_gp] at h),
    fun z ↦ by rw [hlab_gp]; exact hmerge z, fun z b ↦ ?_, fun z k ↦ ?_⟩, fun z₀ ↦ ?_⟩
  · have hb : V₃ (PieceIdent.mOld (ψ.ident.vertex b)) = oldSV₃ ψ.data π b.1 := by
      rw [hVold, V₀_vertex]
    rw [oldSourceVertex_eq, ← hb]
    refine hcount _ z fun k hk ↦ absurd (hb.symm.trans hk) ?_
    exact CutPaths.lift₃V_ne_markR₃ hD hπ _ k
  · rw [markSourceVertex_eq, ← hVmark k]
    exact hcount _ z fun k' _ b hb ↦ arm_stablePath_ne hD hT hπ k' b hb z
  · rw [hlab_gp, ← R.len (R.lab z₀)]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    by_cases h : R.lab z = R.lab z₀
    · rw [if_pos ((hiff z z₀).mpr h), if_pos h]
      rfl
    · rw [if_neg (fun h' ↦ h ((hiff z z₀).mp h')), if_neg h]

end Bridge

/-! ## 3. The actual positions: proof of `GluingPositivity.exists_pieceLabels` -/

section Positions

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p}

theorem freshOf_congr {T : CFGraph} {d : ℕ} (D : GluingDatum T d) (t : T.edges)
    {x x' : D.SourceEdge} (h : x = x') (hx : x.1.1 = t) (hx' : x'.1.1 = t) :
    Refine.freshOf D t x hx = Refine.freshOf D t x' hx' := by
  subst h; rfl

theorem sourceEdge_val_eq {T : CFGraph} {d : ℕ} (D : GluingDatum T d) (x : D.SourceEdge) :
    D.sourceEdge x.1.1 x.1.2 = x :=
  Subtype.ext (Prod.ext rfl x.2)

/-- The realisation equation of a member, along its rows. -/
theorem len_of_member {yG : Fin p → ℚ} {d : ℕ} (ψ : FibreMember core yG d) (i : Fin p) :
    (∑ x : NonDanglingEdge ψ.data, if ψ.ident.row x.stablePath = i then
      srcLen ψ.data (fun e ↦ ψ.coords (ψ.fullDim.labelling.targetEdge.symm e)) x.1 else 0) =
      yG i := by
  have h := congrFun ψ.realizes (ψ.fullDim.labelling.row (ψ.ident.row.symm i))
  rw [Onto.mulVec_eq_sum, Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  have hiff : ψ.fullDim.labelling.row x.stablePath =
      ψ.fullDim.labelling.row (ψ.ident.row.symm i) ↔ ψ.ident.row x.stablePath = i := by
    rw [ψ.fullDim.labelling.row.injective.eq_iff, Equiv.eq_symm_apply]
  by_cases hx : ψ.ident.row x.stablePath = i
  · rw [if_pos hx, if_pos (hiff.mpr hx)]
    rfl
  · rw [if_neg hx, if_neg (fun h ↦ hx (hiff.mp h))]

/-- The placement of the three marks on three successive surviving edges. -/
abbrev mkPlacement {T : CFGraph} {d : ℕ} {D : GluingDatum T d} (x₀ : NonDanglingEdge D)
    (x₁ : NonDanglingEdge (refineDatum D x₀.1.1.1))
    (x₂ : NonDanglingEdge (refineDatum (refineDatum D x₀.1.1.1) x₁.1.1.1)) : Placement T d :=
  ⟨x₀.1.1.1, x₁.1.1.1, x₂.1.1.1, ![x₀.1.1.2, x₁.1.1.2, x₂.1.1.2]⟩

section MkPlacement

variable {T : CFGraph} {d : ℕ} {D : GluingDatum T d} (hD : D.Connected) (x₀ : NonDanglingEdge D)
  (x₁ : NonDanglingEdge (refineDatum D x₀.1.1.1))
  (x₂ : NonDanglingEdge (refineDatum (refineDatum D x₀.1.1.1) x₁.1.1.1))

include hD in
theorem mkPlacement_nonDangling : (mkPlacement x₀ x₁ x₂).NonDangling D := by
  intro k
  fin_cases k
  · show ¬ IsDangling D (D.sourceEdge x₀.1.1.1 x₀.1.1.2)
    rw [sourceEdge_val_eq]; exact x₀.2
  · show ¬ IsDangling D (D.sourceEdge (parentT x₀.1.1.1 x₁.1.1.1) x₁.1.1.2)
    rw [← Refine.isDangling_sourceEdge _ _ hD, sourceEdge_val_eq]; exact x₁.2
  · show ¬ IsDangling D (D.sourceEdge (parentT x₀.1.1.1 (parentT x₁.1.1.1 x₂.1.1.1)) x₂.1.1.2)
    rw [← Refine.isDangling_sourceEdge _ _ hD,
      ← Refine.isDangling_sourceEdge _ _ (refineDatum_connected _ _ hD), sourceEdge_val_eq]
    exact x₂.2

theorem markR₃_mk₀ (hπ : (mkPlacement x₀ x₁ x₂).NonDangling D) :
    markR₃ D (mkPlacement x₀ x₁ x₂) 0 =
      Refine.oldSV _ x₂.1.1.1 (Refine.oldSV _ x₁.1.1.1 (Refine.freshOf D x₀.1.1.1 x₀.1 rfl)) := by
  rw [Placement.markR₃_zero_eq D _ hπ]
  exact congrArg _ (congrArg _ (freshOf_congr _ _ (sourceEdge_val_eq _ _) _ _))

include hD in
theorem markR₃_mk₁ (hπ : (mkPlacement x₀ x₁ x₂).NonDangling D) :
    markR₃ D (mkPlacement x₀ x₁ x₂) 1 =
      Refine.oldSV _ x₂.1.1.1 (Refine.freshOf _ x₁.1.1.1 x₁.1 rfl) := by
  rw [Placement.markR₃_one_eq D _ hD hπ]
  exact congrArg _ (freshOf_congr _ _ (sourceEdge_val_eq _ _) _ _)

include hD in
theorem markR₃_mk₂ (hπ : (mkPlacement x₀ x₁ x₂).NonDangling D) :
    markR₃ D (mkPlacement x₀ x₁ x₂) 2 = Refine.freshOf _ x₂.1.1.1 x₂.1 rfl := by
  rw [Placement.markR₃_two_eq D _ hD hπ]
  exact freshOf_congr _ _ (sourceEdge_val_eq _ _) _ _

include hD in
theorem newV₃_markVertex {m : ℕ} (V : Fin m → D.SourceVertex)
    (hπ : (mkPlacement x₀ x₁ x₂).NonDangling D) (k : Fin 3) :
    newV (newV (newV V x₀) x₁) x₂ (markVertex m k) = markR₃ D (mkPlacement x₀ x₁ x₂) k := by
  fin_cases k
  · refine (congrArg _ (Fin.ext (by simp [markVertex]) :
      markVertex m 0 = (Fin.last m).castSucc.castSucc)).trans ?_
    exact (newV₃_mark₀ V x₀ x₁ x₂).trans (markR₃_mk₀ x₀ x₁ x₂ hπ).symm
  · refine (congrArg _ (Fin.ext (by simp [markVertex]) :
      markVertex m 1 = (Fin.last (m + 1)).castSucc)).trans ?_
    exact (newV₃_mark₁ V x₀ x₁ x₂).trans (markR₃_mk₁ hD x₀ x₁ x₂ hπ).symm
  · refine (congrArg _ (Fin.ext (by simp [markVertex]) :
      markVertex m 2 = Fin.last (m + 1 + 1))).trans ?_
    exact (newV₃_mark₂ V x₀ x₁ x₂).trans (markR₃_mk₂ hD x₀ x₁ x₂ hπ).symm

theorem newV₃_mOld {m : ℕ} (V : Fin m → D.SourceVertex) (v : Fin m) :
    newV (newV (newV V x₀) x₁) x₂ (PieceIdent.mOld v) =
      oldSV₃ D (mkPlacement x₀ x₁ x₂) (V v) :=
  newV₃_old V x₀ x₁ x₂ v

end MkPlacement

/-- **The pieces at the actual positions**, the statement of
`GluingPositivity.exists_pieceLabels`. -/
theorem exists_pieceLabels_of_open {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} (hpos : ∀ i, 0 < y i)
    (ψ : FibreMember core (baseRequest s y) (2 + 2)) (hψ : ψ.Open) :
    ∃ π : Placement ψ.target (2 + 2), ∃ hπ : π.NonDangling ψ.data,
      ∃ lab : StablePath (glueDatum ψ.data π) → Fin (p + 1 + 1 + 1),
        PieceIdent.PieceLabels s ψ hπ lab ∧
        ∃ w₃ : π.T₃.edges → ℚ, (∀ e, 0 ≤ w₃ e) ∧
          ∀ z₀ : NonDanglingEdge (refine₃ ψ.data π),
            (∑ z : NonDanglingEdge (refine₃ ψ.data π),
              if CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z =
                CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z₀
              then w₃ z.1.1.1 / (refine₃ ψ.data π).sourceEdgeIndex z.1 else 0) =
              y (Fin.castAdd 3 (lab (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1
                ψ.fullDim.targetConnected hπ z₀))) := by
  classical
  have hD := ψ.fullDim.valid.1
  -- stage zero, at the coordinates of `ψ`
  obtain ⟨L₀, hL₀lab, -⟩ := exists_layout₀ ψ _ (fun e ↦ (hψ _).le) (len_of_member ψ)
  -- the requests of the three stages
  have hg : ∀ i, 0 < gPart y i := fun i ↦ hpos _
  have hy₂ := mergeRequest_pos s.third hg
  have hy₁ := mergeRequest_pos s.second hy₂
  -- the three marks, each at its actual position
  obtain ⟨x₀, -, L₁, hm₁, -, -⟩ := forward hD L₀ s.first (y' := mergeRequest s.second
    (mergeRequest s.third (gPart y))) rfl (hy₁ _) (hy₁ _).le
  have hD₁ := refineDatum_connected _ x₀.1.1.1 hD
  obtain ⟨x₁, -, L₂, hm₂, -, -⟩ := forward hD₁ L₁ s.second
    (y' := mergeRequest s.third (gPart y)) rfl (hy₂ _) (hy₂ _).le
  have hD₂ := refineDatum_connected _ x₁.1.1.1 hD₁
  obtain ⟨x₂, -, L₃, hm₃, -, -⟩ := forward hD₂ L₂ s.third (y' := gPart y) rfl (hg _) (hg _).le
  have hπ := mkPlacement_nonDangling hD x₀ x₁ x₂
  have hmerge : ∀ z, mergeOne s.first (mergeOne s.second (mergeOne s.third (L₃.lab z))) =
      ψ.ident.row (parentND₃ (π := mkPlacement x₀ x₁ x₂) z).stablePath := by
    intro z
    rw [hm₃, hm₂, hm₁, hL₀lab]
    rfl
  obtain ⟨lab, hl, hlen⟩ := pieceLabels_of_labelData (π := mkPlacement x₀ x₁ x₂) hπ
    (newV₃_mOld x₀ x₁ x₂ (V₀ ψ)) (newV₃_markVertex hD x₀ x₁ x₂ (V₀ ψ) hπ)
    (L₃.toLabelData (newV_injective (newV_injective (newV_injective (V₀_injective ψ) x₀) x₁) x₂))
    hmerge L₃.exists_lab
  exact ⟨mkPlacement x₀ x₁ x₂, hπ, lab, hl, L₃.w, L₃.w_nonneg, hlen⟩

end Positions

/-! ## 4. An open gluing gives label data at the third stage -/

section Transport

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
  {ψ : FibreMember core (baseRequest s y) (2 + 2)} {π : Placement ψ.target (2 + 2)}
  (hπ : π.NonDangling ψ.data) {φ : FibreMember (tripodCore core s) y (3 + 2)}
  (iso : GeometricDatumIso (glueDatum ψ.data π) φ.data) (hL : GluedLabels s ψ π φ.ident iso)
  {V₃ : Fin (n + 1 + 1 + 1) → (refine₃ ψ.data π).SourceVertex}
  (hVold : ∀ v, V₃ (PieceIdent.mOld v) = oldSV₃ ψ.data π (V₀ ψ v))
  (hVmark : ∀ k, V₃ (markVertex n k) = markR₃ ψ.data π k)

include hL in
omit hπ in
/-- The glued old path of a surviving edge lies on a G-slot of `φ`. -/
theorem isGSlot_row_gluedPath (hπ : π.NonDangling ψ.data) (z : NonDanglingEdge (refine₃ ψ.data π)) :
    IsGSlot (φ.ident.row (iso.stablePathEquiv
      (glueDatum_connected ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected)
      (CutPaths.gluedPath ψ.data π ψ.fullDim.valid.1 ψ.fullDim.targetConnected hπ z))) := by
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hS : Onto.ShapeLabels s ψ.data π φ.ident iso := ⟨hL.mark, hL.centre, hL.leg⟩
  rcases Dichotomy.isGSlot_or_eq_legSlot (φ.ident.row (iso.stablePathEquiv
    (glueDatum_connected ψ.data π hD hT) (CutPaths.gluedPath ψ.data π hD hT hπ z))) with h | ⟨k, hk⟩
  · exact h
  · exfalso
    have hrow := Onto.row_legND hD hT iso hS k
    rw [← GeometricDatumIso.stablePathEquiv_mk, ← hk] at hrow
    have := (iso.stablePathEquiv _).injective (φ.ident.row.injective hrow)
    exact CutPaths.gluedPath_ne_hairpin hD hT hπ z k this.symm

include hπ hL hVold hVmark in
/-- **The label data of an open gluing** at the third stage: the G-slots of the glued old paths,
and the coordinates of `φ`, positive. -/
theorem labelData₃_of_gluing (hφ : φ.Open) :
    ∃ R : LabelData (refine₃ ψ.data π) (markedCore core s) V₃ (gPart y),
      (∀ ε, 0 < R.w ε) ∧
      ∀ z, mergeOne s.first (mergeOne s.second (mergeOne s.third (R.lab z))) =
        ψ.ident.row (parentND₃ z).stablePath := by
  classical
  have hD := ψ.fullDim.valid.1
  have hT := ψ.fullDim.targetConnected
  have hT0 := ψ.fullDim.targetGenus
  have hG := glueDatum_connected ψ.data π hD hT
  have hS : Onto.ShapeLabels s ψ.data π φ.ident iso := ⟨hL.mark, hL.centre, hL.leg⟩
  set gp := CutPaths.gluedPath ψ.data π hD hT hπ with hgp
  set row : NonDanglingEdge (refine₃ ψ.data π) → Fin (p + 1 + 1 + 1 + 3) := fun z ↦
    φ.ident.row (iso.stablePathEquiv hG (gp z)) with hrow
  set lab : NonDanglingEdge (refine₃ ψ.data π) → Fin (p + 1 + 1 + 1) := fun z ↦
    ⟨(row z).val, isGSlot_row_gluedPath iso hL hπ z⟩ with hlab
  have hrowlab : ∀ z, row z = Fin.castAdd 3 (lab z) := fun z ↦ Fin.ext rfl
  have hlabiff : ∀ z i, lab z = i ↔
      iso.stablePathEquiv hG (gp z) = φ.ident.row.symm (Fin.castAdd 3 i) := by
    intro z i
    rw [Equiv.eq_symm_apply]
    show lab z = i ↔ row z = Fin.castAdd 3 i
    rw [hrowlab]
    exact ⟨fun h ↦ by rw [h], fun h ↦ Fin.castAdd_injective _ _ h⟩
  have hinner := inner_of_marks hVold hVmark
  refine ⟨{
    lab := lab
    w := fun ε ↦ Onto.zG iso (π.liftE₃ ε)
    w_nonneg := fun ε ↦ (hφ _).le
    const := ?_
    inc := ?_
    len := ?_ }, fun ε ↦ hφ _, ?_⟩
  · -- constant along the glued old paths
    intro z z' x hz hz' hin
    by_cases hzz : z = z'
    · rw [hzz]
    have hm : ∀ k, x ≠ markR₃ ψ.data π k := fun k h ↦ hin.2 ⟨markVertex n k, (hVmark k).trans h.symm⟩
    have h := CutPaths.gluedPath_eq_of_incident hD hT hπ hzz hz hz' hin.1 hm
    exact Fin.ext (congrArg (fun Q ↦ (φ.ident.row (iso.stablePathEquiv hG Q)).val) h)
  · -- the incidences, read off `φ`
    intro a i
    have hvert : (φ.ident.vertex.symm a.castSucc).1 =
        iso.sourceVertexEquiv (oldVertex₃ ψ.data π (V₃ a)) := by
      rcases fin_cases_marked a with ⟨v, rfl⟩ | ⟨k, rfl⟩
      · have h := hL.old (ψ.ident.vertex.symm v)
        rw [Equiv.apply_symm_apply] at h
        rw [hVold]
        exact h
      · rw [hVmark, ← markSourceVertex_eq]
        exact hL.mark k
    have hinc := φ.ident.incidence (φ.ident.vertex.symm a.castSucc) (Fin.castAdd 3 i)
    rw [Equiv.apply_symm_apply, PieceIdent.coreIncidence_castSucc_castAdd, hvert] at hinc
    rw [← hinc]
    set Q := (iso.stablePathEquiv hG).symm (φ.ident.row.symm (Fin.castAdd 3 i)) with hQ
    have hQ' : φ.ident.row.symm (Fin.castAdd 3 i) = iso.stablePathEquiv hG Q := by
      rw [hQ, Equiv.apply_symm_apply]
    rw [hQ', ← iso.incidenceCount_map hG]
    rw [incidenceCount_oldVertex₃ hD hT hπ _ Q]
    · congr 1
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine and_congr_right fun _ ↦ ?_
      rw [hlabiff z i, hQ, Equiv.eq_symm_apply (iso.stablePathEquiv hG)]
    · intro k _ b hb hbQ
      have hbk : b = Onto.legND hD hT k := Subtype.ext hb
      have hrow' := Onto.row_legND hD hT iso hS k
      rw [← hbk, ← GeometricDatumIso.stablePathEquiv_mk, hbQ, hQ, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply] at hrow'
      have := congrArg Fin.val hrow'
      simp only [Fin.val_castAdd, legSlot, Fin.val_natAdd] at this
      omega
  · -- the lengths, read off `φ`
    intro i
    obtain ⟨z₀, hz₀⟩ := Onto.exists_gluedPath_eq_gSlot hD hT hπ hT0 iso hS i
    have hlen := Onto.length_gluedPath hD hT hπ iso z₀
    rw [hz₀, Equiv.apply_symm_apply] at hlen
    show _ = y (Fin.castAdd 3 i)
    rw [← hlen]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have hiff : lab z = i ↔ gp z = gp z₀ := by
      rw [hlabiff, ← hz₀, (iso.stablePathEquiv hG).injective.eq_iff]
    by_cases h : lab z = i
    · rw [if_pos h, if_pos (hiff.mp h)]
      rfl
    · rw [if_neg h, if_neg (fun h' ↦ h (hiff.mpr h'))]
  · -- the merged labels are the rows of `ψ`
    intro z
    have h := pieceLabel_eq hπ iso hL z
    unfold pieceLabel at h
    rw [← GeometricDatumIso.stablePathEquiv_mk] at h
    change mergeSlot s (row z) = _ at h
    rw [hrowlab, mergeSlot_castAdd] at h
    exact Option.some_injective _ h

end Transport

/-! ## 5. The placement is forced: proof of `GluingWellDefined.placement_forced` -/

section PlacementLemmas

variable {T : CFGraph} {d : ℕ} {D : GluingDatum T d} (hD : D.Connected) (π : Placement T d)
  (hπ : π.NonDangling D)

/-- Mark `0` of a placement, as a surviving source edge whose target edge is `π.edge₀` on the
nose. -/
abbrev mkEdge₀ : NonDanglingEdge D :=
  ⟨⟨(π.edge₀, (D.edgePartition π.edge₀).repr (π.sheet 0)), SheetPartition.repr_idem _ _⟩, hπ 0⟩

/-- Mark `1`. -/
abbrev mkEdge₁ : NonDanglingEdge (refineDatum D (mkEdge₀ π hπ).1.1.1) :=
  ⟨⟨(π.edge₁, ((refineDatum D π.edge₀).edgePartition π.edge₁).repr (π.sheet 1)),
    SheetPartition.repr_idem _ _⟩, (π.markEdge₁ D hD hπ).2⟩

/-- Mark `2`. -/
abbrev mkEdge₂ : NonDanglingEdge (refineDatum (refineDatum D (mkEdge₀ π hπ).1.1.1)
    (mkEdge₁ hD π hπ).1.1.1) :=
  ⟨⟨(π.edge₂, ((refineDatum (refineDatum D π.edge₀) π.edge₁).edgePartition π.edge₂).repr
    (π.sheet 2)), SheetPartition.repr_idem _ _⟩, (π.markEdge₂ D hD hπ).2⟩

theorem newV₃_mOld_mk {m : ℕ} (V : Fin m → D.SourceVertex) (v : Fin m) :
    newV (newV (newV V (mkEdge₀ π hπ)) (mkEdge₁ hD π hπ)) (mkEdge₂ hD π hπ)
      (PieceIdent.mOld v) = oldSV₃ D π (V v) :=
  newV₃_old V _ _ _ v

theorem newV₃_markVertex_mk {m : ℕ} (V : Fin m → D.SourceVertex) (k : Fin 3) :
    newV (newV (newV V (mkEdge₀ π hπ)) (mkEdge₁ hD π hπ)) (mkEdge₂ hD π hπ)
      (markVertex m k) = markR₃ D π k := by
  fin_cases k
  · refine (congrArg _ (Fin.ext (by simp [markVertex]) :
      markVertex m 0 = (Fin.last m).castSucc.castSucc)).trans ?_
    exact (newV₃_mark₀ V _ _ _).trans (Placement.markR₃_zero_eq D π hπ).symm
  · refine (congrArg _ (Fin.ext (by simp [markVertex]) :
      markVertex m 1 = (Fin.last (m + 1)).castSucc)).trans ?_
    exact (newV₃_mark₁ V _ _ _).trans (Placement.markR₃_one_eq D π hD hπ).symm
  · refine (congrArg _ (Fin.ext (by simp [markVertex]) :
      markVertex m 2 = Fin.last (m + 1 + 1))).trans ?_
    exact (newV₃_mark₂ V _ _ _).trans (Placement.markR₃_two_eq D π hD hπ).symm

end PlacementLemmas

section Forced

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p}

/-- **The requested lengths of an open member are positive.** -/
theorem request_pos_of_open {m q : ℕ} {C : Core m q} {y : Fin q → ℚ} {d : ℕ}
    (φ : FibreMember C y d) (hφ : φ.Open) (i : Fin q) : 0 < y i := by
  classical
  have h := congrFun φ.realizes (φ.fullDim.labelling.row (φ.ident.row.symm i))
  rw [Onto.mulVec_eq_sum, Equiv.symm_apply_apply, Equiv.apply_symm_apply] at h
  rw [← h]
  obtain ⟨x₀, hx₀⟩ := Quot.exists_rep (φ.ident.row.symm i)
  refine Finset.sum_pos' (fun x _ ↦ ?_) ⟨x₀, Finset.mem_univ _, ?_⟩
  · split_ifs
    · exact div_nonneg (hφ _).le (Nat.cast_nonneg _)
    · exact le_rfl
  · have hc : φ.fullDim.labelling.row x₀.stablePath =
        φ.fullDim.labelling.row (φ.ident.row.symm i) := congrArg φ.fullDim.labelling.row hx₀
    rw [if_pos hc]
    exact div_pos (hφ _) (sourceEdgeIndex_pos' _)

/-- **Lengths realising the request along the rows of a member are its coordinates.** -/
theorem w_eq_coords {yG : Fin p → ℚ} {d : ℕ} (ψ : FibreMember core yG d)
    (w : ψ.target.edges → ℚ)
    (hlen : ∀ i, (∑ x : NonDanglingEdge ψ.data,
      if ψ.ident.row x.stablePath = i then srcLen ψ.data w x.1 else 0) = yG i) :
    w = fun e ↦ ψ.coords (ψ.fullDim.labelling.targetEdge.symm e) := by
  classical
  set L := ψ.fullDim.labelling with hL
  have hc := ψ.coords_unique (fun col ↦ w (L.targetEdge col)) (by
    funext r
    show (GluingDatum.LengthMatrixPresentation.matrix L.presentation).mulVec _ r = _
    rw [Onto.mulVec_eq_sum, ← hlen (ψ.ident.row (L.row.symm r))]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hiff : L.row x.stablePath = r ↔ ψ.ident.row x.stablePath = ψ.ident.row (L.row.symm r) := by
      rw [ψ.ident.row.injective.eq_iff, Equiv.eq_symm_apply]
    by_cases hx : L.row x.stablePath = r
    · rw [if_pos hx, if_pos (hiff.mp hx), Equiv.apply_symm_apply]
      rfl
    · rw [if_neg hx, if_neg (fun h ↦ hx (hiff.mpr h))])
  funext e
  have := congrFun hc (L.targetEdge.symm e)
  simp only [Equiv.apply_symm_apply] at this
  exact this

/-- **The placement is forced**, the statement of `GluingWellDefined.placement_forced`. -/
theorem placement_forced' (hl₀ : core.tail s.first ≠ core.head s.first)
    (hl₁ : (subdivide core s.first).tail s.second ≠ (subdivide core s.first).head s.second)
    (hl₂ : (subdivide (subdivide core s.first) s.second).tail s.third ≠
      (subdivide (subdivide core s.first) s.second).head s.third)
    {y : Fin (p + 1 + 1 + 1 + 3) → ℚ} {ψ : FibreMember core (baseRequest s y) (2 + 2)}
    {φ φ' : FibreMember (tripodCore core s) y (3 + 2)} (hφ : φ.Open) (hφ' : φ'.Open)
    {π π' : Placement ψ.target (2 + 2)} (hπ : π.NonDangling ψ.data)
    (hπ' : π'.NonDangling ψ.data)
    (iso : GeometricDatumIso (glueDatum ψ.data π) φ.data)
    (iso' : GeometricDatumIso (glueDatum ψ.data π') φ'.data)
    (hL : GluedLabels s ψ π φ.ident iso) (hL' : GluedLabels s ψ π' φ'.ident iso') :
    ∃ σ : Fin 3 → Fin (2 + 2), π' = ⟨π.edge₀, π.edge₁, π.edge₂, σ⟩ ∧
      ∀ k, (ψ.data.edgePartition (π.parentEdge k)).Rel (π.sheet k) (σ k) := by
  classical
  have hD := ψ.fullDim.valid.1
  set W : ψ.target.edges → ℚ := fun e ↦ ψ.coords (ψ.fullDim.labelling.targetEdge.symm e) with hW
  -- the label data of a gluing at the third stage, merged back to the rows of `ψ`
  have key : ∀ (π : Placement ψ.target (2 + 2)) (hπ : π.NonDangling ψ.data)
      (φ : FibreMember (tripodCore core s) y (3 + 2)) (_ : φ.Open)
      (iso : GeometricDatumIso (glueDatum ψ.data π) φ.data) (_ : GluedLabels s ψ π φ.ident iso),
      ∃ R₃ : LabelData (refineDatum (refineDatum (refineDatum ψ.data (mkEdge₀ π hπ).1.1.1)
          (mkEdge₁ hD π hπ).1.1.1) (mkEdge₂ hD π hπ).1.1.1)
        (subdivide (subdivide (subdivide core s.first) s.second) s.third)
        (newV (newV (newV (V₀ ψ) (mkEdge₀ π hπ)) (mkEdge₁ hD π hπ))
          (mkEdge₂ hD π hπ)) (gPart y),
        (∀ ε, 0 < R₃.w ε) ∧
        ((R₃.down (refineDatum_connected _ _ (refineDatum_connected _ _ hD)) s.third
          (mkEdge₂ hD π hπ)).down (refineDatum_connected _ _ hD) s.second
            (mkEdge₁ hD π hπ) |>.down hD s.first (mkEdge₀ π hπ)).lab =
          (fun x ↦ ψ.ident.row x.stablePath) ∧
        ((R₃.down (refineDatum_connected _ _ (refineDatum_connected _ _ hD)) s.third
          (mkEdge₂ hD π hπ)).down (refineDatum_connected _ _ hD) s.second
            (mkEdge₁ hD π hπ) |>.down hD s.first (mkEdge₀ π hπ)).w = W := by
    intro π hπ φ hφ iso hL
    have h1 := newV₃_mOld_mk hD π hπ (V₀ ψ)
    have h2 := newV₃_markVertex_mk hD π hπ (V₀ ψ)
    have hR := labelData₃_of_gluing (V₃ := newV (newV (newV (V₀ ψ)
      (mkEdge₀ π hπ)) (mkEdge₁ hD π hπ)) (mkEdge₂ hD π hπ)) hπ iso hL h1 h2 hφ
    have hR' : ∃ R₃ : LabelData (refineDatum (refineDatum (refineDatum ψ.data
          (mkEdge₀ π hπ).1.1.1) (mkEdge₁ hD π hπ).1.1.1) (mkEdge₂ hD π hπ).1.1.1)
        (subdivide (subdivide (subdivide core s.first) s.second) s.third)
        (newV (newV (newV (V₀ ψ) (mkEdge₀ π hπ)) (mkEdge₁ hD π hπ))
          (mkEdge₂ hD π hπ)) (gPart y),
        (∀ ε, 0 < R₃.w ε) ∧
        ∀ z, mergeOne s.first (mergeOne s.second (mergeOne s.third (R₃.lab z))) =
          ψ.ident.row (parentND₃ (π := π) z).stablePath := by
      rcases hR with ⟨R, h1, h2⟩
      exact ⟨R, h1, h2⟩
    rcases hR' with ⟨R₃, hpos, hmerge⟩
    have hlab : ((R₃.down (refineDatum_connected _ _ (refineDatum_connected _ _ hD)) s.third
        (mkEdge₂ hD π hπ)).down (refineDatum_connected _ _ hD) s.second
          (mkEdge₁ hD π hπ) |>.down hD s.first (mkEdge₀ π hπ)).lab =
        (fun x ↦ ψ.ident.row x.stablePath) := by
      funext x
      rw [LabelData.down₃_lab, hmerge]
      congr 2
      apply Subtype.ext
      simp only [parentND₃, parentSE₃, Refine.someHalfND, Refine.parentSE_someHalf]
    refine ⟨R₃, hpos, hlab, ?_⟩
    apply w_eq_coords ψ
    intro i
    have h := (((R₃.down (refineDatum_connected _ _ (refineDatum_connected _ _ hD)) s.third
        (mkEdge₂ hD π hπ)).down (refineDatum_connected _ _ hD) s.second
          (mkEdge₁ hD π hπ) |>.down hD s.first (mkEdge₀ π hπ))).len i
    rw [hlab] at h
    exact h
  have hk := key π hπ φ hφ iso hL
  have hk' := key π' hπ' φ' hφ' iso' hL'
  rcases hk with ⟨R₃, hpos, hlab, hw⟩
  rcases hk' with ⟨R₃', hpos', hlab', hw'⟩
  -- stage zero, at the coordinates of `ψ`
  have hW : ∀ e, 0 ≤ W e := fun e ↦ by
    rw [← hw]
    exact (LabelData.down_pos _ _ _ _ (LabelData.down_pos _ _ _ _
      (LabelData.down_pos _ _ _ _ hpos)) e).le
  obtain ⟨L₀, hL₀lab, hL₀w⟩ := exists_layout₀ ψ W hW (len_of_member ψ)
  have hy₃ : ∀ i, 0 < gPart y i := fun i ↦ request_pos_of_open φ hφ _
  have h3 := three_forced hD (V₀_injective ψ) s.first s.second s.third hl₀ hl₁ hl₂
    hy₃ L₀ _ _ _ R₃ hpos (hlab.trans hL₀lab.symm) (hw.trans hL₀w.symm) _ _ _ R₃'
    (hlab'.trans hL₀lab.symm) (hw'.trans hL₀w.symm)
  rcases h3 with ⟨hx₀, hx₁, hx₂⟩
  -- the placements agree, up to the sheets
  obtain ⟨e₀, e₁, e₂, σ⟩ := π
  obtain ⟨e₀', e₁', e₂', σ'⟩ := π'
  have he₀ : e₀ = e₀' := congrArg (fun x : NonDanglingEdge ψ.data ↦ x.1.1.1) hx₀
  subst he₀
  have hx₁' := eq_of_heq hx₁
  have he₁ : e₁ = e₁' := congrArg (fun x : NonDanglingEdge (refineDatum ψ.data e₀) ↦ x.1.1.1) hx₁'
  subst he₁
  have hx₂' := eq_of_heq hx₂
  have he₂ : e₂ = e₂' :=
    congrArg (fun x : NonDanglingEdge (refineDatum (refineDatum ψ.data e₀) e₁) ↦ x.1.1.1) hx₂'
  subst he₂
  refine ⟨σ', rfl, fun k ↦ ?_⟩
  rw [SheetPartition.rel_iff]
  fin_cases k
  · exact congrArg (fun x : NonDanglingEdge ψ.data ↦ x.1.1.2) hx₀
  · have h := congrArg (fun x : NonDanglingEdge (refineDatum ψ.data e₀) ↦ x.1.1.2) hx₁'
    change ((refineDatum ψ.data e₀).edgePartition e₁).repr (σ 1) =
      ((refineDatum ψ.data e₀).edgePartition e₁).repr (σ' 1) at h
    rw [refineDatum_edgePartition] at h
    exact h
  · have h := congrArg
      (fun x : NonDanglingEdge (refineDatum (refineDatum ψ.data e₀) e₁) ↦ x.1.1.2) hx₂'
    change ((refineDatum (refineDatum ψ.data e₀) e₁).edgePartition e₂).repr (σ 2) =
      ((refineDatum (refineDatum ψ.data e₀) e₁).edgePartition e₂).repr (σ' 2) at h
    rw [refineDatum_edgePartition, refineDatum_edgePartition] at h
    exact h

end Forced

end Chains

end GenusSixExistence.Tripod.Gluing

end
