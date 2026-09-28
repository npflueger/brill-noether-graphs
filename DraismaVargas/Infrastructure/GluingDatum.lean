import Mathlib.Data.Multiset.Fintype
import Utilities.Harmonic.Basic
import DraismaVargas.Infrastructure.SheetPartition

/-!
# Finite sheet-partition gluing data

This module introduces the global finite object used in Draisma--Vargas Part
I.  A relation above every target vertex and every *edge occurrence* partitions
the finite sheet set.  Edge relations refine the relations at both endpoints.

The quotient source is constructed literally: its vertices and edge
occurrences are the blocks above target vertices and edges.  Using the
multiset-as-type for target edges keeps parallel target occurrences distinct.
The remaining gluing-datum conditions (`Connected` and
`RiemannHurwitz`) are exposed as propositions rather than hidden in the data.
-/

namespace DraismaVargas.Infrastructure

open Finset

/-- Exhaustive finite connectedness replay for an arbitrary concrete graph. -/
def graphConnectedCheck (graph : CFGraph) : Bool :=
  @decide (graph_connected graph) Fintype.decidableForallFintype

@[simp] theorem graphConnectedCheck_eq_true_iff (graph : CFGraph) :
    graphConnectedCheck graph = true ↔ graph_connected graph := by
  unfold graphConnectedCheck
  exact @decide_eq_true_iff (graph_connected graph)
    Fintype.decidableForallFintype

namespace SheetPartition

/-- The finite type of blocks of a sheet partition, represented by its fixed
canonical representatives. -/
def Blocks (partition : SheetPartition d) :=
  {i : Fin d // partition.repr i = i}

instance (partition : SheetPartition d) : Fintype partition.Blocks :=
  inferInstanceAs (Fintype {i : Fin d // partition.repr i = i})

instance (partition : SheetPartition d) : DecidableEq partition.Blocks :=
  inferInstanceAs (DecidableEq {i : Fin d // partition.repr i = i})

/-- The block containing `i`, as its canonical representative. -/
def toBlock (partition : SheetPartition d) (i : Fin d) : partition.Blocks :=
  ⟨partition.repr i, partition.repr_idem i⟩

@[simp] theorem toBlock_val (partition : SheetPartition d) (i : Fin d) :
    (partition.toBlock i).1 = partition.repr i := rfl

end SheetPartition

/-- The verticality and refinement data of a finite DV gluing datum over a
fixed target graph.  Target edges are occurrences, not endpoint pairs. -/
structure GluingDatum (target : CFGraph) (degree : ℕ) where
  degree_pos : 0 < degree
  vertexPartition : target.V → SheetPartition degree
  edgePartition : target.edges → SheetPartition degree
  refines_left : ∀ edge,
    (edgePartition edge).Refines (vertexPartition (edge : target.V × target.V).1)
  refines_right : ∀ edge,
    (edgePartition edge).Refines (vertexPartition (edge : target.V × target.V).2)

/-- Two gluing data over the same target and degree agree as soon as both
partition assignments do: the remaining three fields are propositions.
`LocalCases.W3ShiftIncomingTransport` uses it to prove that contraction
commutes with the branch swap as a literal equality of data. -/
theorem gluingDatum_ext {target : CFGraph} {degree : ℕ}
    {first second : GluingDatum target degree}
    (hVertex : first.vertexPartition = second.vertexPartition)
    (hEdge : first.edgePartition = second.edgePartition) : first = second := by
  revert hVertex hEdge
  obtain ⟨-, vertexFirst, edgeFirst, -, -⟩ := first
  obtain ⟨-, vertexSecond, edgeSecond, -, -⟩ := second
  intro hVertex hEdge
  have hV : vertexFirst = vertexSecond := hVertex
  have hE : edgeFirst = edgeSecond := hEdge
  subst hV
  subst hE
  rfl

namespace GluingDatum

variable {target : CFGraph} {degree : ℕ}

/-- Vertices of the quotient source: one block above one target vertex. -/
def SourceVertex (data : GluingDatum target degree) :=
  {item : target.V × Fin degree //
    (data.vertexPartition item.1).repr item.2 = item.2}

/-- Edge occurrences of the quotient source: one block above one target edge
occurrence. -/
def SourceEdge (data : GluingDatum target degree) :=
  {item : target.edges × Fin degree //
    (data.edgePartition item.1).repr item.2 = item.2}

instance (data : GluingDatum target degree) :
    DecidableEq data.SourceVertex := by
  unfold SourceVertex
  infer_instance

noncomputable instance (data : GluingDatum target degree) :
    DecidableEq data.SourceEdge := Classical.decEq _

instance (data : GluingDatum target degree) :
    Fintype data.SourceVertex := by
  unfold SourceVertex
  infer_instance

instance (data : GluingDatum target degree) :
    Fintype data.SourceEdge := by
  unfold SourceEdge
  infer_instance

/-- Canonical quotient-source edge block above a target occurrence and
containing a chosen sheet. -/
noncomputable def sourceEdge (data : GluingDatum target degree)
    (edge : target.edges) (sheet : Fin degree) : data.SourceEdge :=
  ⟨(edge, (data.edgePartition edge).repr sheet),
    (data.edgePartition edge).repr_idem sheet⟩

@[simp] theorem sourceEdge_target (data : GluingDatum target degree)
    (edge : target.edges) (sheet : Fin degree) :
    (data.sourceEdge edge sheet).1.1 = edge := rfl

@[simp] theorem sourceEdge_sheet (data : GluingDatum target degree)
    (edge : target.edges) (sheet : Fin degree) :
    (data.sourceEdge edge sheet).1.2 =
      (data.edgePartition edge).repr sheet := rfl

/-- The local degrees of all quotient-source vertices over any fixed target
vertex add up to the sheet degree. -/
theorem sum_sourceVertex_localDegree_over (data : GluingDatum target degree)
    (root : target.V) :
    (∑ vertex : data.SourceVertex,
      if vertex.1.1 = root then
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ)
      else 0) = degree := by
  let summand : target.V × Fin degree → ℤ := fun item ↦
    if item.1 = root then
      ((data.vertexPartition item.1).blockCard item.2 : ℤ)
    else 0
  have hEnumerate :
      (∑ vertex : data.SourceVertex, summand vertex.1) =
        ∑ item : target.V × Fin degree,
          if (data.vertexPartition item.1).repr item.2 = item.2 then
            summand item
          else 0 := by
    calc
      (∑ vertex : data.SourceVertex, summand vertex.1) =
          ∑ item ∈ Finset.univ.filter
              (fun item : target.V × Fin degree ↦
                (data.vertexPartition item.1).repr item.2 = item.2),
            summand item := by
        symm
        exact Finset.sum_subtype _ (by simp) summand
      _ = ∑ item : target.V × Fin degree,
          if (data.vertexPartition item.1).repr item.2 = item.2 then
            summand item
          else 0 := by
        rw [Finset.sum_filter]
  change (∑ vertex : data.SourceVertex, summand vertex.1) = degree
  rw [hEnumerate, Fintype.sum_prod_type]
  refine (Fintype.sum_eq_single root ?_).trans ?_
  · intro vertex hne
    apply Finset.sum_eq_zero
    intro sheet _
    simp [summand, hne]
  · simp only [summand, if_pos]
    exact (data.vertexPartition root).sum_blockCard_representatives_eq_degree
      data.degree_pos

/-- Endpoint above one end of the underlying target occurrence. -/
def sourceEndpoint (data : GluingDatum target degree)
    (vertex : target.V) (sheet : Fin degree) : data.SourceVertex :=
  ⟨(vertex, (data.vertexPartition vertex).repr sheet),
    (data.vertexPartition vertex).repr_idem sheet⟩

/-- Equality with a quotient-source vertex separates into equality of target
vertices and membership in its sheet block. -/
@[simp] theorem sourceEndpoint_eq_iff (data : GluingDatum target degree)
    (vertex : target.V) (sheet : Fin degree) (sourceVertex : data.SourceVertex) :
    data.sourceEndpoint vertex sheet = sourceVertex ↔
      vertex = sourceVertex.1.1 ∧
        (data.vertexPartition vertex).Rel sheet sourceVertex.1.2 := by
  constructor
  · intro h
    have hVertex := congrArg (fun item : data.SourceVertex ↦ item.1.1) h
    have hSheet := congrArg (fun item : data.SourceVertex ↦ item.1.2) h
    have hVertexEq : vertex = sourceVertex.1.1 := hVertex
    have hSheetEq : (data.vertexPartition vertex).repr sheet =
        sourceVertex.1.2 := hSheet
    refine ⟨hVertexEq, ?_⟩
    unfold SheetPartition.Rel
    rw [show (data.vertexPartition vertex).repr sheet = sourceVertex.1.2 by
      exact hSheetEq]
    rw [show (data.vertexPartition vertex).repr sourceVertex.1.2 =
        sourceVertex.1.2 by
      rw [hVertexEq]
      exact sourceVertex.2]
  · rintro ⟨hVertex, hSheet⟩
    subst vertex
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · unfold SheetPartition.Rel at hSheet
      change (data.vertexPartition sourceVertex.1.1).repr sheet = sourceVertex.1.2
      exact hSheet.trans sourceVertex.2

/-- Reconstructing a quotient-source vertex from its stored target vertex and
sheet representative gives the vertex itself. -/
@[simp] theorem sourceEndpoint_self (data : GluingDatum target degree)
    (sourceVertex : data.SourceVertex) :
    data.sourceEndpoint sourceVertex.1.1 sourceVertex.1.2 = sourceVertex := by
  apply (data.sourceEndpoint_eq_iff sourceVertex.1.1 sourceVertex.1.2
    sourceVertex).mpr
  exact ⟨rfl, rfl⟩

/-- Ordered endpoints of a quotient-source edge occurrence. -/
def sourceEnds (data : GluingDatum target degree)
    (edge : data.SourceEdge) : data.SourceVertex × data.SourceVertex :=
  (data.sourceEndpoint (edge.1.1 : target.V × target.V).1 edge.1.2,
    data.sourceEndpoint (edge.1.1 : target.V × target.V).2 edge.1.2)

/-- A quotient-source edge occurrence never joins a vertex to itself: its two
endpoints sit over the two ends of a target occurrence, and the target is
loopless. -/
theorem sourceEnds_ne (data : GluingDatum target degree)
    (edge : data.SourceEdge) : (data.sourceEnds edge).1 ≠ (data.sourceEnds edge).2 := by
  intro h
  have hTarget : (edge.1.1 : target.V × target.V).1 =
      (edge.1.1 : target.V × target.V).2 :=
    congrArg (fun vertex : data.SourceVertex => vertex.1.1) h
  have hEdgeMem : (edge.1.1 : target.V × target.V) ∈ target.edges :=
    Multiset.coe_mem
  have hPair : (edge.1.1 : target.V × target.V) =
      ((edge.1.1 : target.V × target.V).1,
        (edge.1.1 : target.V × target.V).1) := by
    apply Prod.ext
    · rfl
    · exact hTarget.symm
  rw [hPair] at hEdgeMem
  exact target.loopless (edge.1.1 : target.V × target.V).1 hEdgeMem

/-- The literal finite quotient graph `G = (T × [d]) / ∼`. -/
def sourceGraph (data : GluingDatum target degree) : CFGraph where
  V := data.SourceVertex
  instNonempty := by
    let sheet : Fin degree := ⟨0, data.degree_pos⟩
    let vertex : target.V := Classical.choice inferInstance
    exact ⟨data.sourceEndpoint vertex sheet⟩
  edges := (Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds
  loopless := by
    intro vertex hmem
    simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and] at hmem
    obtain ⟨edge, hedge⟩ := hmem
    exact data.sourceEnds_ne edge (by
      rw [hedge])

/-- Edge occurrences incident to a target vertex. -/
def incidentEdges (vertex : target.V) : Finset target.edges :=
  ((Finset.univ : Finset target.edges).filter fun (edge : target.edges) =>
    (edge : target.V × target.V).1 = vertex ∨
      (edge : target.V × target.V).2 = vertex)

/-- The local Riemann--Hurwitz condition at every target vertex. -/
def RiemannHurwitz (data : GluingDatum target degree) : Prop :=
  ∀ vertex sheet,
    (∑ edge ∈ incidentEdges vertex,
      ((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) sheet : ℤ)) - 2 ≥
    ((data.vertexPartition vertex).blockCard sheet : ℤ) *
      (((incidentEdges vertex).card : ℤ) - 2)

/-- The one-target-vertex component of `RiemannHurwitz`. -/
def RiemannHurwitzAtTargetVertex (data : GluingDatum target degree)
    (vertex : target.V) : Prop :=
  ∀ sheet,
    (∑ edge ∈ incidentEdges vertex,
      ((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) sheet : ℤ)) - 2 ≥
    ((data.vertexPartition vertex).blockCard sheet : ℤ) *
      (((incidentEdges vertex).card : ℤ) - 2)

theorem riemannHurwitz_iff_forall_targetVertex
    (data : GluingDatum target degree) :
    data.RiemannHurwitz ↔ ∀ vertex, data.RiemannHurwitzAtTargetVertex vertex :=
  Iff.rfl

/-- A list whose underlying occurrence multiset is the incident edge finset
converts the target-vertex condition to the list form consumed by local case
receipts. The multiset equality itself records both coverage and absence of
duplicates without requiring decidable equality on occurrences. -/
theorem riemannHurwitzAtTargetVertex_iff_incidentList
    (data : GluingDatum target degree) (vertex : target.V)
    (edges : List target.edges)
    (hEdges : (edges : Multiset target.edges) = (incidentEdges vertex).val) :
    data.RiemannHurwitzAtTargetVertex vertex ↔
      SheetPartition.RiemannHurwitzAt (data.vertexPartition vertex)
        (edges.map data.edgePartition) := by
  have hLength : (edges.map data.edgePartition).length =
      (incidentEdges vertex).card := by
    have hCard := congrArg Multiset.card hEdges
    simpa using hCard
  constructor
  · intro h
    unfold SheetPartition.RiemannHurwitzAt
    intro sheet
    rw [List.map_map]
    change (edges.map (fun edge ↦
      ((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) sheet : ℤ))).sum - 2 ≥
      ((data.vertexPartition vertex).blockCard sheet : ℤ) *
        (((edges.map data.edgePartition).length : ℤ) - 2)
    have hSum :
        (edges.map (fun edge ↦
          ((data.edgePartition edge).blockCountWithin
            (data.vertexPartition vertex) sheet : ℤ))).sum =
          ∑ edge ∈ incidentEdges vertex,
            ((data.edgePartition edge).blockCountWithin
              (data.vertexPartition vertex) sheet : ℤ) := by
      have hMapped := congrArg
        (fun multiset : Multiset target.edges ↦
          (multiset.map (fun edge ↦
            ((data.edgePartition edge).blockCountWithin
              (data.vertexPartition vertex) sheet : ℤ))).sum) hEdges
      simpa using hMapped
    rw [hSum, hLength]
    exact h sheet
  · intro h
    unfold SheetPartition.RiemannHurwitzAt at h
    intro sheet
    have hList := h sheet
    rw [List.map_map] at hList
    change (edges.map (fun edge ↦
      ((data.edgePartition edge).blockCountWithin
        (data.vertexPartition vertex) sheet : ℤ))).sum - 2 ≥
      ((data.vertexPartition vertex).blockCard sheet : ℤ) *
        (((edges.map data.edgePartition).length : ℤ) - 2) at hList
    have hSum :
        (edges.map (fun edge ↦
          ((data.edgePartition edge).blockCountWithin
            (data.vertexPartition vertex) sheet : ℤ))).sum =
          ∑ edge ∈ incidentEdges vertex,
            ((data.edgePartition edge).blockCountWithin
              (data.vertexPartition vertex) sheet : ℤ) := by
      have hMapped := congrArg
        (fun multiset : Multiset target.edges ↦
          (multiset.map (fun edge ↦
            ((data.edgePartition edge).blockCountWithin
              (data.vertexPartition vertex) sheet : ℤ))).sum) hEdges
      simpa using hMapped
    rw [hSum, hLength] at hList
    exact hList

/-- The quotient-source connectedness condition. -/
def Connected (data : GluingDatum target degree) : Prop :=
  graph_connected data.sourceGraph

/-- All four defining conditions of a DV gluing datum: verticality is built
into the indexed partition fields, refinement is stored in the structure,
and these are the connectedness and Riemann--Hurwitz conditions. -/
def Valid (data : GluingDatum target degree) : Prop :=
  data.Connected ∧ data.RiemannHurwitz

/-- Exhaustive finite connectedness replay for a concrete gluing datum. -/
def checkConnected (data : GluingDatum target degree) : Bool :=
  graphConnectedCheck data.sourceGraph

/-- Exhaustive finite local Riemann--Hurwitz replay. -/
def checkRiemannHurwitz (data : GluingDatum target degree) : Bool :=
  @decide data.RiemannHurwitz Fintype.decidableForallFintype

/-- Exact finite checker for the remaining gluing-datum conditions. -/
def check (data : GluingDatum target degree) : Bool :=
  data.checkConnected && data.checkRiemannHurwitz

@[simp] theorem checkConnected_eq_true_iff (data : GluingDatum target degree) :
    data.checkConnected = true ↔ data.Connected := by
  simp [checkConnected, Connected]

@[simp] theorem checkRiemannHurwitz_eq_true_iff
    (data : GluingDatum target degree) :
    data.checkRiemannHurwitz = true ↔ data.RiemannHurwitz := by
  unfold checkRiemannHurwitz
  exact @decide_eq_true_iff data.RiemannHurwitz
    Fintype.decidableForallFintype

@[simp] theorem check_eq_true_iff (data : GluingDatum target degree) :
    data.check = true ↔ data.Valid := by
  simp [check, Valid]

/-! ## The indexed harmonic map carried by a gluing datum -/

/-- Dilation index of one quotient-source edge block. -/
def sourceEdgeIndex (data : GluingDatum target degree)
    (edge : data.SourceEdge) : ℕ :=
  (data.edgePartition edge.1.1).blockCard edge.1.2

/-- The index of the canonical source edge through a sheet is the cardinality
of that sheet's edge-partition block. -/
@[simp] theorem sourceEdgeIndex_sourceEdge (data : GluingDatum target degree)
    (edge : target.edges) (sheet : Fin degree) :
    data.sourceEdgeIndex (data.sourceEdge edge sheet) =
      (data.edgePartition edge).blockCard sheet := by
  unfold sourceEdgeIndex sourceEdge
  simpa [SheetPartition.blockCard] using congrArg Finset.card
    ((data.edgePartition edge).block_eq_of_rel
      ((data.edgePartition edge).rel_repr_left sheet))

/-- Above the left endpoint of a target-edge occurrence, the indices of all
source edge blocks meeting a fixed vertex block sum to that vertex block's
local degree. -/
theorem sum_sourceEdgeIndex_left (data : GluingDatum target degree)
    (edge : target.edges) (sheet : Fin degree) :
    (∑ representative : Fin degree,
      if (data.edgePartition edge).repr representative = representative ∧
          (data.vertexPartition (edge : target.V × target.V).1).Rel
            sheet representative then
        ((data.edgePartition edge).blockCard representative : ℤ)
      else 0) =
    ((data.vertexPartition (edge : target.V × target.V).1).blockCard sheet : ℤ) := by
  exact SheetPartition.sum_blockCard_representatives_eq_blockCard
    (data.edgePartition edge)
    (data.vertexPartition (edge : target.V × target.V).1)
    (data.refines_left edge) sheet

/-- Above the right endpoint of a target-edge occurrence, the indices of all
source edge blocks meeting a fixed vertex block sum to that vertex block's
local degree. -/
theorem sum_sourceEdgeIndex_right (data : GluingDatum target degree)
    (edge : target.edges) (sheet : Fin degree) :
    (∑ representative : Fin degree,
      if (data.edgePartition edge).repr representative = representative ∧
          (data.vertexPartition (edge : target.V × target.V).2).Rel
            sheet representative then
        ((data.edgePartition edge).blockCard representative : ℤ)
      else 0) =
    ((data.vertexPartition (edge : target.V × target.V).2).blockCard sheet : ℤ) := by
  exact SheetPartition.sum_blockCard_representatives_eq_blockCard
    (data.edgePartition edge)
    (data.vertexPartition (edge : target.V × target.V).2)
    (data.refines_right edge) sheet

/-- Signed source-edge incidence after pulling a slope on each target-edge
occurrence back with the corresponding sheet-block index. -/
def sourceEdgeIncidence (data : GluingDatum target degree)
    (targetSlope : target.edges → ℤ) (vertex : data.SourceVertex) : ℤ :=
  ∑ edge : data.SourceEdge,
    ((if (data.sourceEnds edge).1 = vertex then
        (data.sourceEdgeIndex edge : ℤ) * targetSlope edge.1.1
      else 0) +
      (if (data.sourceEnds edge).2 = vertex then
        (data.sourceEdgeIndex edge : ℤ) * (-targetSlope edge.1.1)
      else 0))

/-- Signed incidence of slopes on the occurrence-labelled target graph. -/
def targetEdgeIncidence (targetSlope : target.edges → ℤ)
    (vertex : target.V) : ℤ :=
  ∑ edge : target.edges,
    ((if (edge : target.V × target.V).1 = vertex then targetSlope edge else 0) +
      (if (edge : target.V × target.V).2 = vertex then -targetSlope edge else 0))

/-- Sheet-partition refinement is exactly the harmonic incidence equation,
before any subdivision presentation or divisor language is introduced. -/
theorem sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence
    (data : GluingDatum target degree) (targetSlope : target.edges → ℤ)
    (vertex : data.SourceVertex) :
    data.sourceEdgeIncidence targetSlope vertex =
      ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
        targetEdgeIncidence targetSlope vertex.1.1 := by
  let summand : target.edges × Fin degree → ℤ := fun item ↦
    ((if data.sourceEndpoint (item.1 : target.V × target.V).1 item.2 = vertex then
        ((data.edgePartition item.1).blockCard item.2 : ℤ) * targetSlope item.1
      else 0) +
      (if data.sourceEndpoint (item.1 : target.V × target.V).2 item.2 = vertex then
        ((data.edgePartition item.1).blockCard item.2 : ℤ) * (-targetSlope item.1)
      else 0))
  have hEnumerate :
      (∑ edge : data.SourceEdge, summand edge.1) =
        ∑ item : target.edges × Fin degree,
          if (data.edgePartition item.1).repr item.2 = item.2 then
            summand item
          else 0 := by
    calc
      (∑ edge : data.SourceEdge, summand edge.1) =
          ∑ item ∈ Finset.univ.filter
              (fun item : target.edges × Fin degree ↦
                (data.edgePartition item.1).repr item.2 = item.2),
            summand item := by
        symm
        exact Finset.sum_subtype _ (by simp) summand
      _ = ∑ item : target.edges × Fin degree,
          if (data.edgePartition item.1).repr item.2 = item.2 then
            summand item
          else 0 := by
        rw [Finset.sum_filter]
  have hLeft (edge : target.edges) :
      (∑ representative : Fin degree,
        if (data.edgePartition edge).repr representative = representative then
          if data.sourceEndpoint (edge : target.V × target.V).1
              representative = vertex then
            ((data.edgePartition edge).blockCard representative : ℤ) *
              targetSlope edge
          else 0
        else 0) =
      if (edge : target.V × target.V).1 = vertex.1.1 then
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
          targetSlope edge
      else 0 := by
    by_cases hTail : (edge : target.V × target.V).1 = vertex.1.1
    · rw [if_pos hTail]
      calc
        (∑ representative : Fin degree,
          if (data.edgePartition edge).repr representative = representative then
            if data.sourceEndpoint (edge : target.V × target.V).1
                representative = vertex then
              ((data.edgePartition edge).blockCard representative : ℤ) *
                targetSlope edge
            else 0
          else 0) =
            ∑ representative : Fin degree,
              if (data.edgePartition edge).repr representative = representative ∧
                  (data.vertexPartition (edge : target.V × target.V).1).Rel
                    vertex.1.2 representative then
                ((data.edgePartition edge).blockCard representative : ℤ) *
                  targetSlope edge
              else 0 := by
          apply Finset.sum_congr rfl
          intro representative _
          by_cases hRepresentative :
              (data.edgePartition edge).repr representative = representative
          · have hEndpoint :
                data.sourceEndpoint (edge : target.V × target.V).1
                    representative = vertex ↔
                  (data.vertexPartition (edge : target.V × target.V).1).Rel
                    vertex.1.2 representative := by
              rw [sourceEndpoint_eq_iff]
              simp only [hTail, true_and]
              exact eq_comm
            by_cases hRel :
                (data.vertexPartition (edge : target.V × target.V).1).Rel
                  vertex.1.2 representative
            · rw [if_pos hRepresentative, if_pos (hEndpoint.mpr hRel),
                if_pos ⟨hRepresentative, hRel⟩]
            · rw [if_pos hRepresentative,
                if_neg (fun h ↦ hRel (hEndpoint.mp h)),
                if_neg (fun h ↦ hRel h.2)]
          · simp [hRepresentative]
        _ = ((data.vertexPartition (edge : target.V × target.V).1).blockCard
              vertex.1.2 : ℤ) * targetSlope edge :=
          SheetPartition.sum_blockCard_representatives_mul_eq_blockCard_mul
            (data.edgePartition edge)
            (data.vertexPartition (edge : target.V × target.V).1)
            (data.refines_left edge) vertex.1.2 (targetSlope edge)
        _ = ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
              targetSlope edge := by rw [hTail]
    · rw [if_neg hTail]
      apply Finset.sum_eq_zero
      intro representative _
      simp [sourceEndpoint_eq_iff, hTail]
  have hRight (edge : target.edges) :
      (∑ representative : Fin degree,
        if (data.edgePartition edge).repr representative = representative then
          if data.sourceEndpoint (edge : target.V × target.V).2
              representative = vertex then
            ((data.edgePartition edge).blockCard representative : ℤ) *
              (-targetSlope edge)
          else 0
        else 0) =
      if (edge : target.V × target.V).2 = vertex.1.1 then
        ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
          (-targetSlope edge)
      else 0 := by
    by_cases hHead : (edge : target.V × target.V).2 = vertex.1.1
    · rw [if_pos hHead]
      calc
        (∑ representative : Fin degree,
          if (data.edgePartition edge).repr representative = representative then
            if data.sourceEndpoint (edge : target.V × target.V).2
                representative = vertex then
              ((data.edgePartition edge).blockCard representative : ℤ) *
                (-targetSlope edge)
            else 0
          else 0) =
            ∑ representative : Fin degree,
              if (data.edgePartition edge).repr representative = representative ∧
                  (data.vertexPartition (edge : target.V × target.V).2).Rel
                    vertex.1.2 representative then
                ((data.edgePartition edge).blockCard representative : ℤ) *
                  (-targetSlope edge)
              else 0 := by
          apply Finset.sum_congr rfl
          intro representative _
          by_cases hRepresentative :
              (data.edgePartition edge).repr representative = representative
          · have hEndpoint :
                data.sourceEndpoint (edge : target.V × target.V).2
                    representative = vertex ↔
                  (data.vertexPartition (edge : target.V × target.V).2).Rel
                    vertex.1.2 representative := by
              rw [sourceEndpoint_eq_iff]
              simp only [hHead, true_and]
              exact eq_comm
            by_cases hRel :
                (data.vertexPartition (edge : target.V × target.V).2).Rel
                  vertex.1.2 representative
            · rw [if_pos hRepresentative, if_pos (hEndpoint.mpr hRel),
                if_pos ⟨hRepresentative, hRel⟩]
            · rw [if_pos hRepresentative,
                if_neg (fun h ↦ hRel (hEndpoint.mp h)),
                if_neg (fun h ↦ hRel h.2)]
          · simp [hRepresentative]
        _ = ((data.vertexPartition (edge : target.V × target.V).2).blockCard
              vertex.1.2 : ℤ) * (-targetSlope edge) :=
          SheetPartition.sum_blockCard_representatives_mul_eq_blockCard_mul
            (data.edgePartition edge)
            (data.vertexPartition (edge : target.V × target.V).2)
            (data.refines_right edge) vertex.1.2 (-targetSlope edge)
        _ = ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
              (-targetSlope edge) := by rw [hHead]
    · rw [if_neg hHead]
      apply Finset.sum_eq_zero
      intro representative _
      simp [sourceEndpoint_eq_iff, hHead]
  unfold sourceEdgeIncidence targetEdgeIncidence
  change (∑ edge : data.SourceEdge, summand edge.1) = _
  rw [hEnumerate, Fintype.sum_prod_type]
  calc
    (∑ edge : target.edges, ∑ representative : Fin degree,
      if (data.edgePartition edge).repr representative = representative then
        summand (edge, representative)
      else 0) =
        ∑ edge : target.edges,
          (((∑ representative : Fin degree,
              if (data.edgePartition edge).repr representative = representative then
                if data.sourceEndpoint (edge : target.V × target.V).1
                    representative = vertex then
                  ((data.edgePartition edge).blockCard representative : ℤ) *
                    targetSlope edge
                else 0
              else 0)) +
            (∑ representative : Fin degree,
              if (data.edgePartition edge).repr representative = representative then
                if data.sourceEndpoint (edge : target.V × target.V).2
                    representative = vertex then
                  ((data.edgePartition edge).blockCard representative : ℤ) *
                    (-targetSlope edge)
                else 0
              else 0)) := by
      apply Finset.sum_congr rfl
      intro edge _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro representative _
      by_cases hRepresentative :
          (data.edgePartition edge).repr representative = representative
      <;> simp [summand, hRepresentative]
    _ = ∑ edge : target.edges,
        (((if (edge : target.V × target.V).1 = vertex.1.1 then
            ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
              targetSlope edge
          else 0) +
          (if (edge : target.V × target.V).2 = vertex.1.1 then
            ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
              (-targetSlope edge)
          else 0))) := by
      apply Finset.sum_congr rfl
      intro edge _
      rw [hLeft edge, hRight edge]
    _ = ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) *
        ∑ edge : target.edges,
          ((if (edge : target.V × target.V).1 = vertex.1.1 then
              targetSlope edge else 0) +
            (if (edge : target.V × target.V).2 = vertex.1.1 then
              -targetSlope edge else 0)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro edge _
      by_cases hTail : (edge : target.V × target.V).1 = vertex.1.1 <;>
        by_cases hHead : (edge : target.V × target.V).2 = vertex.1.1 <;>
        simp [hTail, hHead]

/-- Total dilation index of the source bundle joining two quotient vertices. -/
def indexedMultiplicity (data : GluingDatum target degree)
    (first second : data.SourceVertex) : ℕ :=
  ∑ edge : data.SourceEdge,
    if data.sourceEnds edge = (first, second) ∨
        data.sourceEnds edge = (second, first) then
      data.sourceEdgeIndex edge
    else 0

/-- The canonical indexed harmonic certificate underlying a sheet gluing
datum.  Its validity is checked or proved separately; the data itself is the
literal quotient map with block cardinalities as local degrees and edge
indices. -/
def harmonicCertificate (data : GluingDatum target degree) :
    MarkedGraphs.IndexedHarmonicCertificate data.sourceGraph target where
  vertexMap := fun vertex ↦ vertex.1.1
  localDegree := fun vertex ↦
    (data.vertexPartition vertex.1.1).blockCard vertex.1.2
  edgeIndex := data.indexedMultiplicity

end GluingDatum

end DraismaVargas.Infrastructure
