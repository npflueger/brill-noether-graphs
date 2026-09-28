import DraismaVargas.LocalCases.TargetRelabelStable
import DraismaVargas.LocalCases.CaterpillarDatum

/-!
# Transport of a gluing datum along an isomorphism, and the induced stable dictionary

**Source.**  Draisma--Vargas Part I (arXiv:1909.12924), the compatible-labelling rule of
the section on inherited properties (`section-inherited-properties`): an
isomorphism of tropical morphisms is a relabelling of the target together with a
relabelling of the sheets above it.  In this library this file is the transport half of
the invariance of the multiplicity under isomorphism, and the second of the two pieces of
the finiteness of the fibre.

## The object

`DatumIso first second` is an isomorphism of gluing data over *different*
targets and a common degree:

* equivalences `targetVertex`, `targetEdge` of the target's vertices and **edge
  occurrences**, respecting both stored endpoints (`ends_fst`, `ends_snd`);
* a sheet permutation at every target vertex and at every target edge
  occurrence (`vertexPerm`, `edgePerm`);
* the two partition assignments correspond (`vertexPartition`, `edgePartition`);
* **compatibility** (`compatible_fst`, `compatible_snd`): the relative
  permutation `vertexPerm⁻¹ ∘ edgePerm` stays inside every block of the
  endpoint's vertex partition.

The last pair is exactly the condition of
`Infrastructure.GluingDatum.SheetRelabeling`, and it is not a decoration: it is
what makes the sheet permutations descend to a map of the *quotient source*
(`sourceEnds_map`).  Without it the two partition assignments can still
correspond while the induced vertex and edge maps disagree -- take the discrete
partition on an occurrence, a vertex partition with two blocks of size two at
its endpoint, the identity occurrence permutation and a vertex permutation
carrying one sheet out of its block.

Unlike `LocalCases.TargetRelabelPruning`, whose target isomorphism is a
`Utilities.CFGraphIso` and whose occurrence bijection is therefore *chosen* by
`GluingTransport.edgeEquiv`, the occurrence bijection here is **given as data**
and preserves the stored orientation, so no disjunction over reversed
occurrences appears anywhere below.

## What is proved

* `refl`, `symm`, `trans` -- `DatumIso` is an equivalence relation on gluing
  data of a fixed degree.
* `sourceVertexEquiv`, `sourceEdgeEquiv`, `sourceEnds_map`,
  `sourceEdgeIndex_map`, `incident_map_iff`, `num_edges_map`,
  `sourceGraphLaplacianEquiv`, `connected` -- the induced isomorphism of
  quotient sources, with dilation indices preserved.
* `isDangling_map_iff`, `nonDanglingEdgeEquiv`, `nonDanglingValency_map`,
  `consecutive_map_iff`, `stablePathEquiv`, `danglingEdgeNoGlue_map` -- pruning
  and the `Consecutive` relation transport, so the stable-path quotient is
  carried by the literal occurrence bijection (`Quot.congr`), not chosen from a
  cardinality.
* `occurrences_map`, `matrix_map` -- every entry of the natural stable-source
  matrix `LocalCases.StableSourceMatrix.matrix` is preserved.
* `branchVertexEquiv`, `incidenceCount_map`, **`graphEquivalence`** -- the
  induced dictionary of the stable graph, in
  `LocalCases.StableGraphIncidence.Equivalence`'s shape.  `Count.MemberIso`'s
  dictionaries `stableVertex`, `stableRow` and `incidence` are constructed from it.
* `branchVertexEquiv_refl`/`_symm`/`_trans`, `stablePathEquiv_refl`/`_symm`/
  `_trans` -- **functoriality of the induced dictionary**: it is compatible
  with `refl`, `symm` and `trans` on the nose; `MemberIso.refl`/`.symm`/`.trans` in
  `Count.Fibre` need exactly these six identities.
* `hasPathEnds_map`, `trivalent_map` -- the two stable-graph hypotheses of
  `FullDimensionalSourcePresentation` transport.
* `mem_incidentEdges_map`, `incidentEdges_card_map`, `targetNumEdges_map`,
  `targetLaplacianEquiv`, `targetConnected_map`, `targetEdgeCard_map`,
  `targetGenus_map`, `genus_sourceGraph`, `sourceGenus_map`,
  `blockCountWithin_map`, `riemannHurwitz_map`, `valid_map` -- the target-side
  and validity transport, everything `FullDimensionalSourcePresentation`'s
  remaining fields need.
* `ofSheetRelabeling`, `globalRelabeling`, `globalRelabelDatum`, `ofGlobalPerm`
  -- inhabitants: every compatible sheet relabelling is a `DatumIso`, and one
  permutation used at every target element is always compatible.

## Non-vacuity (`Witness`)

`catSheetIso m` is the caterpillar-of-loops datum of every even genus
`g = 2m + 2` relabelled by the transposition of sheets `0` and `1`.  It is
**not** the identity: `catSheetIso_vertexPerm_ne` shows its sheet permutation is
not `Equiv.refl`, and `catSheetIso_ne` shows the relabelled datum is a
*different* gluing datum (`pairPart_relabel_swap_ne`: the swap really moves the
pair partition `{0, j}`).

## What is not proved here

* `Count.MemberIso` carries a `DatumIso` as its `datum` field; the transport of
  presentations, length matrices and multiplicities along it is
  `DraismaVargasCount.TransportMultiplicity`, and none of them appears in this file.
* Nothing is claimed about the *existence* of an isomorphism between two given
  data, in particular no normal form for the target tree.  That is the other
  half of the finiteness of the fibre, `DraismaVargasCount.TargetNormalForm`.

## Consumers

`DraismaVargasCount.TransportMultiplicity` (the invariance and descent of the
multiplicity), and the finiteness `Fintype (Fibre …)` of `Count.FibreNormalForm`, which
needs this transport together with a normal form for genus-zero targets.
-/

namespace DraismaVargas.Count.Transport

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open Utilities Utilities.Certificate

variable {target₁ target₂ target₃ : CFGraph} {degree : ℕ}

/-- An isomorphism of gluing data. -/
structure DatumIso (first : GluingDatum target₁ degree)
    (second : GluingDatum target₂ degree) where
  targetVertex : target₁.V ≃ target₂.V
  targetEdge : target₁.edges ≃ target₂.edges
  ends_fst : ∀ edge : target₁.edges,
    ((targetEdge edge : target₂.V × target₂.V)).1 =
      targetVertex ((edge : target₁.V × target₁.V)).1
  ends_snd : ∀ edge : target₁.edges,
    ((targetEdge edge : target₂.V × target₂.V)).2 =
      targetVertex ((edge : target₁.V × target₁.V)).2
  vertexPerm : target₁.V → Equiv.Perm (Fin degree)
  edgePerm : target₁.edges → Equiv.Perm (Fin degree)
  vertexPartition : ∀ vertex : target₁.V,
    second.vertexPartition (targetVertex vertex) =
      (first.vertexPartition vertex).relabel (vertexPerm vertex)
  edgePartition : ∀ edge : target₁.edges,
    second.edgePartition (targetEdge edge) =
      (first.edgePartition edge).relabel (edgePerm edge)
  compatible_fst : ∀ (edge : target₁.edges) (sheet : Fin degree),
    (first.vertexPartition ((edge : target₁.V × target₁.V)).1).Rel
      ((vertexPerm ((edge : target₁.V × target₁.V)).1).symm (edgePerm edge sheet)) sheet
  compatible_snd : ∀ (edge : target₁.edges) (sheet : Fin degree),
    (first.vertexPartition ((edge : target₁.V × target₁.V)).2).Rel
      ((vertexPerm ((edge : target₁.V × target₁.V)).2).symm (edgePerm edge sheet)) sheet

namespace DatumIso

variable {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
variable {third : GluingDatum target₃ degree}

theorem vertexRepr_iff (iso : DatumIso first second) (vertex : target₁.V)
    (sheet : Fin degree) :
    (second.vertexPartition (iso.targetVertex vertex)).repr (iso.vertexPerm vertex sheet) =
        iso.vertexPerm vertex sheet ↔
      (first.vertexPartition vertex).repr sheet = sheet := by
  rw [iso.vertexPartition vertex]
  simp [SheetPartition.relabel]

theorem edgeRepr_iff (iso : DatumIso first second) (edge : target₁.edges)
    (sheet : Fin degree) :
    (second.edgePartition (iso.targetEdge edge)).repr (iso.edgePerm edge sheet) =
        iso.edgePerm edge sheet ↔
      (first.edgePartition edge).repr sheet = sheet := by
  rw [iso.edgePartition edge]
  simp [SheetPartition.relabel]

/-- The underlying bijection of vertex-sheet pairs. -/
def vertexPairEquiv (iso : DatumIso first second) :
    target₁.V × Fin degree ≃ target₂.V × Fin degree where
  toFun item := (iso.targetVertex item.1, iso.vertexPerm item.1 item.2)
  invFun item := (iso.targetVertex.symm item.1,
    (iso.vertexPerm (iso.targetVertex.symm item.1)).symm item.2)
  left_inv := by rintro ⟨vertex, sheet⟩; simp
  right_inv := by rintro ⟨vertex, sheet⟩; simp

/-- The underlying bijection of edge-sheet pairs. -/
def edgePairEquiv (iso : DatumIso first second) :
    target₁.edges × Fin degree ≃ target₂.edges × Fin degree where
  toFun item := (iso.targetEdge item.1, iso.edgePerm item.1 item.2)
  invFun item := (iso.targetEdge.symm item.1,
    (iso.edgePerm (iso.targetEdge.symm item.1)).symm item.2)
  left_inv := by rintro ⟨edge, sheet⟩; simp
  right_inv := by rintro ⟨edge, sheet⟩; simp

/-- Quotient-source vertices correspond. -/
def sourceVertexEquiv (iso : DatumIso first second) :
    first.SourceVertex ≃ second.SourceVertex :=
  Equiv.subtypeEquiv iso.vertexPairEquiv fun item ↦
    (iso.vertexRepr_iff item.1 item.2).symm

/-- Quotient-source edge occurrences correspond. -/
def sourceEdgeEquiv (iso : DatumIso first second) :
    first.SourceEdge ≃ second.SourceEdge :=
  Equiv.subtypeEquiv iso.edgePairEquiv fun item ↦
    (iso.edgeRepr_iff item.1 item.2).symm

@[simp] theorem sourceVertexEquiv_fst (iso : DatumIso first second)
    (vertex : first.SourceVertex) :
    (iso.sourceVertexEquiv vertex).1.1 = iso.targetVertex vertex.1.1 := rfl

@[simp] theorem sourceVertexEquiv_snd (iso : DatumIso first second)
    (vertex : first.SourceVertex) :
    (iso.sourceVertexEquiv vertex).1.2 = iso.vertexPerm vertex.1.1 vertex.1.2 := rfl

@[simp] theorem sourceEdgeEquiv_fst (iso : DatumIso first second)
    (edge : first.SourceEdge) :
    (iso.sourceEdgeEquiv edge).1.1 = iso.targetEdge edge.1.1 := rfl

@[simp] theorem sourceEdgeEquiv_snd (iso : DatumIso first second)
    (edge : first.SourceEdge) :
    (iso.sourceEdgeEquiv edge).1.2 = iso.edgePerm edge.1.1 edge.1.2 := rfl


/-! ### Two small relabelling identities -/

theorem relabel_refl (partition : SheetPartition degree) :
    partition.relabel (Equiv.refl (Fin degree)) = partition := by
  cases partition
  rfl

theorem relabel_symm_relabel (partition : SheetPartition degree)
    (permutation : Equiv.Perm (Fin degree)) :
    (partition.relabel permutation).relabel permutation.symm = partition := by
  rw [SheetPartition.relabel_relabel, Equiv.self_trans_symm, relabel_refl]


/-! ### Endpoints, indices, and the two source graphs -/

theorem sourceEndpoint_map (iso : DatumIso first second) (vertex : target₁.V)
    (sheet : Fin degree) :
    second.sourceEndpoint (iso.targetVertex vertex) (iso.vertexPerm vertex sheet) =
      iso.sourceVertexEquiv (first.sourceEndpoint vertex sheet) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · show (second.vertexPartition (iso.targetVertex vertex)).repr
      (iso.vertexPerm vertex sheet) =
      iso.vertexPerm vertex ((first.vertexPartition vertex).repr sheet)
    rw [iso.vertexPartition vertex]
    simp [SheetPartition.relabel]

/-- **The transport is a map of quotient-source graphs**: the two endpoints of a
transported occurrence are the transported endpoints, in the same order. -/
theorem sourceEnds_map (iso : DatumIso first second) (edge : first.SourceEdge) :
    second.sourceEnds (iso.sourceEdgeEquiv edge) =
      (iso.sourceVertexEquiv (first.sourceEnds edge).1,
        iso.sourceVertexEquiv (first.sourceEnds edge).2) := by
  have hFst : second.sourceEndpoint
      ((iso.targetEdge edge.1.1 : target₂.V × target₂.V)).1
      (iso.edgePerm edge.1.1 edge.1.2) =
      iso.sourceVertexEquiv (first.sourceEnds edge).1 := by
    rw [iso.ends_fst edge.1.1]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show (second.vertexPartition
        (iso.targetVertex ((edge.1.1 : target₁.V × target₁.V)).1)).repr
        (iso.edgePerm edge.1.1 edge.1.2) =
        iso.vertexPerm ((edge.1.1 : target₁.V × target₁.V)).1
          ((first.vertexPartition ((edge.1.1 : target₁.V × target₁.V)).1).repr edge.1.2)
      rw [iso.vertexPartition]
      show iso.vertexPerm ((edge.1.1 : target₁.V × target₁.V)).1
          ((first.vertexPartition ((edge.1.1 : target₁.V × target₁.V)).1).repr
            ((iso.vertexPerm ((edge.1.1 : target₁.V × target₁.V)).1).symm
              (iso.edgePerm edge.1.1 edge.1.2))) = _
      exact congrArg _ (iso.compatible_fst edge.1.1 edge.1.2)
  have hSnd : second.sourceEndpoint
      ((iso.targetEdge edge.1.1 : target₂.V × target₂.V)).2
      (iso.edgePerm edge.1.1 edge.1.2) =
      iso.sourceVertexEquiv (first.sourceEnds edge).2 := by
    rw [iso.ends_snd edge.1.1]
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · show (second.vertexPartition
        (iso.targetVertex ((edge.1.1 : target₁.V × target₁.V)).2)).repr
        (iso.edgePerm edge.1.1 edge.1.2) =
        iso.vertexPerm ((edge.1.1 : target₁.V × target₁.V)).2
          ((first.vertexPartition ((edge.1.1 : target₁.V × target₁.V)).2).repr edge.1.2)
      rw [iso.vertexPartition]
      show iso.vertexPerm ((edge.1.1 : target₁.V × target₁.V)).2
          ((first.vertexPartition ((edge.1.1 : target₁.V × target₁.V)).2).repr
            ((iso.vertexPerm ((edge.1.1 : target₁.V × target₁.V)).2).symm
              (iso.edgePerm edge.1.1 edge.1.2))) = _
      exact congrArg _ (iso.compatible_snd edge.1.1 edge.1.2)
  exact Prod.ext hFst hSnd

/-- Dilation indices are preserved. -/
theorem sourceEdgeIndex_map (iso : DatumIso first second) (edge : first.SourceEdge) :
    second.sourceEdgeIndex (iso.sourceEdgeEquiv edge) = first.sourceEdgeIndex edge := by
  show (second.edgePartition (iso.targetEdge edge.1.1)).blockCard
    (iso.edgePerm edge.1.1 edge.1.2) = _
  rw [iso.edgePartition edge.1.1]
  exact (first.edgePartition edge.1.1).relabel_blockCard (iso.edgePerm edge.1.1) edge.1.2

/-- Incidence in the quotient source is preserved. -/
theorem incident_map_iff (iso : DatumIso first second) (edge : first.SourceEdge)
    (vertex : first.SourceVertex) :
    Incident second (iso.sourceEdgeEquiv edge) (iso.sourceVertexEquiv vertex) ↔
      Incident first edge vertex := by
  unfold Incident
  rw [iso.sourceEnds_map edge]
  simp only [Equiv.apply_eq_iff_eq]

/-- Every quotient-source edge multiplicity is preserved. -/
theorem num_edges_map (iso : DatumIso first second)
    (left right : first.SourceVertex) :
    num_edges second.sourceGraph (iso.sourceVertexEquiv left)
        (iso.sourceVertexEquiv right) =
      num_edges first.sourceGraph left right := by
  rw [GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum,
    GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum]
  symm
  apply Fintype.sum_equiv iso.sourceEdgeEquiv
  intro edge
  rw [iso.sourceEnds_map edge]
  simp [Prod.ext_iff]

/-- The transport is an adjacency-preserving equivalence of quotient sources. -/
def sourceGraphLaplacianEquiv (iso : DatumIso first second) :
    LaplacianEquiv first.sourceGraph second.sourceGraph where
  toEquiv := iso.sourceVertexEquiv
  num_edges_eq := iso.num_edges_map

theorem connected (iso : DatumIso first second) (hConnected : first.Connected) :
    second.Connected :=
  iso.sourceGraphLaplacianEquiv.graphConnected hConnected

/-! ### `DatumIso` is an equivalence relation -/

/-- The identity isomorphism. -/
def refl (data : GluingDatum target₁ degree) : DatumIso data data where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends_fst _ := rfl
  ends_snd _ := rfl
  vertexPerm _ := Equiv.refl _
  edgePerm _ := Equiv.refl _
  vertexPartition _ := (relabel_refl _).symm
  edgePartition _ := (relabel_refl _).symm
  compatible_fst _ _ := rfl
  compatible_snd _ _ := rfl

/-- The inverse isomorphism. -/
def symm (iso : DatumIso first second) : DatumIso second first where
  targetVertex := iso.targetVertex.symm
  targetEdge := iso.targetEdge.symm
  ends_fst edge := by
    have hEnds := iso.ends_fst (iso.targetEdge.symm edge)
    rw [Equiv.apply_symm_apply] at hEnds
    rw [hEnds, Equiv.symm_apply_apply]
  ends_snd edge := by
    have hEnds := iso.ends_snd (iso.targetEdge.symm edge)
    rw [Equiv.apply_symm_apply] at hEnds
    rw [hEnds, Equiv.symm_apply_apply]
  vertexPerm vertex := (iso.vertexPerm (iso.targetVertex.symm vertex)).symm
  edgePerm edge := (iso.edgePerm (iso.targetEdge.symm edge)).symm
  vertexPartition vertex := by
    have hForward := iso.vertexPartition (iso.targetVertex.symm vertex)
    rw [Equiv.apply_symm_apply] at hForward
    rw [hForward, relabel_symm_relabel]
  edgePartition edge := by
    have hForward := iso.edgePartition (iso.targetEdge.symm edge)
    rw [Equiv.apply_symm_apply] at hForward
    rw [hForward, relabel_symm_relabel]
  compatible_fst edge sheet := by
    set old := iso.targetEdge.symm edge with hOld
    have hEnds : ((edge : target₂.V × target₂.V)).1 =
        iso.targetVertex ((old : target₁.V × target₁.V)).1 := by
      have := iso.ends_fst old
      rwa [hOld, Equiv.apply_symm_apply] at this
    have hBase := iso.compatible_fst old ((iso.edgePerm old).symm sheet)
    rw [Equiv.apply_symm_apply] at hBase
    have hGoal := ((first.vertexPartition ((old : target₁.V × target₁.V)).1).relabel_rel_iff
      (iso.vertexPerm ((old : target₁.V × target₁.V)).1)
      ((iso.edgePerm old).symm sheet)
      ((iso.vertexPerm ((old : target₁.V × target₁.V)).1).symm sheet)).mpr hBase.symm
    rw [Equiv.apply_symm_apply] at hGoal
    rw [hEnds, iso.vertexPartition]
    simp only [Equiv.symm_apply_apply, Equiv.symm_symm]
    exact hGoal
  compatible_snd edge sheet := by
    set old := iso.targetEdge.symm edge with hOld
    have hEnds : ((edge : target₂.V × target₂.V)).2 =
        iso.targetVertex ((old : target₁.V × target₁.V)).2 := by
      have := iso.ends_snd old
      rwa [hOld, Equiv.apply_symm_apply] at this
    have hBase := iso.compatible_snd old ((iso.edgePerm old).symm sheet)
    rw [Equiv.apply_symm_apply] at hBase
    have hGoal := ((first.vertexPartition ((old : target₁.V × target₁.V)).2).relabel_rel_iff
      (iso.vertexPerm ((old : target₁.V × target₁.V)).2)
      ((iso.edgePerm old).symm sheet)
      ((iso.vertexPerm ((old : target₁.V × target₁.V)).2).symm sheet)).mpr hBase.symm
    rw [Equiv.apply_symm_apply] at hGoal
    rw [hEnds, iso.vertexPartition]
    simp only [Equiv.symm_apply_apply, Equiv.symm_symm]
    exact hGoal

/-- Isomorphisms of gluing data compose. -/
def trans (left : DatumIso first second) (right : DatumIso second third) :
    DatumIso first third where
  targetVertex := left.targetVertex.trans right.targetVertex
  targetEdge := left.targetEdge.trans right.targetEdge
  ends_fst edge := by
    rw [Equiv.trans_apply, right.ends_fst, left.ends_fst, Equiv.trans_apply]
  ends_snd edge := by
    rw [Equiv.trans_apply, right.ends_snd, left.ends_snd, Equiv.trans_apply]
  vertexPerm vertex := (left.vertexPerm vertex).trans
    (right.vertexPerm (left.targetVertex vertex))
  edgePerm edge := (left.edgePerm edge).trans (right.edgePerm (left.targetEdge edge))
  vertexPartition vertex := by
    rw [Equiv.trans_apply, right.vertexPartition, left.vertexPartition,
      SheetPartition.relabel_relabel]
  edgePartition edge := by
    rw [Equiv.trans_apply, right.edgePartition, left.edgePartition,
      SheetPartition.relabel_relabel]
  compatible_fst edge sheet := by
    have hRight := right.compatible_fst (left.targetEdge edge) (left.edgePerm edge sheet)
    rw [left.ends_fst edge, left.vertexPartition] at hRight
    have hPulled := ((first.vertexPartition ((edge : target₁.V × target₁.V)).1).relabel_rel_iff
        (left.vertexPerm ((edge : target₁.V × target₁.V)).1)
        ((left.vertexPerm ((edge : target₁.V × target₁.V)).1).symm
          ((right.vertexPerm (left.targetVertex ((edge : target₁.V × target₁.V)).1)).symm
            (right.edgePerm (left.targetEdge edge) (left.edgePerm edge sheet))))
        ((left.vertexPerm ((edge : target₁.V × target₁.V)).1).symm
          (left.edgePerm edge sheet))).mp (by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hRight)
    exact hPulled.trans (left.compatible_fst edge sheet)
  compatible_snd edge sheet := by
    have hRight := right.compatible_snd (left.targetEdge edge) (left.edgePerm edge sheet)
    rw [left.ends_snd edge, left.vertexPartition] at hRight
    have hPulled := ((first.vertexPartition ((edge : target₁.V × target₁.V)).2).relabel_rel_iff
        (left.vertexPerm ((edge : target₁.V × target₁.V)).2)
        ((left.vertexPerm ((edge : target₁.V × target₁.V)).2).symm
          ((right.vertexPerm (left.targetVertex ((edge : target₁.V × target₁.V)).2)).symm
            (right.edgePerm (left.targetEdge edge) (left.edgePerm edge sheet))))
        ((left.vertexPerm ((edge : target₁.V × target₁.V)).2).symm
          (left.edgePerm edge sheet))).mp (by
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact hRight)
    exact hPulled.trans (left.compatible_snd edge sheet)

/-! ### Pruning, stable paths and the induced incidence dictionary -/

/-- Dangling occurrences correspond to dangling occurrences. -/
theorem isDangling_map_iff (iso : DatumIso first second) (hConnected : first.Connected)
    (edge : first.SourceEdge) :
    IsDangling second (iso.sourceEdgeEquiv edge) ↔ IsDangling first edge := by
  constructor
  · intro hDangling
    refine SheetRelabelPruning.isDangling_map first
      iso.sourceGraphLaplacianEquiv.symm hConnected (iso.sourceEdgeEquiv edge) edge ?_ hDangling
    rw [iso.sourceEnds_map edge]
    show first.sourceEnds edge =
      (iso.sourceVertexEquiv.symm (iso.sourceVertexEquiv (first.sourceEnds edge).1),
        iso.sourceVertexEquiv.symm (iso.sourceVertexEquiv (first.sourceEnds edge).2))
    simp only [Equiv.symm_apply_apply]
  · exact SheetRelabelPruning.isDangling_map second iso.sourceGraphLaplacianEquiv
      (iso.connected hConnected) edge (iso.sourceEdgeEquiv edge) (iso.sourceEnds_map edge)

/-- Surviving occurrences correspond. -/
noncomputable def nonDanglingEdgeEquiv (iso : DatumIso first second)
    (hConnected : first.Connected) :
    NonDanglingEdge first ≃ NonDanglingEdge second :=
  iso.sourceEdgeEquiv.subtypeEquiv fun edge ↦
    not_congr (iso.isDangling_map_iff hConnected edge).symm

@[simp] theorem nonDanglingEdgeEquiv_val (iso : DatumIso first second)
    (hConnected : first.Connected) (edge : NonDanglingEdge first) :
    (iso.nonDanglingEdgeEquiv hConnected edge).1 = iso.sourceEdgeEquiv edge.1 := rfl

theorem nonDanglingIncident_map (iso : DatumIso first second)
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
theorem nonDanglingValency_map (iso : DatumIso first second)
    (hConnected : first.Connected) (vertex : first.SourceVertex) :
    nonDanglingValency second (iso.sourceVertexEquiv vertex) =
      nonDanglingValency first vertex := by
  rw [← card_nonDanglingIncident, iso.nonDanglingIncident_map hConnected,
    Finset.card_image_of_injective _ iso.sourceEdgeEquiv.injective,
    card_nonDanglingIncident]

/-- Consecutive occurrences correspond to consecutive occurrences. -/
theorem consecutive_map_iff (iso : DatumIso first second)
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
noncomputable def stablePathEquiv (iso : DatumIso first second)
    (hConnected : first.Connected) : StablePath first ≃ StablePath second :=
  Quot.congr (iso.nonDanglingEdgeEquiv hConnected)
    fun left right ↦ (iso.consecutive_map_iff hConnected left right).symm

theorem stablePathEquiv_mk (iso : DatumIso first second)
    (hConnected : first.Connected) (edge : NonDanglingEdge first) :
    iso.stablePathEquiv hConnected edge.stablePath =
      (iso.nonDanglingEdgeEquiv hConnected edge).stablePath := rfl

theorem danglingEdgeNoGlue_map (iso : DatumIso first second)
    (hConnected : first.Connected) (hNoGlue : DanglingEdgeNoGlue first) :
    DanglingEdgeNoGlue second := by
  intro edge hDangling
  obtain ⟨edge, rfl⟩ := iso.sourceEdgeEquiv.surjective edge
  rw [iso.sourceEdgeIndex_map]
  exact hNoGlue edge ((iso.isDangling_map_iff hConnected edge).mp hDangling)

/-- Row-filtered occurrence sets correspond. -/
theorem occurrences_map (iso : DatumIso first second) (hConnected : first.Connected)
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
theorem matrix_map (iso : DatumIso first second) (hConnected : first.Connected)
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
noncomputable def branchVertexEquiv (iso : DatumIso first second)
    (hConnected : first.Connected) :
    StableGraphIncidence.BranchVertex first ≃ StableGraphIncidence.BranchVertex second :=
  iso.sourceVertexEquiv.subtypeEquiv fun vertex ↦ by
    rw [iso.nonDanglingValency_map hConnected]

/-- **Every incidence multiplicity is preserved**, counted with flags, so a
stable loop keeps its two incidences at one branch vertex. -/
theorem incidenceCount_map (iso : DatumIso first second) (hConnected : first.Connected)
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

/-- **The stable dictionary the fibre's isomorphisms carry as data is now
constructed** from the isomorphism of gluing data. -/
noncomputable def graphEquivalence (iso : DatumIso first second)
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
    (DatumIso.refl data).branchVertexEquiv hConnected =
      Equiv.refl (StableGraphIncidence.BranchVertex data) :=
  Equiv.ext fun _ ↦ rfl

theorem stablePathEquiv_refl (data : GluingDatum target₁ degree)
    (hConnected : data.Connected) :
    (DatumIso.refl data).stablePathEquiv hConnected = Equiv.refl (StablePath data) := by
  refine Equiv.ext ?_
  refine Quot.ind ?_
  intro _
  rfl

theorem branchVertexEquiv_symm (iso : DatumIso first second)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    iso.symm.branchVertexEquiv hSecond = (iso.branchVertexEquiv hFirst).symm :=
  Equiv.ext fun _ ↦ rfl

theorem stablePathEquiv_symm (iso : DatumIso first second)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    iso.symm.stablePathEquiv hSecond = (iso.stablePathEquiv hFirst).symm := by
  refine Equiv.ext ?_
  refine Quot.ind ?_
  intro _
  rfl

theorem branchVertexEquiv_trans (left : DatumIso first second)
    (right : DatumIso second third)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    (left.trans right).branchVertexEquiv hFirst =
      (left.branchVertexEquiv hFirst).trans (right.branchVertexEquiv hSecond) :=
  Equiv.ext fun _ ↦ rfl

theorem stablePathEquiv_trans (left : DatumIso first second)
    (right : DatumIso second third)
    (hFirst : first.Connected) (hSecond : second.Connected) :
    (left.trans right).stablePathEquiv hFirst =
      (left.stablePathEquiv hFirst).trans (right.stablePathEquiv hSecond) := by
  refine Equiv.ext ?_
  refine Quot.ind ?_
  intro _
  rfl

theorem hasPathEnds_map (iso : DatumIso first second) (hConnected : first.Connected)
    (hEnds : HasPathEnds first) : HasPathEnds second :=
  (iso.graphEquivalence hConnected).hasPathEnds hConnected hEnds

/-- Trivalence of the stable graph is preserved. -/
theorem trivalent_map (iso : DatumIso first second) (hConnected : first.Connected)
    (hTrivalent : ∀ vertex : first.SourceVertex, nonDanglingValency first vertex ≤ 3)
    (vertex : second.SourceVertex) : nonDanglingValency second vertex ≤ 3 := by
  obtain ⟨vertex, rfl⟩ := iso.sourceVertexEquiv.surjective vertex
  rw [iso.nonDanglingValency_map hConnected]
  exact hTrivalent vertex

/-! ### The target, its leaves, and validity -/

theorem mem_incidentEdges_map (iso : DatumIso first second) (vertex : target₁.V)
    (edge : target₁.edges) :
    iso.targetEdge edge ∈ GluingDatum.incidentEdges (iso.targetVertex vertex) ↔
      edge ∈ GluingDatum.incidentEdges vertex := by
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and,
    iso.ends_fst, iso.ends_snd, EmbeddingLike.apply_eq_iff_eq]

theorem incidentEdges_card_map (iso : DatumIso first second) (vertex : target₁.V) :
    (GluingDatum.incidentEdges (iso.targetVertex vertex)).card =
      (GluingDatum.incidentEdges vertex).card := by
  refine (Finset.card_bij (fun edge _ ↦ iso.targetEdge edge) ?_ ?_ ?_).symm
  · exact fun edge hEdge ↦ (iso.mem_incidentEdges_map vertex edge).mpr hEdge
  · exact fun _ _ _ _ h ↦ iso.targetEdge.injective h
  · intro edge hEdge
    refine ⟨iso.targetEdge.symm edge, ?_, iso.targetEdge.apply_symm_apply edge⟩
    refine (iso.mem_incidentEdges_map vertex _).mp ?_
    rwa [Equiv.apply_symm_apply]

/-- Every target edge multiplicity is preserved. -/
theorem targetNumEdges_map (iso : DatumIso first second) (left right : target₁.V) :
    num_edges target₂ (iso.targetVertex left) (iso.targetVertex right) =
      num_edges target₁ left right := by
  rw [← GluingTransport.card_edgeKey_fiber target₂ (iso.targetVertex left)
      (iso.targetVertex right),
    ← GluingTransport.card_edgeKey_fiber target₁ left right]
  refine Fintype.card_congr (Equiv.subtypeEquiv iso.targetEdge ?_).symm
  intro edge
  rw [GluingTransport.edgeKey, GluingTransport.edgeKey, iso.ends_fst, iso.ends_snd]
  simp [Prod.ext_iff]

/-- The target relabelling is an adjacency-preserving vertex equivalence. -/
def targetLaplacianEquiv (iso : DatumIso first second) :
    LaplacianEquiv target₁ target₂ where
  toEquiv := iso.targetVertex
  num_edges_eq := iso.targetNumEdges_map

theorem targetConnected_map (iso : DatumIso first second)
    (hConnected : graph_connected target₁) : graph_connected target₂ :=
  iso.targetLaplacianEquiv.graphConnected hConnected

theorem targetEdgeCard_map (iso : DatumIso first second) :
    Multiset.card target₂.edges = Multiset.card target₁.edges := by
  rw [← Multiset.card_coe target₂.edges, ← Multiset.card_coe target₁.edges]
  exact Fintype.card_congr iso.targetEdge.symm

theorem targetGenus_map (iso : DatumIso first second) : genus target₂ = genus target₁ := by
  unfold genus
  rw [iso.targetEdgeCard_map, Fintype.card_congr iso.targetVertex]

theorem genus_sourceGraph (data : GluingDatum target₁ degree) :
    genus data.sourceGraph =
      (Fintype.card data.SourceEdge : ℤ) - (Fintype.card data.SourceVertex : ℤ) + 1 := by
  unfold genus
  have hEdges : Multiset.card data.sourceGraph.edges = Fintype.card data.SourceEdge := by
    show Multiset.card
      ((Finset.univ : Finset data.SourceEdge).val.map data.sourceEnds) = _
    rw [Multiset.card_map]
    rfl
  rw [hEdges]
  congr 2

theorem sourceGenus_map (iso : DatumIso first second) :
    genus second.sourceGraph = genus first.sourceGraph := by
  rw [genus_sourceGraph, genus_sourceGraph,
    Fintype.card_congr iso.sourceEdgeEquiv.symm,
    Fintype.card_congr iso.sourceVertexEquiv.symm]

/-- Refinement counts are preserved at an incident target vertex. -/
theorem blockCountWithin_map (iso : DatumIso first second) (vertex : target₁.V)
    (edge : target₁.edges) (hIncident : edge ∈ GluingDatum.incidentEdges vertex)
    (sheet : Fin degree) :
    (second.edgePartition (iso.targetEdge edge)).blockCountWithin
        (second.vertexPartition (iso.targetVertex vertex)) (iso.vertexPerm vertex sheet) =
      (first.edgePartition edge).blockCountWithin (first.vertexPartition vertex) sheet := by
  classical
  have hPoint : ∀ item : Fin degree,
      (first.vertexPartition vertex).Rel
        ((iso.edgePerm edge).trans (iso.vertexPerm vertex).symm item) item := by
    have hEnd := (Finset.mem_filter.mp hIncident).2
    rcases hEnd with hFst | hSnd
    · intro item
      have hCompatible := iso.compatible_fst edge item
      rw [hFst] at hCompatible
      exact hCompatible
    · intro item
      have hCompatible := iso.compatible_snd edge item
      rw [hSnd] at hCompatible
      exact hCompatible
  have hSplit : (first.edgePartition edge).relabel (iso.edgePerm edge) =
      ((first.edgePartition edge).relabel
        ((iso.edgePerm edge).trans (iso.vertexPerm vertex).symm)).relabel
          (iso.vertexPerm vertex) := by
    rw [SheetPartition.relabel_relabel]
    congr 1
    ext item
    simp
  rw [iso.edgePartition edge, iso.vertexPartition vertex, hSplit,
    SheetPartition.relabel_blockCountWithin,
    SheetPartition.relabel_blockCountWithin_fixed_of_pointwise _ _ _ hPoint]

/-- The local Riemann--Hurwitz inequalities transport. -/
theorem riemannHurwitz_map (iso : DatumIso first second)
    (hRiemannHurwitz : first.RiemannHurwitz) : second.RiemannHurwitz := by
  classical
  intro vertex sheet
  obtain ⟨vertex, rfl⟩ := iso.targetVertex.surjective vertex
  obtain ⟨sheet, rfl⟩ := (iso.vertexPerm vertex).surjective sheet
  have hBase := hRiemannHurwitz vertex sheet
  have hSum : (∑ edge ∈ GluingDatum.incidentEdges (iso.targetVertex vertex),
      ((second.edgePartition edge).blockCountWithin
        (second.vertexPartition (iso.targetVertex vertex))
          (iso.vertexPerm vertex sheet) : ℤ)) =
      ∑ edge ∈ GluingDatum.incidentEdges vertex,
        ((first.edgePartition edge).blockCountWithin
          (first.vertexPartition vertex) sheet : ℤ) := by
    refine (Finset.sum_bij (fun edge _ ↦ iso.targetEdge edge) ?_ ?_ ?_ ?_).symm
    · exact fun edge hEdge ↦ (iso.mem_incidentEdges_map vertex edge).mpr hEdge
    · exact fun _ _ _ _ h ↦ iso.targetEdge.injective h
    · intro edge hEdge
      refine ⟨iso.targetEdge.symm edge, ?_, iso.targetEdge.apply_symm_apply edge⟩
      refine (iso.mem_incidentEdges_map vertex _).mp ?_
      rwa [Equiv.apply_symm_apply]
    · intro edge hEdge
      rw [iso.blockCountWithin_map vertex edge hEdge sheet]
  have hCard := iso.incidentEdges_card_map vertex
  have hBlock : (second.vertexPartition (iso.targetVertex vertex)).blockCard
      (iso.vertexPerm vertex sheet) =
      (first.vertexPartition vertex).blockCard sheet := by
    rw [iso.vertexPartition vertex, SheetPartition.relabel_blockCard]
  change (∑ edge ∈ GluingDatum.incidentEdges (iso.targetVertex vertex),
      ((second.edgePartition edge).blockCountWithin
        (second.vertexPartition (iso.targetVertex vertex))
          (iso.vertexPerm vertex sheet) : ℤ)) - 2 ≥
    ((second.vertexPartition (iso.targetVertex vertex)).blockCard
      (iso.vertexPerm vertex sheet) : ℤ) *
      (((GluingDatum.incidentEdges (iso.targetVertex vertex)).card : ℤ) - 2)
  rw [hSum, hCard, hBlock]
  exact hBase

theorem valid_map (iso : DatumIso first second) (hValid : first.Valid) : second.Valid :=
  ⟨iso.connected hValid.1, iso.riemannHurwitz_map hValid.2⟩

/-! ### Inhabitants: sheet relabellings, and a non-identity witness -/

/-- Every compatible sheet relabelling of a datum is an isomorphism onto the
relabelled datum. -/
def ofSheetRelabeling {data : GluingDatum target₁ degree}
    (relabeling : data.SheetRelabeling) : DatumIso data relabeling.apply where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends_fst _ := rfl
  ends_snd _ := rfl
  vertexPerm := relabeling.vertexPermutation
  edgePerm := relabeling.edgePermutation
  vertexPartition _ := rfl
  edgePartition _ := rfl
  compatible_fst := relabeling.compatible_left
  compatible_snd := relabeling.compatible_right

/-- One sheet permutation used at every target vertex and every target edge
occurrence is always compatible: the relative permutation is the identity. -/
def globalRelabeling (data : GluingDatum target₁ degree)
    (permutation : Equiv.Perm (Fin degree)) : data.SheetRelabeling where
  vertexPermutation _ := permutation
  edgePermutation _ := permutation
  compatible_left _ sheet := by
    rw [Equiv.symm_apply_apply]
    exact rfl
  compatible_right _ sheet := by
    rw [Equiv.symm_apply_apply]
    exact rfl

/-- The datum obtained by relabelling every sheet by one permutation. -/
def globalRelabelDatum (data : GluingDatum target₁ degree)
    (permutation : Equiv.Perm (Fin degree)) : GluingDatum target₁ degree :=
  (globalRelabeling data permutation).apply

@[simp] theorem globalRelabelDatum_vertexPartition (data : GluingDatum target₁ degree)
    (permutation : Equiv.Perm (Fin degree)) (vertex : target₁.V) :
    (globalRelabelDatum data permutation).vertexPartition vertex =
      (data.vertexPartition vertex).relabel permutation := rfl

/-- **The global sheet isomorphism.** -/
def ofGlobalPerm (data : GluingDatum target₁ degree)
    (permutation : Equiv.Perm (Fin degree)) :
    DatumIso data (globalRelabelDatum data permutation) :=
  ofSheetRelabeling (globalRelabeling data permutation)

@[simp] theorem ofGlobalPerm_vertexPerm (data : GluingDatum target₁ degree)
    (permutation : Equiv.Perm (Fin degree)) (vertex : target₁.V) :
    (ofGlobalPerm data permutation).vertexPerm vertex = permutation := rfl

/-- Its induced source-vertex map moves the sheet coordinate by `permutation`:
the transport is not a map that only ever fires on the identity. -/
@[simp] theorem ofGlobalPerm_sourceVertexEquiv_sheet (data : GluingDatum target₁ degree)
    (permutation : Equiv.Perm (Fin degree)) (vertex : data.SourceVertex) :
    ((ofGlobalPerm data permutation).sourceVertexEquiv vertex).1.2 =
      permutation vertex.1.2 := rfl

end DatumIso

/-! ### The non-identity witness: the caterpillar of loops with a sheet swap -/

namespace Witness

open DraismaVargas.Infrastructure.CaterpillarTree
open DraismaVargas.LocalCases.CaterpillarDatum

theorem zero_ne_one (m : ℕ) : (0 : Fin (m + 2)) ≠ 1 := by
  intro hEq
  have hVal := congrArg Fin.val hEq
  rw [Fin.val_zero, Fin.val_one] at hVal
  exact absurd hVal (by omega)

/-- **The swap of sheets `0` and `1` really moves the pair partition.** -/
theorem pairPart_relabel_swap_ne (m j : ℕ) (hj : 1 ≤ j) (hjlt : j < m + 2) :
    (pairPart m j).relabel (Equiv.swap (0 : Fin (m + 2)) 1) ≠ pairPart m j := by
  intro hEq
  have hApplyAt : ∀ sheet : Fin (m + 2),
      (Equiv.swap (0 : Fin (m + 2)) 1)
          ((pairPart m j).repr ((Equiv.swap (0 : Fin (m + 2)) 1) sheet)) =
        (pairPart m j).repr sheet := by
    intro sheet
    have hApply := congrArg (fun partition : SheetPartition (m + 2) ↦
      partition.repr sheet) hEq
    simp only [SheetPartition.relabel, Equiv.symm_swap] at hApply
    exact hApply
  by_cases hOne : j = 1
  · subst hOne
    have hStep := hApplyAt 0
    rw [Equiv.swap_apply_left, pairPart_repr, if_pos (by simp), Equiv.swap_apply_left,
      pairPart_repr, if_neg (by simp)] at hStep
    exact zero_ne_one m hStep.symm
  · have hTwo : 2 ≤ j := by omega
    have hNeZero : (⟨j, hjlt⟩ : Fin (m + 2)) ≠ 0 := by
      intro hZero
      have hVal := congrArg Fin.val hZero
      rw [Fin.val_zero] at hVal
      change j = 0 at hVal
      omega
    have hNeOne : (⟨j, hjlt⟩ : Fin (m + 2)) ≠ 1 := by
      intro hOne'
      have hVal := congrArg Fin.val hOne'
      rw [Fin.val_one] at hVal
      change j = 1 at hVal
      omega
    have hStep := hApplyAt ⟨j, hjlt⟩
    rw [Equiv.swap_apply_of_ne_of_ne hNeZero hNeOne, pairPart_repr, if_pos rfl,
      Equiv.swap_apply_left] at hStep
    exact zero_ne_one m hStep.symm

/-- **The witness**: the caterpillar-of-loops datum of every even genus,
relabelled by the transposition of sheets `0` and `1`. -/
def catSheetIso (m : ℕ) :
    DatumIso (caterpillarDatum m)
      (DatumIso.globalRelabelDatum (caterpillarDatum m)
        (Equiv.swap (0 : Fin (m + 2)) 1)) :=
  DatumIso.ofGlobalPerm (caterpillarDatum m) (Equiv.swap (0 : Fin (m + 2)) 1)

theorem catSheetIso_vertexPerm (m : ℕ) (vertex : (catTree m).V) :
    (catSheetIso m).vertexPerm vertex = Equiv.swap (0 : Fin (m + 2)) 1 := rfl

/-- Its sheet permutation is not the identity. -/
theorem catSheetIso_vertexPerm_ne (m : ℕ) (vertex : (catTree m).V) :
    (catSheetIso m).vertexPerm vertex ≠ Equiv.refl (Fin (m + 2)) := by
  rw [catSheetIso_vertexPerm]
  intro hEq
  have hStep := Equiv.ext_iff.mp hEq 0
  rw [Equiv.swap_apply_left, Equiv.refl_apply] at hStep
  exact zero_ne_one m hStep.symm

/-- **It is not an isomorphism of a datum with itself**: the relabelled datum
is a different gluing datum. -/
theorem catSheetIso_ne (m : ℕ) :
    DatumIso.globalRelabelDatum (caterpillarDatum m)
        (Equiv.swap (0 : Fin (m + 2)) 1) ≠ caterpillarDatum m := by
  intro hEq
  have hField := congrArg (fun data : GluingDatum (catTree m) (m + 2) ↦
    data.vertexPartition (vtx m 0 (by omega))) hEq
  simp only [DatumIso.globalRelabelDatum_vertexPartition,
    caterpillarDatum_vertexPartition, catVertexPart] at hField
  exact pairPart_relabel_swap_ne m (pairIndex (vtx m 0 (by omega)).val)
    (pairIndex_pos _) (pairIndex_lt m _ (by omega)) hField

end Witness

namespace DatumIso

variable {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}
end DatumIso

end DraismaVargas.Count.Transport
