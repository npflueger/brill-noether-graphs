import DraismaVargasCount.ResolutionExpansion
import DraismaVargasCount.W4WallExhaustion
import DraismaVargasCount.MergePinning
import DraismaVargas.LocalCases.M11IncomingOuterPartitions
import DraismaVargas.LocalCases.SecondEquation

/-!
# Exhaustion of the labelled geometric star at a divalent `w2-r2-nd3-M-11` wall

Source: Draisma--Vargas Part I (arXiv:1909.12924), Figure 32 (the three M-11 local
resolutions of Case `{w2-r2-nd3-M-11}`), and Vargas, Part II (arXiv:2609.09109), the star
of a codimension-one wall.

This is the `w2M11` counterpart of `Count.W4WallExhaustion`, laid out section by
section against that file so the two can be compared.  Three things differ.

## 1.  Discreteness is unavailable, and provably so

`W4WallExhaustion.vertexPartition_ne_discrete_of_card_ne_four` says that at a
codimension-one wall discreteness of the merged sheet partition *forces*
valency four.  A divalent wall therefore never has one
(`vertexPartition_ne_discrete`), so the whole `Count.DiscreteW4Normalization`
route -- "the local partitions are forced, hence the member's datum is the
uniform expansion" -- is unavailable here, not merely unproved.

What replaces it is `Count.ResolutionExpansion`: an arbitrary regrowth's datum
is the expansion at the local resolution **read off its own endpoint
partitions**.  Section 1 proves that (`transported_eq_resolutionDatum`,
`datumIso`, `sourceVertexMap_datumIso`, `retainedSourceEdge_datumIso`), and it
is unconditional: no valency hypothesis, no discreteness, no family, no choice
of figure.  In the discrete four-valent case the resolution it reads off is the
joined one and the statement specializes to
`DiscreteW4Normalization.normalized_eq`.

## 2.  The index is `(placement, resolution)`, and the placement factor is `Bool`

At `w4` the index is the three `2+2` pairings of four occurrences.  At a
divalent wall the two incident occurrences admit exactly two *unordered*
splits -- both on one side, or one each -- and section 2 proves that an
arbitrary regrowth realizes one of the two after the normalizing endpoint
transposition (`exists_side`, `side`, `side_placement`).  That is the `Bool`
factor, proved, and it is the divalent analogue of
`LocalCases.W4IncomingTargetNormalization.pairing`.

The second factor, the local resolution, is **not** a fixed finite set:
`ResolutionM11.splitResolutionAt` carries a distinguished block, so what a wall
presents is a pair and not a numeral.  Computer censuses (not part of this library) find
M-11 walls with two labelled classes and M-11 walls with three, so no numeral is correct
for the family.  Hence the headline is a bijection onto a supplied index type
(`starEquiv`, `card_eq_of_index`) rather than `Fintype.card … = 3`.

## 3.  Merge pinning is derived; endpoint sheet rigidity is a hypothesis

* `Pinned` is derived: `pinned_of_isWall` gets it from `Count.MergePinning.map_merge`,
  which pins the merged vertex at every valency from the nonvanishing dimension
  correction alone, and `pinned_of_targetExcess_eq_one` derives it from equation (C).
* `ResolutionExpansion.Transport.endpoint_compatible` is a hypothesis here, and it has no
  `w4` counterpart.  A `GeometricDatumIso` promises that its occurrence
  permutation agrees with its vertex permutation modulo the blocks of the
  *base* wall partition; the expanded datum needs agreement modulo the blocks of
  `resolution.left` / `resolution.right`, which at a non-joined resolution are
  strictly finer.  At the joined resolution the two coincide
  (`ResolutionExpansion.uniformTransport`), which is exactly why
  `Count.GeometricUniformExpansion.lift` needed no such field.  **Every**
  non-`w4` family meets this obligation, not just M-11.
  `Count.ResolutionExpansionFree` replaces `Transport` by a form with decoupled endpoint
  permutations, and `M11StarExhaustionProof` proves exhaustion at M-11 walls through it.

## What is proved

* §0 `vertexPartition_ne_discrete` -- the scope statement.
* §1 `transported_eq_resolutionDatum`, `datumIso`, `datumIso_occurrence`,
  `contractVertex_targetIso`, `sourceVertexMap_datumIso`,
  `retainedSourceEdge_datumIso` -- the resolution-expansion normalization of an
  arbitrary regrowth, and the two source dictionaries it induces.
  Unconditional.
* §2 `exists_side`, `side`, `side_placement` -- the two-element placement
  census at a divalent wall, from `SecondEquation.valencySplit_of_twoStar`.
* §3 `pullbackTwoStar`, `pullbackTwoStar_edge`.
* §4 `Candidate`, `candDatumIso`, `Candidate.datumIso`, `Candidate.starMember`,
  `Candidate.oldCompatible`, `Candidate.data_eq`,
  `Candidate.member_contractSourceVertex`, `Candidate.member_edgeEmbedding_val`.
* §5 `pinned_of_isWall`, `pinned_of_targetExcess_eq_one`,
  `member_card_incidentEdges`, `inheritedStar`, `memberSide`,
  `memberPlacement`, `memberResolution`, `normIso`, `transIso`, `frameDatum`,
  `source_square`, `edge_square`, `frameIso`.
* §6 `exists_cls_eq`, `cls_surjective`, `card_le_of_index`, `starEquiv`,
  `card_eq_of_index`.
* §7 `occurrence_map` and the column calculus it runs on -- the input a
  divalent placement-rigidity theorem would consume.

## What is not proved here

* **`ResolutionExpansion.Transport` is a hypothesis of `transIso`, `frameDatum`,
  `source_square`, `edge_square` and `frameIso`**, and through `Covers` of
  everything in §6.  Its `endpoint_compatible` field is the obligation
  described above; its other five fields are the ones
  `GeometricUniformExpansion.lift` already needed.  Nothing here says an
  arbitrary limit isomorphism admits such a transport.
* **`Covers` is a hypothesis.**  It says every member's presented index is
  received by some candidate's index.  At `w4` the corresponding statement is
  proved; here it is carried, because the resolution factor is not a fixed
  finite set and because it contains a `Transport`.  It fails at every split
  regrowth (see its docstring), so §6 is used only where it holds.
* **`Separates` is a hypothesis**, and it is literally the injectivity of
  `i ↦ (cand i).starMember.cls`.  `card_eq_of_index` and `starEquiv` therefore
  prove no cardinality on their own.  At `w4` injectivity is
  `W4PairingRigidity.pairing_eq_of_expansionIso`, whose statement is specific to
  a four-element star; no divalent counterpart is proved here.  §7 is the input such a
  theorem would consume.
* **The candidates are a hypothesis**, exactly as in `W4WallExhaustion`:
  nothing *in this file* constructs a `Candidate`, and nothing says how many a
  wall has.
* **`hTwo` and the family are hypotheses.**  Nothing here proves that a wall of
  the Draisma--Vargas count schedule is divalent at its merged vertex, nor that
  it belongs to `w2M11` rather than `w2M1k`, `w2Mkk`, `w2P` or `w2R1`; the
  divalent placement census of §2 is shared by all five.
* **Nothing about multiplicities**, parities, `Count.CountSchedule`, or any
  other family.

## Consumers

The normalization of §1 and the placement census of §2 are used by the star censuses of
the divalent wall families (`M11StarCensusProof`, `M11StarExhaustionProof`,
`W2M1kStarCensusProof`, `W2MkkStarCensusProof`, `W2PStarExhaustionProof`) and at other
walls (`W3FourStarExhaustionProof`, `W3Nd3StarCensusProof`, `W4StarParity`), which feed the
trivalent walls, step 2 of the genus-six assembly.
-/
namespace DraismaVargas.Count.M11WallExhaustion

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GraphContraction GluingContraction TargetExpansion
open W2R1Target (TwoStar)
open GeometricSegmentWalls (FrameIso)
open WallStar (Regrowth Nondegenerate)
open SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

/-! ## 0.  Why discreteness is unavailable -/

/-- **A divalent codimension-one wall never carries a discrete merged
partition.**  A special case of
`Count.W4WallExhaustion.vertexPartition_ne_discrete_of_card_ne_four`, recorded
here because it is the reason none of the `Count.DiscreteW4Normalization`
route transcribes. -/
theorem vertexPartition_ne_discrete {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (vertex : target.V)
    (hExcess : data.targetExcess vertex = 1)
    (hTwo : (GluingDatum.incidentEdges vertex).card = 2) :
    data.vertexPartition vertex ≠ SheetPartition.discrete degree :=
  W4WallExhaustion.vertexPartition_ne_discrete_of_card_ne_four data vertex hExcess
    (by rw [hTwo]; decide)

/-! ## 1.  The incoming resolution of an arbitrary regrowth

Everything in this section is stated for an arbitrary placement census
`hPlacement`; nothing is specific to a divalent wall, to M-11, or to any
valency at all.  It is the resolution-expansion replacement for
`Count.DiscreteW4Normalization`. -/

section Incoming

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (second : (contract target hab hOne).edges → Bool)
  (hPlacement :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))

/-- The incoming target, normalized onto the canonical expansion of its own
limit at the placement `second`. -/
noncomputable def targetIso :
    Utilities.CFGraphIso target (graph (contract target hab hOne) ⟨a, hab⟩ second) :=
  M11IncomingTargetNormalization.incomingIso hc hab hOne second hPlacement

/-- The normalized datum. -/
noncomputable def transported : GluingDatum (graph (contract target hab hOne) ⟨a, hab⟩ second)
    degree :=
  GluingTransport.transport (targetIso hc hab hOne second hPlacement) data

/-- **The local resolution an arbitrary regrowth presents**: its two expanded
endpoint partitions and its regrown occurrence, read off the normalized datum.
No case distinction and no figure is used to produce it. -/
noncomputable def incomingResolution : ResolutionM11.LocalResolution degree :=
  ResolutionExpansion.readOff second (transported data hc hab hOne second hPlacement)

theorem transported_away (vertex : (contract target hab hOne).V) (hOff : vertex ≠ ⟨a, hab⟩) :
    (transported data hc hab hOne second hPlacement).vertexPartition
        (oldVertex (contract target hab hOne) vertex) =
      (contractDatum data hc hab hOne).vertexPartition vertex :=
  M11IncomingOuterPartitions.transported_vertexPartition_of_ne data hc hab hOne second
    hPlacement vertex hOff

theorem transported_retained (hConnected : graph_connected target) (hGenus : genus target = 0)
    (edge : (contract target hab hOne).edges) :
    (transported data hc hab hOne second hPlacement).edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ second (some edge)) =
      (contractDatum data hc hab hOne).edgePartition edge :=
  M11IncomingOuterPartitions.transported_edgePartition_retained data hc hab hOne second
    hPlacement hConnected hGenus edge

/-- The exterior compatibility obligation of the presented resolution is a
theorem, not an input. -/
theorem incomingOldCompatible (hConnected : graph_connected target) (hGenus : genus target = 0) :
    GlobalResolution.OldCompatible (contractDatum data hc hab hOne) ⟨a, hab⟩ second
      (incomingResolution data hc hab hOne second hPlacement) :=
  ResolutionExpansion.oldCompatible_of_expansion (contractDatum data hc hab hOne) ⟨a, hab⟩
    second (incomingResolution data hc hab hOne second hPlacement)
    (transported data hc hab hOne second hPlacement) rfl rfl
    (transported_away data hc hab hOne second hPlacement)
    (transported_retained data hc hab hOne second hPlacement hConnected hGenus)

/-- **An arbitrary regrowth is a resolution expansion of its own limit.**  A
literal equality of gluing data, not an isomorphism.  The generic replacement
for `Count.DiscreteW4Normalization.normalized_eq`: no discreteness, no
valency, no family. -/
theorem transported_eq_resolutionDatum (hConnected : graph_connected target)
    (hGenus : genus target = 0) :
    transported data hc hab hOne second hPlacement =
      GlobalResolution.datum (contractDatum data hc hab hOne) ⟨a, hab⟩ second
        (incomingResolution data hc hab hOne second hPlacement)
        (incomingOldCompatible data hc hab hOne second hPlacement hConnected hGenus) :=
  ResolutionExpansion.eq_resolutionDatum (contractDatum data hc hab hOne) ⟨a, hab⟩ second
    (incomingResolution data hc hab hOne second hPlacement)
    (transported data hc hab hOne second hPlacement) _ rfl rfl
    (transported_away data hc hab hOne second hPlacement) rfl
    (transported_retained data hc hab hOne second hPlacement hConnected hGenus)

/-- **The normalization isomorphism.**  The M-11 analogue of
`Count.DiscreteW4Normalization.datumIso`. -/
noncomputable def datumIso (hConnected : graph_connected target) (hGenus : genus target = 0) :
    GeometricDatumIso data
      (GlobalResolution.datum (contractDatum data hc hab hOne) ⟨a, hab⟩ second
        (incomingResolution data hc hab hOne second hPlacement)
        (incomingOldCompatible data hc hab hOne second hPlacement hConnected hGenus)) :=
  transported_eq_resolutionDatum data hc hab hOne second hPlacement hConnected hGenus ▸
    GeometricDatumIso.ofTargetIso (targetIso hc hab hOne second hPlacement) data

/-! ### The dictionaries the normalization induces -/

private theorem cast_iso_fields {firstTarget secondTarget : CFGraph} {d : ℕ}
    {first : GluingDatum firstTarget d} {middle last : GluingDatum secondTarget d}
    (h : middle = last) (iso : GeometricDatumIso first middle) :
    (h ▸ iso : GeometricDatumIso first last).targetVertex = iso.targetVertex ∧
    (h ▸ iso : GeometricDatumIso first last).targetEdge = iso.targetEdge ∧
    (h ▸ iso : GeometricDatumIso first last).vertexPerm = iso.vertexPerm ∧
    (h ▸ iso : GeometricDatumIso first last).edgePerm = iso.edgePerm := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

variable (hConnected : graph_connected target) (hGenus : genus target = 0)

theorem datumIso_targetVertex :
    (datumIso data hc hab hOne second hPlacement hConnected hGenus).targetVertex =
      (targetIso hc hab hOne second hPlacement).vertexEquiv :=
  (cast_iso_fields
    (transported_eq_resolutionDatum data hc hab hOne second hPlacement hConnected hGenus) _).1

theorem datumIso_targetEdge :
    (datumIso data hc hab hOne second hPlacement hConnected hGenus).targetEdge =
      GluingTransport.edgeEquiv (targetIso hc hab hOne second hPlacement) :=
  (cast_iso_fields
    (transported_eq_resolutionDatum data hc hab hOne second hPlacement hConnected hGenus) _).2.1

theorem datumIso_vertexPerm (vertex : target.V) :
    (datumIso data hc hab hOne second hPlacement hConnected hGenus).vertexPerm vertex =
      Equiv.refl (Fin degree) :=
  congrFun (cast_iso_fields
    (transported_eq_resolutionDatum data hc hab hOne second hPlacement hConnected hGenus) _).2.2.1
    vertex

theorem datumIso_edgePerm (edge : target.edges) :
    (datumIso data hc hab hOne second hPlacement hConnected hGenus).edgePerm edge =
      Equiv.refl (Fin degree) :=
  congrFun (cast_iso_fields
    (transported_eq_resolutionDatum data hc hab hOne second hPlacement hConnected hGenus) _).2.2.2
    edge

/-- Every literal `Option` column of the incoming contraction is preserved. -/
theorem datumIso_occurrence (column : Option (contract target hab hOne).edges) :
    (datumIso data hc hab hOne second hPlacement hConnected hGenus).targetEdge
        (M11IncomingCoordinates.incomingColumnEquiv hc hab hOne column) =
      occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ second column := by
  rw [datumIso_targetEdge]
  exact M11IncomingTargetNormalization.incomingIso_occurrence hc hab hOne second hPlacement
    hConnected hGenus column

/-- Normalizing the two expanded endpoints does not change the literal
contraction to the old target, including the endpoint-swap case.  The M-11
analogue of `Count.DiscreteW4Normalization.contractVertex_targetIso`. -/
theorem contractVertex_targetIso (vertex : target.V) :
    contractVertex (contract target hab hOne) ⟨a, hab⟩
        ((targetIso hc hab hOne second hPlacement).vertexEquiv vertex) =
      fold target hab vertex := by
  classical
  have hEndpoints := M11IncomingOuterPartitions.incomingIso_symm_endpoints hc hab hOne second
    hPlacement
  have hFoldEndpoints :
      (fold target hab ((targetIso hc hab hOne second hPlacement).vertexEquiv.symm
        (oldVertex (contract target hab hOne) ⟨a, hab⟩)),
       fold target hab ((targetIso hc hab hOne second hPlacement).vertexEquiv.symm
        (freshVertex (contract target hab hOne)))) = (⟨a, hab⟩, ⟨a, hab⟩) := by
    have h := congrArg (Prod.map (fold target hab) (fold target hab)) hEndpoints
    split_ifs at h <;>
      simpa only [Prod.map, fold_self, fold_of_ne target hab hab, targetIso] using h
  have hInverse : ∀ v : Vertex (contract target hab hOne),
      contractVertex (contract target hab hOne) ⟨a, hab⟩ v =
        fold target hab ((targetIso hc hab hOne second hPlacement).vertexEquiv.symm v) := by
    intro v
    cases v with
    | inl v =>
      by_cases h : v = ⟨a, hab⟩
      · subst v
        exact (congrArg Prod.fst hFoldEndpoints).symm
      · have hOld := M11IncomingOuterPartitions.incomingIso_symm_oldVertex hc hab hOne second
          hPlacement v h
        change (targetIso hc hab hOne second hPlacement).vertexEquiv.symm
          (oldVertex (contract target hab hOne) v) = v.1 at hOld
        exact (fold_of_ne target hab v.property).symm.trans
          (congrArg (fold target hab) hOld).symm
    | inr v =>
      cases v
      exact (congrArg Prod.snd hFoldEndpoints).symm
  simpa only [Equiv.symm_apply_apply] using
    hInverse ((targetIso hc hab hOne second hPlacement).vertexEquiv vertex)

/-- **The source-contraction dictionary of the normalization.**  The M-11
analogue of `Count.DiscreteW4Normalization.contractSourceVertex_datumIso`. -/
theorem sourceVertexMap_datumIso (vertex : data.SourceVertex) :
    sourceVertexMap data hc hab hOne vertex =
      GlobalResolution.sourceVertexMap (contractDatum data hc hab hOne) ⟨a, hab⟩ second
        (incomingResolution data hc hab hOne second hPlacement)
        (incomingOldCompatible data hc hab hOne second hPlacement hConnected hGenus)
        ((datumIso data hc hab hOne second hPlacement hConnected
          hGenus).sourceVertexEquiv vertex) := by
  show (contractDatum data hc hab hOne).sourceEndpoint (fold target hab vertex.1.1) vertex.1.2 =
    (contractDatum data hc hab hOne).sourceEndpoint
      (contractVertex (contract target hab hOne) ⟨a, hab⟩
        ((datumIso data hc hab hOne second hPlacement hConnected hGenus).targetVertex vertex.1.1))
      ((datumIso data hc hab hOne second hPlacement hConnected hGenus).vertexPerm vertex.1.1
        vertex.1.2)
  rw [datumIso_targetVertex, contractVertex_targetIso, datumIso_vertexPerm]
  rfl

/-- **The retained-occurrence dictionary of the normalization.**  The M-11
analogue of `Count.DiscreteW4Normalization.retainedSourceEdge_datumIso`. -/
theorem retainedSourceEdge_datumIso (edge : (contractDatum data hc hab hOne).SourceEdge) :
    (datumIso data hc hab hOne second hPlacement hConnected hGenus).sourceEdgeEquiv
        (WallDegeneration.sourceEdgeEmbedding data hc hab hOne edge) =
      ResolutionExpansion.retainedSourceEdge (contractDatum data hc hab hOne) ⟨a, hab⟩ second
        (incomingResolution data hc hab hOne second hPlacement)
        (incomingOldCompatible data hc hab hOne second hPlacement hConnected hGenus) edge := by
  apply Subtype.ext
  change ((datumIso data hc hab hOne second hPlacement hConnected hGenus).targetEdge
      (WallDegeneration.sourceEdgeEmbedding data hc hab hOne edge).1.1,
    (datumIso data hc hab hOne second hPlacement hConnected hGenus).edgePerm
      (WallDegeneration.sourceEdgeEmbedding data hc hab hOne edge).1.1
      (WallDegeneration.sourceEdgeEmbedding data hc hab hOne edge).1.2) = _
  rw [IncomingNormalizationRows.sourceEdgeEmbedding_val]
  apply Prod.ext
  · exact datumIso_occurrence data hc hab hOne second hPlacement hConnected hGenus (some edge.1.1)
  · rw [datumIso_edgePerm]
    rfl

end Incoming

/-! ## 2.  The placement census at a divalent wall

Two incident occurrences admit exactly two unordered splits, so the placement
factor of the index is `Bool`.  `false` is the *split* shape — both
occurrences stay on one side and the regrown occurrence is a leaf — and `true`
is the *joined* shape, one occurrence on each side.  This is the divalent
analogue of `LocalCases.W4IncomingTargetNormalization.pairing`, and unlike
that one it is a two-element and not a three-element census. -/

section Placement

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)

/-- The two canonical divalent placements. -/
noncomputable def divalentPlacement (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩) (side : Bool) :
    (contract target hab hOne).edges → Bool :=
  if side then star.right else fun _ ↦ true

@[simp] theorem divalentPlacement_true (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩) :
    divalentPlacement hab hOne star true = star.right := by
  rw [divalentPlacement, if_pos rfl]

@[simp] theorem divalentPlacement_false (hab : a ≠ b) (hOne : num_edges target a b = 1)
    (star : TwoStar (contract target hab hOne) ⟨a, hab⟩) :
    divalentPlacement hab hOne star false = fun _ ↦ true := by
  rw [divalentPlacement]
  exact if_neg (by decide)

include hc hab hOne star in
/-- **The divalent placement census.**  An arbitrary full-dimensional regrowth
of a divalent wall realizes one of the two canonical placements, possibly
after exchanging the expanded endpoints.  The trichotomy it runs on is
`LocalCases.SecondEquation.valencySplit_of_twoStar`, so nothing beyond
validity and change-minimality is used. -/
theorem exists_side (hValid : data.Valid) (hMinimal : data.ChangeMinimal) :
    ∃ side : Bool,
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge =
          divalentPlacement hab hOne star side edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge =
          !(divalentPlacement hab hOne star side edge)) := by
  rcases SecondEquation.valencySplit_of_twoStar data hc hab hOne hValid hMinimal star with
    ⟨hLeft, hRight, _, _⟩ | ⟨hLeft, _, _, _⟩ | ⟨_, hRight, _, _⟩
  · refine ⟨true, ?_⟩
    rw [divalentPlacement_true]
    exact M11IncomingTargetNormalization.joinedPlacement hc hab hOne star hLeft hRight
  · refine ⟨false, ?_⟩
    rw [divalentPlacement_false]
    exact M11IncomingTargetNormalization.splitPlacement hc hab hOne star (Or.inl hLeft)
  · refine ⟨false, ?_⟩
    rw [divalentPlacement_false]
    exact M11IncomingTargetNormalization.splitPlacement hc hab hOne star (Or.inr hRight)

/-- The placement shape an arbitrary regrowth presents. -/
noncomputable def side (hValid : data.Valid) (hMinimal : data.ChangeMinimal) : Bool :=
  Classical.choose (exists_side data hc hab hOne star hValid hMinimal)

theorem side_placement (hValid : data.Valid) (hMinimal : data.ChangeMinimal) :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge =
        divalentPlacement hab hOne star (side data hc hab hOne star hValid hMinimal) edge) ∨
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge =
        !(divalentPlacement hab hOne star (side data hc hab hOne star hValid hMinimal) edge)) :=
  Classical.choose_spec (exists_side data hc hab hOne star hValid hMinimal)

end Placement

/-! ## 3.  Pulling the wall's occurrence labels back to a member -/

/-- Pull the two named retained occurrences back along the actual target
occurrence bijection.  The divalent analogue of
`Count.DiscreteContraction.pullbackFourStar`. -/
noncomputable def pullbackTwoStar {target otherTarget : CFGraph} {degree : ℕ}
    {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
    (iso : GeometricDatumIso first second) (vertex : target.V) (otherVertex : otherTarget.V)
    (hVertex : iso.targetVertex vertex = otherVertex)
    (star : TwoStar otherTarget otherVertex) : TwoStar target vertex where
  label := star.label.trans (Equiv.subtypeEquiv iso.targetEdge (fun edge ↦ by
    rw [← hVertex]
    exact (iso.mem_incidentEdges_map vertex edge).symm)).symm

theorem pullbackTwoStar_edge {target otherTarget : CFGraph} {degree : ℕ}
    {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}
    (iso : GeometricDatumIso first second) (vertex : target.V) (otherVertex : otherTarget.V)
    (hVertex : iso.targetVertex vertex = otherVertex)
    (star : TwoStar otherTarget otherVertex) (label : Fin 2) :
    iso.targetEdge ((pullbackTwoStar iso vertex otherVertex hVertex star).edge label) =
      star.edge label :=
  iso.targetEdge.apply_symm_apply (star.edge label)

/-! ## 4.  Candidates at a (placement, resolution) index -/

section Candidates

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
variable {hy : Nondegenerate y} {wall : Regrowth core y degree}

open W4WallExhaustion (mergeVertex)

/-- **Merge pinning, carried as a named hypothesis.**  At `w4` this is a
theorem (`Count.DiscreteContraction.map_merge_of_four_valent`), because full
dimensionality bounds every non-merge valency by three while the merge has
four.  At valency two that argument gives nothing, so `Pinned` is exactly what
a divalent pinning invariant would have to supply. -/
def Pinned (hy : Nondegenerate y) (wall : Regrowth core y degree) : Prop :=
  ∀ (other : Regrowth core y degree) (iso : GeometricStar.LimitIso hy other wall),
    iso.datum.targetVertex (mergeVertex other) = mergeVertex wall

/-- **`Pinned` holds at every wall.**  `Count.MergePinning.map_merge`
pins the merged vertex at *every* valency, from the nonvanishing dimension
correction `Count.MergePinning.IsWall` alone. -/
theorem pinned_of_isWall (hWall : MergePinning.IsWall wall) : Pinned hy wall :=
  fun other iso ↦ MergePinning.map_merge other wall iso hWall

/-- **`Pinned` from equation (C)**, in the form
`LocalCases.SecondEquation`'s wall interfaces already state it. -/
theorem pinned_of_targetExcess_eq_one
    (hExcess : wall.limit.targetExcess (mergeVertex wall) = 1) : Pinned hy wall :=
  pinned_of_isWall (MergePinning.isWall_of_targetExcess_eq_one wall hExcess)

/-- Divalence of the merged vertex is inherited by every member of the star, so
the `w2` family condition needs to be checked only at the wall. -/
theorem member_card_incidentEdges (hWall : MergePinning.IsWall wall)
    (hTwo : (GluingDatum.incidentEdges (mergeVertex wall)).card = 2)
    (other : Regrowth core y degree) (iso : GeometricStar.LimitIso hy other wall) :
    (GluingDatum.incidentEdges (mergeVertex other)).card = 2 :=
  (MergePinning.card_incidentEdges_mergeVertex other wall iso hWall).trans hTwo

variable (wall) in
/-- The frame a candidate presentation carries. -/
noncomputable def candFrame
    (placement : (wall.frame.limitTarget wall.column).edges → Bool)
    (data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall) placement)
      degree)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p))
    (ident : CoreIdentification core data) : Frame core degree :=
  ⟨_, data, fullDim, ident⟩

variable (wall) in
/-- The regrowth it becomes once its vanishing coordinate is named. -/
noncomputable def candRegrowth
    (placement : (wall.frame.limitTarget wall.column).edges → Bool)
    (data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall) placement)
      degree)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p))
    (ident : CoreIdentification core data) (column : Fin p)
    (degenerate : (candFrame wall placement data fullDim ident).DegenerateAt y column) :
    Regrowth core y degree :=
  ⟨candFrame wall placement data fullDim ident, column, degenerate⟩

variable (wall) in
/-- The `hMerge` input of `Count.W4LimitContraction.limitIso`, from the
resolution's own contraction receipt. -/
theorem cand_merge
    {placement : (wall.frame.limitTarget wall.column).edges → Bool}
    {resolution : ResolutionM11.LocalResolution degree}
    {data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall) placement)
      degree}
    (side_old : data.vertexPartition
      (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)) = resolution.left)
    (side_fresh : data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column)) =
      resolution.right)
    (merge : SheetPartition.join resolution.left resolution.right =
      wall.limit.vertexPartition (mergeVertex wall)) :
    SheetPartition.join
        (data.vertexPartition
          (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)))
        (data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column))) =
      wall.limit.vertexPartition (mergeVertex wall) := by
  rw [side_old, side_fresh]
  exact merge

variable (wall) in
/-- **The canonical limit dictionary of a candidate.**  Contracting the
regrown occurrence returns the wall's own limit, by the literal contraction
dictionaries; no choice enters. -/
noncomputable def candDatumIso
    {placement : (wall.frame.limitTarget wall.column).edges → Bool}
    {resolution : ResolutionM11.LocalResolution degree}
    (data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall) placement)
      degree)
    (fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p))
    (ident : CoreIdentification core data) (column : Fin p)
    (degenerate : (candFrame wall placement data fullDim ident).DegenerateAt y column)
    (column_eq : (candFrame wall placement data fullDim ident).edgeOf column =
      occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) placement none)
    (side_old : data.vertexPartition
      (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)) = resolution.left)
    (side_fresh : data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column)) =
      resolution.right)
    (merge : SheetPartition.join resolution.left resolution.right =
      wall.limit.vertexPartition (mergeVertex wall))
    (away : ∀ vertex : (wall.frame.limitTarget wall.column).V, vertex ≠ mergeVertex wall →
      data.vertexPartition (oldVertex (wall.frame.limitTarget wall.column) vertex) =
        wall.limit.vertexPartition vertex)
    (retained : ∀ edge : (wall.frame.limitTarget wall.column).edges,
      data.edgePartition (occurrenceEquiv (wall.frame.limitTarget wall.column)
        (mergeVertex wall) placement (some edge)) = wall.limit.edgePartition edge) :
    GeometricDatumIso
      (candRegrowth wall placement data fullDim ident column degenerate).limit wall.limit :=
  W4LimitContraction.limitIso rfl
    (fst_ne_snd ((candFrame wall placement data fullDim ident).edgeOf column))
    ((candFrame wall placement data fullDim ident).numEdges_edgeOf column) column_eq
    wall.limit data (cand_merge wall side_old side_fresh merge) away retained

/-- **A candidate at the index `(placement, resolution)`.**  The first five
fields present a full-dimensional core-identified regrowth of the expanded
wall whose vanishing coordinate is the regrown occurrence; the next five are
the partition conditions `Count.ResolutionExpansion` and
`Count.W4LimitContraction` ask of a target expansion carrying that
resolution; the last two say the resulting canonical contraction dictionary
is over the core.

The only difference from `Count.W4WallExhaustion.Candidate` is that
`side_old`, `side_fresh` and `new_edge` name the resolution's three
partitions instead of the wall partition three times, and that the join
condition is a field (`merge`) instead of a corollary of discreteness. -/
structure Candidate (hy : Nondegenerate y) (wall : Regrowth core y degree)
    (placement : (wall.frame.limitTarget wall.column).edges → Bool)
    (resolution : ResolutionM11.LocalResolution degree) where
  /-- The candidate's gluing datum on the expanded wall target. -/
  data : GluingDatum (graph (wall.frame.limitTarget wall.column) (mergeVertex wall) placement)
    degree
  /-- Its full-dimensional presentation. -/
  fullDim : FullDimensionalSource.FullDimensionalSourcePresentation data (Fin p)
  /-- Its identification of the stable graph with the requested core. -/
  ident : CoreIdentification core data
  /-- The coordinate that vanishes at the wall request. -/
  column : Fin p
  /-- It really vanishes, and nothing else does. -/
  degenerate : (candFrame wall placement data fullDim ident).DegenerateAt y column
  /-- It is the regrown occurrence. -/
  column_eq : (candFrame wall placement data fullDim ident).edgeOf column =
    occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) placement none
  /-- The retained expanded endpoint carries the resolution's left partition. -/
  side_old : data.vertexPartition
      (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)) = resolution.left
  /-- …the fresh one carries its right partition. -/
  side_fresh : data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column)) =
    resolution.right
  /-- …and the regrown occurrence carries its new-edge partition. -/
  new_edge : data.edgePartition
      (occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) placement none) =
    resolution.newEdge
  /-- Contracting the regrown occurrence rejoins the wall partition. -/
  merge : SheetPartition.join resolution.left resolution.right =
    wall.limit.vertexPartition (mergeVertex wall)
  /-- Away from the wall nothing changes. -/
  away : ∀ vertex : (wall.frame.limitTarget wall.column).V, vertex ≠ mergeVertex wall →
    data.vertexPartition (oldVertex (wall.frame.limitTarget wall.column) vertex) =
      wall.limit.vertexPartition vertex
  /-- Retained occurrences keep the wall's occurrence partitions. -/
  retained : ∀ edge : (wall.frame.limitTarget wall.column).edges,
    data.edgePartition (occurrenceEquiv (wall.frame.limitTarget wall.column)
      (mergeVertex wall) placement (some edge)) = wall.limit.edgePartition edge
  /-- The canonical contraction dictionary preserves the inherited branch
  labels. -/
  overCore_vertex : ∀ branch : StableGraphIncidence.BranchVertex
      (candRegrowth wall placement data fullDim ident column degenerate).limit,
    (InheritedLimitIncidence.coreIdentification wall hy).vertex
        ((candDatumIso wall data fullDim ident column degenerate column_eq side_old side_fresh
          merge away retained).branchVertexEquiv
            (InheritedLimitRows.limit_connected _) branch) =
      (InheritedLimitIncidence.coreIdentification
        (candRegrowth wall placement data fullDim ident column degenerate) hy).vertex branch
  /-- …and the inherited row labels. -/
  overCore_row : ∀ row : W4StableSource.StablePath
      (candRegrowth wall placement data fullDim ident column degenerate).limit,
    (InheritedLimitIncidence.coreIdentification wall hy).row
        ((candDatumIso wall data fullDim ident column degenerate column_eq side_old side_fresh
          merge away retained).stablePathEquiv
            (InheritedLimitRows.limit_connected _) row) =
      (InheritedLimitIncidence.coreIdentification
        (candRegrowth wall placement data fullDim ident column degenerate) hy).row row

namespace Candidate

variable {placement : (wall.frame.limitTarget wall.column).edges → Bool}
  {resolution : ResolutionM11.LocalResolution degree}

/-- The candidate's frame. -/
noncomputable def frame (c : Candidate hy wall placement resolution) : Frame core degree :=
  candFrame wall placement c.data c.fullDim c.ident

/-- The candidate's regrowth. -/
noncomputable def regrowth (c : Candidate hy wall placement resolution) :
    Regrowth core y degree :=
  candRegrowth wall placement c.data c.fullDim c.ident c.column c.degenerate

theorem regrowth_frame (c : Candidate hy wall placement resolution) :
    c.regrowth.frame = c.frame := rfl

/-- The `hMerge` input of `Count.W4LimitContraction.limitIso`. -/
theorem merge_join (c : Candidate hy wall placement resolution) :
    SheetPartition.join
        (c.data.vertexPartition
          (oldVertex (wall.frame.limitTarget wall.column) (mergeVertex wall)))
        (c.data.vertexPartition (freshVertex (wall.frame.limitTarget wall.column))) =
      wall.limit.vertexPartition (mergeVertex wall) :=
  cand_merge wall c.side_old c.side_fresh c.merge

/-- **The candidate's canonical limit dictionary.** -/
noncomputable def datumIso (c : Candidate hy wall placement resolution) :
    GeometricDatumIso c.regrowth.limit wall.limit :=
  candDatumIso wall c.data c.fullDim c.ident c.column c.degenerate c.column_eq c.side_old
    c.side_fresh c.merge c.away c.retained

/-- **A candidate is a labelled member of the wall's geometric star.** -/
noncomputable def starLimitIso (c : Candidate hy wall placement resolution) :
    GeometricStar.LimitIso hy c.regrowth wall where
  datum := c.datumIso
  overCore_vertex := c.overCore_vertex
  overCore_row := c.overCore_row

noncomputable def starMember (c : Candidate hy wall placement resolution) :
    GeometricStar.StarMember hy wall := ⟨c.regrowth, ⟨c.starLimitIso⟩⟩

@[simp] theorem starMember_member (c : Candidate hy wall placement resolution) :
    (c.starMember).member = c.regrowth := rfl

/-- The exterior compatibility obligation of the candidate's index. -/
theorem oldCompatible (c : Candidate hy wall placement resolution) :
    GlobalResolution.OldCompatible wall.limit (mergeVertex wall) placement resolution :=
  ResolutionExpansion.oldCompatible_of_expansion wall.limit (mergeVertex wall) placement
    resolution c.data c.side_old c.side_fresh c.away c.retained

/-- **A candidate's datum is literally the resolution expansion at its own
index.**  The M-11 form of `Count.W4WallExhaustion.Candidate.data_eq`: an
equality of gluing data, not an isomorphism. -/
theorem data_eq (c : Candidate hy wall placement resolution) :
    c.data = GlobalResolution.datum wall.limit (mergeVertex wall) placement resolution
      c.oldCompatible :=
  ResolutionExpansion.eq_resolutionDatum wall.limit (mergeVertex wall) placement resolution
    c.data c.oldCompatible c.side_old c.side_fresh c.away c.new_edge c.retained

/-- **The candidate's source contraction, read through its own limit
dictionary, is the wall's own source endpoint.** -/
theorem member_contractSourceVertex (c : Candidate hy wall placement resolution)
    (vertex : c.data.SourceVertex) :
    c.datumIso.sourceVertexEquiv (InheritedLimitBranches.vertexMap c.regrowth vertex) =
      wall.limit.sourceEndpoint
        (contractVertex (wall.frame.limitTarget wall.column) (mergeVertex wall) vertex.1.1)
        vertex.1.2 :=
  W4LimitContraction.sourceVertexEquiv_sourceVertexMap rfl
    (fst_ne_snd (c.frame.edgeOf c.column)) (c.frame.numEdges_edgeOf c.column) c.column_eq
    wall.limit c.data c.merge_join c.away c.retained vertex

/-- **The candidate's retained occurrence embedding**, on the underlying
occurrence/sheet pair. -/
theorem member_edgeEmbedding_val (c : Candidate hy wall placement resolution)
    (edge : c.regrowth.limit.SourceEdge) :
    (InheritedLimitRows.edgeEmbedding c.regrowth edge).1 =
      (occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) placement
          (some (c.datumIso.sourceEdgeEquiv edge).1.1),
        (c.datumIso.sourceEdgeEquiv edge).1.2) := by
  have hVal : (c.datumIso.sourceEdgeEquiv edge).1 =
      (W4LimitContraction.edgeEquiv rfl (fst_ne_snd (c.frame.edgeOf c.column))
        (c.frame.numEdges_edgeOf c.column) c.column_eq edge.1.1, edge.1.2) :=
    W4LimitContraction.sourceEdgeEquiv_val rfl (fst_ne_snd (c.frame.edgeOf c.column))
      (c.frame.numEdges_edgeOf c.column) c.column_eq wall.limit c.data c.merge_join c.away
      c.retained edge
  rw [hVal]
  refine (IncomingNormalizationRows.sourceEdgeEmbedding_val c.data rfl
    (fst_ne_snd (c.frame.edgeOf c.column)) (c.frame.numEdges_edgeOf c.column) edge).trans ?_
  exact Prod.ext (W4LimitContraction.occurrenceEquiv_edgeEquiv rfl
    (fst_ne_snd (c.frame.edgeOf c.column)) (c.frame.numEdges_edgeOf c.column) c.column_eq
    edge.1.1).symm rfl

end Candidate

/-! ## 5.  The upward frame isomorphism -/

section Lift

variable (hPin : Pinned hy wall)
  (star : TwoStar (wall.frame.limitTarget wall.column) (mergeVertex wall))

/-- The two occurrence labels an arbitrary member inherits from the wall's. -/
noncomputable def inheritedStar (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    TwoStar (other.frame.limitTarget other.column) (mergeVertex other) :=
  pullbackTwoStar iso.datum (mergeVertex other) (mergeVertex wall) (hPin other iso) star

theorem inheritedStar_edge (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (label : Fin 2) :
    iso.datum.targetEdge ((inheritedStar hPin star other iso).edge label) = star.edge label :=
  pullbackTwoStar_edge iso.datum (mergeVertex other) (mergeVertex wall) (hPin other iso) star label

/-- **The placement shape an arbitrary member presents**, in inherited wall
occurrence labels. -/
noncomputable def memberSide (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) : Bool :=
  side other.frame.data rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (inheritedStar hPin star other iso)
    other.frame.fullDim.valid other.frame.fullDim.changeMinimal

/-- The canonical placement it normalizes onto. -/
noncomputable def memberPlacement (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    (other.frame.limitTarget other.column).edges → Bool :=
  divalentPlacement (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (inheritedStar hPin star other iso)
    (memberSide hPin star other iso)

theorem memberPlacement_spec (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    (∀ edge ∈ GluingDatum.incidentEdges (mergeVertex other),
      IncomingTargetExpansion.right (contracted := other.frame.edgeOf other.column) rfl
        (fst_ne_snd (other.frame.edgeOf other.column))
        (other.frame.numEdges_edgeOf other.column) edge =
      memberPlacement hPin star other iso edge) ∨
    (∀ edge ∈ GluingDatum.incidentEdges (mergeVertex other),
      IncomingTargetExpansion.right (contracted := other.frame.edgeOf other.column) rfl
        (fst_ne_snd (other.frame.edgeOf other.column))
        (other.frame.numEdges_edgeOf other.column) edge =
      !(memberPlacement hPin star other iso edge)) :=
  side_placement other.frame.data rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (inheritedStar hPin star other iso)
    other.frame.fullDim.valid other.frame.fullDim.changeMinimal

/-- **The local resolution an arbitrary member presents**, read off its own
endpoint partitions. -/
noncomputable def memberResolution (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) : ResolutionM11.LocalResolution degree :=
  incomingResolution other.frame.data rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (memberPlacement hPin star other iso)
    (memberPlacement_spec hPin star other iso)

theorem memberCompatible (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    GlobalResolution.OldCompatible other.limit (mergeVertex other)
      (memberPlacement hPin star other iso) (memberResolution hPin star other iso) :=
  incomingOldCompatible other.frame.data rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (memberPlacement hPin star other iso)
    (memberPlacement_spec hPin star other iso) other.frame.fullDim.targetConnected
    other.frame.fullDim.targetGenus

/-- **Step one.**  Normalize the arbitrary frame onto the resolution expansion
of its *own* limit, at its own placement and its own resolution.  This is
where the `w4` route would use discreteness; nothing of the kind is used. -/
noncomputable def normIso (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) :
    GeometricDatumIso other.frame.data
      (GlobalResolution.datum other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso)) :=
  M11WallExhaustion.datumIso other.frame.data rfl
    (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) (memberPlacement hPin star other iso)
    (memberPlacement_spec hPin star other iso) other.frame.fullDim.targetConnected
    other.frame.fullDim.targetGenus

variable {placement : (wall.frame.limitTarget wall.column).edges → Bool}
  {resolution : ResolutionM11.LocalResolution degree}

/-- **Step two.**  Carry that resolution expansion onto the wall's, along the
given limit isomorphism.  The hypothesis `transport` carries the obligation: its
`endpoint_compatible` field has no `w4` counterpart. -/
noncomputable def transIso (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : ResolutionExpansion.Transport iso.datum (mergeVertex other) (mergeVertex wall)
      (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
      resolution) :
    GeometricDatumIso
      (GlobalResolution.datum other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso))
      (GlobalResolution.datum wall.limit (mergeVertex wall) placement resolution
        c.oldCompatible) :=
  ResolutionExpansion.lift iso.datum (mergeVertex other) (mergeVertex wall)
    (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
    resolution (memberCompatible hPin star other iso) c.oldCompatible transport

/-- **The datum half of the upward lift.**  The third step is the literal
equality `Candidate.data_eq`, moved across by
`Count.UniformExpansionRecognition.ofEq`. -/
noncomputable def frameDatum (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : ResolutionExpansion.Transport iso.datum (mergeVertex other) (mergeVertex wall)
      (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
      resolution) :
    GeometricDatumIso other.frame.data c.data :=
  ((normIso hPin star other iso).trans (transIso hPin star other iso c transport)).trans
    (UniformExpansionRecognition.ofEq c.data_eq.symm)

theorem frameDatum_sourceVertex (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : ResolutionExpansion.Transport iso.datum (mergeVertex other) (mergeVertex wall)
      (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
      resolution) (vertex : other.frame.data.SourceVertex) :
    ((frameDatum hPin star other iso c transport).sourceVertexEquiv vertex).1 =
      ((transIso hPin star other iso c transport).sourceVertexEquiv
        ((normIso hPin star other iso).sourceVertexEquiv vertex)).1 :=
  UniformExpansionRecognition.ofEq_sourceVertexEquiv c.data_eq.symm
    ((transIso hPin star other iso c transport).sourceVertexEquiv
      ((normIso hPin star other iso).sourceVertexEquiv vertex))

theorem frameDatum_sourceEdge (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : ResolutionExpansion.Transport iso.datum (mergeVertex other) (mergeVertex wall)
      (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
      resolution) (edge : other.frame.data.SourceEdge) :
    ((frameDatum hPin star other iso c transport).sourceEdgeEquiv edge).1 =
      ((transIso hPin star other iso c transport).sourceEdgeEquiv
        ((normIso hPin star other iso).sourceEdgeEquiv edge)).1 :=
  UniformExpansionRecognition.ofEq_sourceEdgeEquiv c.data_eq.symm
    ((transIso hPin star other iso c transport).sourceEdgeEquiv
      ((normIso hPin star other iso).sourceEdgeEquiv edge))

/-- **The branch square.** -/
theorem source_square (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : ResolutionExpansion.Transport iso.datum (mergeVertex other) (mergeVertex wall)
      (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
      resolution) (vertex : other.frame.data.SourceVertex) :
    c.datumIso.sourceVertexEquiv
        (InheritedLimitBranches.vertexMap c.regrowth
          ((frameDatum hPin star other iso c transport).sourceVertexEquiv vertex)) =
      iso.datum.sourceVertexEquiv (InheritedLimitBranches.vertexMap other vertex) := by
  have hMember := Candidate.member_contractSourceVertex c
    ((frameDatum hPin star other iso c transport).sourceVertexEquiv vertex)
  have hVal := frameDatum_sourceVertex hPin star other iso c transport vertex
  have hNorm : InheritedLimitBranches.vertexMap other vertex =
      GlobalResolution.sourceVertexMap other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso)
        ((normIso hPin star other iso).sourceVertexEquiv vertex) :=
    sourceVertexMap_datumIso other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) (memberPlacement hPin star other iso)
      (memberPlacement_spec hPin star other iso) other.frame.fullDim.targetConnected
      other.frame.fullDim.targetGenus vertex
  have hLift := ResolutionExpansion.sourceVertexMap_lift iso.datum (mergeVertex other)
    (mergeVertex wall) (memberPlacement hPin star other iso) placement
    (memberResolution hPin star other iso) resolution (memberCompatible hPin star other iso)
    c.oldCompatible transport ((normIso hPin star other iso).sourceVertexEquiv vertex)
  rw [hMember, hVal, hNorm, hLift]
  rfl

/-- **The row square**, on retained quotient-source occurrences. -/
theorem edge_square (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : ResolutionExpansion.Transport iso.datum (mergeVertex other) (mergeVertex wall)
      (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
      resolution) (edge : other.limit.SourceEdge) :
    (frameDatum hPin star other iso c transport).sourceEdgeEquiv
        (InheritedLimitRows.edgeEmbedding other edge) =
      InheritedLimitRows.edgeEmbedding c.regrowth
        (StarFrameIso.transfer iso c.starLimitIso edge) := by
  apply Subtype.ext
  have hNorm : (normIso hPin star other iso).sourceEdgeEquiv
      (InheritedLimitRows.edgeEmbedding other edge) =
      ResolutionExpansion.retainedSourceEdge other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso) edge :=
    retainedSourceEdge_datumIso other.frame.data rfl
      (fst_ne_snd (other.frame.edgeOf other.column))
      (other.frame.numEdges_edgeOf other.column) (memberPlacement hPin star other iso)
      (memberPlacement_spec hPin star other iso) other.frame.fullDim.targetConnected
      other.frame.fullDim.targetGenus edge
  have hLift : (transIso hPin star other iso c transport).sourceEdgeEquiv
      (ResolutionExpansion.retainedSourceEdge other.limit (mergeVertex other)
        (memberPlacement hPin star other iso) (memberResolution hPin star other iso)
        (memberCompatible hPin star other iso) edge) =
      ResolutionExpansion.retainedSourceEdge wall.limit (mergeVertex wall) placement resolution
        c.oldCompatible (iso.datum.sourceEdgeEquiv edge) :=
    ResolutionExpansion.retainedSourceEdge_lift iso.datum (mergeVertex other)
      (mergeVertex wall) (memberPlacement hPin star other iso) placement
      (memberResolution hPin star other iso) resolution (memberCompatible hPin star other iso)
      c.oldCompatible transport edge
  have hMember := Candidate.member_edgeEmbedding_val c
    (StarFrameIso.transfer iso c.starLimitIso edge)
  have hTransfer : c.datumIso.sourceEdgeEquiv (StarFrameIso.transfer iso c.starLimitIso edge) =
      iso.datum.sourceEdgeEquiv edge :=
    StarFrameIso.datum_sourceEdgeEquiv_transfer iso c.starLimitIso edge
  rw [frameDatum_sourceEdge, hNorm, hLift, hMember, hTransfer]
  rfl

/-- **The upward frame isomorphism.**  An arbitrary regrowth of the core
carrying *any* labelled limit isomorphism to the wall, whose presented index
is transported onto a candidate's, is isomorphic over the labelled core to
that candidate.  Every hypothesis is displayed. -/
noncomputable def frameIso (other : Regrowth core y degree)
    (iso : GeometricStar.LimitIso hy other wall) (c : Candidate hy wall placement resolution)
    (transport : ResolutionExpansion.Transport iso.datum (mergeVertex other) (mergeVertex wall)
      (memberPlacement hPin star other iso) placement (memberResolution hPin star other iso)
      resolution) :
    FrameIso other.frame c.frame :=
  StarFrameIso.ofLimitSquare iso c.starLimitIso (frameDatum hPin star other iso c transport)
    (source_square hPin star other iso c transport) (edge_square hPin star other iso c transport)

/-! ## 6.  Exhaustion -/

section Exhaustion

variable {ι : Type*} (P : ι → ((wall.frame.limitTarget wall.column).edges → Bool))
  (R : ι → ResolutionM11.LocalResolution degree)
  (cand : ∀ i : ι, Candidate hy wall (P i) (R i))

/-- **The classification hypothesis.**  Every member of the wall's star presents
an index which some candidate's index receives, by a transport of its
resolution expansion.  At `w4` the corresponding statement is proved --
`W4IncomingTargetNormalization.pairing` names one of three pairings and
discreteness forces the resolution -- and here it is carried, because the
resolution factor is not a fixed finite set and the transport's
`endpoint_compatible` field is a hypothesis.

**Warning: `Covers` fails at every split regrowth**, i.e. at a regrowth one of whose
contracted endpoints is a leaf, for every index family `(P, R)`.  The cause is the gauge,
not the mathematics: `ResolutionExpansion.lift` puts the wall's merged permutation on both
expanded endpoints, so `Transport.endpoint_compatible` fails for the
transposition-relabelled frame, whose member is in the wall's own class.  Exhaustion itself
holds: `ResolutionExpansionFree.CoversFree` is `Covers` with decoupled endpoint
permutations, and `M11StarExhaustionProof` proves exhaustion at M-11 walls through it. -/
def Covers : Prop :=
  ∀ (other : Regrowth core y degree) (iso : GeometricStar.LimitIso hy other wall),
    ∃ i : ι, ResolutionExpansion.Transport iso.datum (mergeVertex other) (mergeVertex wall)
      (memberPlacement hPin star other iso) (P i) (memberResolution hPin star other iso) (R i)

/-- **Exhaustion.**  Every member of the wall's labelled geometric star lies in
one of the candidate classes. -/
theorem exists_cls_eq (hCover : Covers hPin star P R)
    (member : GeometricStar.StarMember hy wall) :
    ∃ i : ι, member.cls = ((cand i).starMember).cls := by
  obtain ⟨limIso⟩ := member.specializes
  obtain ⟨i, transport⟩ := hCover member.member limIso
  exact ⟨i, Quotient.sound ⟨frameIso hPin star member.member limIso (cand i) transport⟩⟩

theorem cls_surjective (hCover : Covers hPin star P R) :
    Function.Surjective fun i : ι ↦ ((cand i).starMember).cls := by
  refine Quotient.ind ?_
  intro member
  obtain ⟨i, hi⟩ := exists_cls_eq hPin star P R cand hCover member
  exact ⟨i, hi.symm⟩

include cand in
/-- **The upper bound**, with no distinctness receipt used. -/
theorem card_le_of_index [Fintype ι] (hCover : Covers hPin star P R) :
    Fintype.card (GeometricStar.Star hy wall) ≤ Fintype.card ι :=
  Fintype.card_le_of_surjective _ (cls_surjective hPin star P R cand hCover)

/-- **Distinctness, carried.**  Not proved in this file: at `w4` it is
`W4PairingRigidity.pairing_eq_of_expansionIso`, whose statement is specific to
a four-element star.  `occurrence_map` in section 7 is the input a divalent counterpart
would consume. -/
def Separates : Prop := Function.Injective fun i : ι ↦ ((cand i).starMember).cls

/-- **The wall's labelled geometric star is the index type**, given both
hypotheses. -/
noncomputable def starEquiv (hCover : Covers hPin star P R)
    (hSep : Separates P R cand) : ι ≃ GeometricStar.Star hy wall :=
  Equiv.ofBijective _ ⟨hSep, cls_surjective hPin star P R cand hCover⟩

theorem card_eq_of_index [Fintype ι] (hCover : Covers hPin star P R)
    (hSep : Separates P R cand) :
    Fintype.card (GeometricStar.Star hy wall) = Fintype.card ι :=
  (Fintype.card_congr (starEquiv hPin star P R cand hCover hSep)).symm

end Exhaustion

/-! ## 7.  What a divalent rigidity theorem would consume

At `w4`, distinctness of the candidate classes is
`W4PairingRigidity.pairing_eq_of_expansionIso`, and its `hlabel` input is the
statement that a frame isomorphism between two candidates matches the
canonical occurrence dictionaries of their two expansions.  That input is
proved here, at arbitrary placements, so a divalent placement-rigidity theorem
can be written against it without redoing any of the column calculus.  No
rigidity is proved. -/

section Occurrence

variable {placement' : (wall.frame.limitTarget wall.column).edges → Bool}
  {resolution' : ResolutionM11.LocalResolution degree}

/-- A frame isomorphism transports each column label of the source frame to the
column label its induced permutation names. -/
theorem targetEdge_column {k l : Frame core degree} (fi : FrameIso k l) (col : Fin p) :
    fi.datum.targetEdge (k.fullDim.labelling.targetEdge col) =
      l.fullDim.labelling.targetEdge (fi.column col) :=
  (l.fullDim.labelling.targetEdge.apply_symm_apply
    (fi.datum.targetEdge (k.fullDim.labelling.targetEdge col))).symm

theorem retainedColumns_limitColumns (w w' : Regrowth core y degree)
    (limIso : GeometricDatumIso w.limit w'.limit) (col : {col : Fin p // col ≠ w.column}) :
    StarMetricCompatibility.retainedColumns w'.frame w'.column
        (InheritedLimitRows.limitColumns w w' limIso col) =
      limIso.targetEdge (StarMetricCompatibility.retainedColumns w.frame w.column col) := by
  simp [InheritedLimitRows.limitColumns]

/-- A candidate's retained column labels are exactly the wall's retained
occurrences, read through its own canonical limit dictionary. -/
theorem occurrence_retained (c : Candidate hy wall placement resolution)
    (col : {col : Fin p // col ≠ c.regrowth.column}) :
    occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall) placement
        (some (c.datumIso.targetEdge
          (StarMetricCompatibility.retainedColumns c.regrowth.frame c.regrowth.column col))) =
      c.regrowth.frame.fullDim.labelling.targetEdge col.1 :=
  (W4LimitContraction.occurrenceEquiv_edgeEquiv rfl
    (fst_ne_snd (c.regrowth.frame.edgeOf c.regrowth.column))
    (c.regrowth.frame.numEdges_edgeOf c.regrowth.column) c.column_eq _).trans
    (InheritedLimitRows.unfoldEdge_retainedColumns c.regrowth col)

/-- The composite limit dictionary between two candidates. -/
noncomputable def candLimIso (c : Candidate hy wall placement resolution)
    (d : Candidate hy wall placement' resolution') :
    GeometricDatumIso c.regrowth.limit d.regrowth.limit :=
  c.datumIso.trans (d.datumIso).symm

theorem candLimIso_targetEdge (c : Candidate hy wall placement resolution)
    (d : Candidate hy wall placement' resolution')
    (edge : (c.regrowth.frame.limitTarget c.regrowth.column).edges) :
    d.datumIso.targetEdge ((candLimIso c d).targetEdge edge) = c.datumIso.targetEdge edge := by
  change d.datumIso.targetEdge (d.datumIso.targetEdge.symm (c.datumIso.targetEdge edge)) = _
  rw [Equiv.apply_symm_apply]

/-- Both candidates are members of the wall's star, so the composite preserves
the inherited row labels. -/
theorem candLimIso_rowLabel (c : Candidate hy wall placement resolution)
    (d : Candidate hy wall placement' resolution')
    (row : W4StableSource.StablePath c.regrowth.limit) :
    InheritedLimitRows.rowLabel d.regrowth hy
        ((candLimIso c d).stablePathEquiv
          (InheritedLimitRows.limit_connected c.regrowth) row) =
      InheritedLimitRows.rowLabel c.regrowth hy row :=
  (c.starLimitIso.trans (d.starLimitIso).symm).overCore_row row

/-- **Request-free column rigidity at this wall.**  Every frame isomorphism
between two candidates induces exactly the retained-column dictionary of their
composite limit isomorphism (`Count.FrameColumnRigidity.column_eq_allColumns`);
no coordinate-distinctness receipt and no choice of request enters.  This is
verbatim the `w4` argument: nothing in it is about valency. -/
theorem column_eq_limitColumns (c : Candidate hy wall placement resolution)
    (d : Candidate hy wall placement' resolution')
    (fi : FrameIso c.regrowth.frame d.regrowth.frame) :
    fi.column = InheritedLimitRows.allColumns c.regrowth d.regrowth (candLimIso c d) :=
  FrameColumnRigidity.column_eq_allColumns c.regrowth d.regrowth hy (candLimIso c d)
    (candLimIso_rowLabel c d) fi

/-- **The canonical occurrence labels of the two expansions are matched.**  At
`w4` this is the `hlabel` input of
`Count.W4PairingRigidity.pairing_eq_of_expansionIso`; a divalent
placement-rigidity theorem would consume exactly this. -/
theorem occurrence_map (c : Candidate hy wall placement resolution)
    (d : Candidate hy wall placement' resolution')
    (fi : FrameIso c.regrowth.frame d.regrowth.frame)
    (label : Option (wall.frame.limitTarget wall.column).edges) :
    fi.datum.targetEdge
        (occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
          placement label) =
      occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
        placement' label := by
  cases label with
  | none =>
    have hcol : fi.column c.regrowth.column = d.regrowth.column := by
      rw [column_eq_limitColumns c d fi]
      exact InheritedLimitRows.allColumns_collapsed c.regrowth d.regrowth (candLimIso c d)
    refine (congrArg fi.datum.targetEdge (c.column_eq).symm).trans ?_
    refine (targetEdge_column fi c.regrowth.column).trans ?_
    rw [hcol]
    exact d.column_eq
  | some edge =>
    obtain ⟨col, hEdge⟩ : ∃ col : {col : Fin p // col ≠ c.regrowth.column},
        c.datumIso.targetEdge
          (StarMetricCompatibility.retainedColumns c.regrowth.frame c.regrowth.column col) =
          edge :=
      ⟨(StarMetricCompatibility.retainedColumns c.regrowth.frame
          c.regrowth.column).symm (c.datumIso.targetEdge.symm edge), by
          rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]⟩
    have hLeft : occurrenceEquiv (wall.frame.limitTarget wall.column) (mergeVertex wall)
        placement (some edge) =
        c.regrowth.frame.fullDim.labelling.targetEdge col.1 := by
      rw [← hEdge]
      exact occurrence_retained c col
    have hColumn : fi.column col.1 =
        (InheritedLimitRows.limitColumns c.regrowth d.regrowth (candLimIso c d) col).1 := by
      rw [column_eq_limitColumns c d fi]
      exact InheritedLimitRows.allColumns_retained c.regrowth d.regrowth (candLimIso c d) col
    rw [hLeft, targetEdge_column fi col.1, hColumn]
    refine ((occurrence_retained d
      (InheritedLimitRows.limitColumns c.regrowth d.regrowth (candLimIso c d) col)).symm).trans ?_
    rw [retainedColumns_limitColumns, candLimIso_targetEdge, hEdge]

end Occurrence

end Lift

end Candidates

end DraismaVargas.Count.M11WallExhaustion
