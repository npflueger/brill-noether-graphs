module

public import DraismaVargas.LocalCases.W4IncomingGlobalMatching
public import DraismaVargas.LocalCases.M11IncomingOuterPartitions
public import DraismaVargas.LocalCases.W4IncomingTargetNormalization
public import DraismaVargas.LocalCases.GlobalW4
public import DraismaVargas.Infrastructure.PartitionNormalization

@[expose] public section

/-!
# Stored-representative normalization at a four-valent wall

Source: Draisma--Vargas Part I (arXiv:1909.12924), Section 6, Cases
`{aux-r0-nd2}` and `{aux-r0-nd3}` and Equation (1) (see
`W4IncomingGlobalMatching`). The representative
normalization proved here is a formalization artefact with no direct
counterpart in the paper -- the paper only names sheets -- so there is no
further passage to transcribe.

## Does `sheetRelabeling_apply` apply to `partition_sameBlocks` as it stands?

**No, not directly, on two independent counts, both closed here.**

1. **Shape.** `PartitionNormalization.sheetRelabeling`/`sheetRelabeling_apply`
   compare two `GluingDatum`s **on the same graph**, given `SameBlocks`
   at **every** vertex and **every** edge of that graph.
   `W4IncomingGlobalMatching.partition_sameBlocks` supplies `SameBlocks` at
   exactly three positions of `target` -- the two endpoints named by
   `pairingSide false`/`pairingSide true` and the edge `contracted` -- each
   compared against a bare `.left`/`.right`/`.newEdge` component of a
   `LocalResolution`, not against another `GluingDatum`. Reaching the
   `sheetRelabeling` shape needs (i) an actual second `GluingDatum`, and
   (ii) `SameBlocks` (or, better, literal equality) at every *other* vertex
   and edge too.
2. **Graph.** The natural second datum is the `datum` of the actual outgoing
   candidate `GlobalW4.PairingReceipts.candidate`, but by construction
   (`GlobalAssembly.datum`/`GlobalResolution.datum`) it lives on
   `TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩ (star.right q)`,
   a *different* (though canonically isomorphic) graph from `target`.
   `sheetRelabeling` cannot even be stated between `data` and
   `receipts.candidate.datum` until one side is transported across that
   isomorphism.

Both gaps close using only *generic* facts, none of it W4-specific:

* **The isomorphism.** `W4IncomingTargetNormalization.targetIso` is exactly
  `M11IncomingTargetNormalization.incomingIso` instantiated at
  `second := star.right q`.
  `pairingSide_false_eq_targetIso_symm`/`pairingSide_true_eq_targetIso_symm`
  prove `pairingSide` **is** the `oldVertex`/`freshVertex` image of
  `targetIso.symm`, by matching `pairingSide`'s own `if` against
  `M11IncomingOuterPartitions.incomingIso_symm_endpoints`'s identical `if`.
  This needs nothing beyond `W4IncomingTargetNormalization.pairing_placement`.
* **Everywhere off the wall.** `M11IncomingOuterPartitions`'s outer-partition
  lemmas (`transported_vertexPartition_of_ne`, `transported_edgePartition_new`,
  `transported_edgePartition_retained`) are stated with no M11-specific
  content at all -- purely in terms of `data`, `hc`, `hab`, `hOne`, an
  arbitrary `second : _.edges → Bool` and its placement hypothesis -- so they
  apply unchanged with `second := star.right q`. Symmetrically,
  `GlobalResolution`'s `datum_vertexPartition_old_of_ne`/`_old_wall`/`_fresh`
  and `datum_edgePartition_old`/`_new` (the generic simp lemmas underlying
  *every* candidate, W4 or M11) identify the candidate's own values there.
  `candidate_datum_vertexPartition_*`/`candidate_datum_edgePartition_*` below
  package these for `receipts.candidate.datum` specifically.
* **On the wall.** `pairingSide`'s two vertex facts and `partition_sameBlocks`
  itself supply exactly the remaining three positions.

`transported_sameBlocks_vertexPartition`/`_edgePartition` assemble the
complete `∀ vertex`/`∀ edge` `SameBlocks` hypotheses this way, and
`stored_representative_normalization` feeds them to
`PartitionNormalization.sheetRelabeling_apply`, exactly imitating the checked
M11 route (`sheetRelabeling_apply` and its consumers `PartitionStableNormalization`
etc.) rather than inventing a new one. No count-based row bijection and no
incoming classification is introduced anywhere in this transport: every
identification above is a literal equality or a named, quoted fact.

## The one hypothesis this file does not discharge

`stored_representative_normalization` needs an actual
`receipts : GlobalW4.PairingReceipts M₀ star (blockPattern data hc hab hOne star
pictures) q` -- the outgoing candidate datum itself, not merely its
partitions. This is a genuine, satisfiable
hypothesis (not a disguised contradiction: unlike `AuxR0SourceInput`, which
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput` shows is
vacuous under `fd`'s change-minimality, `PairingReceipts`'s fields are exact
block-local Riemann--Hurwitz identities with no `targetExcess`/`equation_c`
content forced to the wrong value). `GlobalW4.AuxR0Profile.ofValidChangeZero`
is the route to constructing it -- from `(M₀).Valid`, an `ExteriorProfile`
built case-by-case from `pictures`, and the ramification-sum-zero equation,
which is `(M₀).targetChange ⟨a, hab⟩ = 0`, itself the natural "Equation (C)"
fact for a codimension-one wall vertex under a full-dimensional presentation
of `data` -- **not** the vacuous `AuxR0SourceInput` bundle (see
`FullDimensionalSource`). This file states the dependency precisely rather than
assuming it.
-/

namespace DraismaVargas.LocalCases.W4IncomingRepresentatives

open DraismaVargas.Infrastructure GraphContraction GluingContraction ContractionRamification
open TargetExpansion
open W4StableSource W4Assembly W4TargetPairings
open ResolutionM11 ResolutionW4
open FullDimensionalSource WallDegeneration
open DraismaVargas.LocalCases.W4IncomingGlobalMatching (pairingSide partition_sameBlocks
  blockPattern)
open DraismaVargas.LocalCases.GlobalW4 (PairingReceipts)
open DraismaVargas.LocalCases.GlobalResolution

section Incoming

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : FourStar (contract target hab hOne) ⟨a, hab⟩)

local notation "M₀" => contractDatum data hc hab hOne
local notation "q" => W4IncomingTargetNormalization.pairing data fd hc hab hOne star

section Iso

include fd star

/-- **The pairing side `false`.** The canonical incoming endpoint carrying pairing
side `false` is the `oldVertex` image of the target isomorphism's inverse. -/
theorem pairingSide_false_eq_targetIso_symm :
    pairingSide data fd hc hab hOne star false =
      (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star).vertexEquiv.symm
        (oldVertex (contract target hab hOne) ⟨a, hab⟩) := by
  have hEndpoints := M11IncomingOuterPartitions.incomingIso_symm_endpoints hc hab hOne
    (star.right q) (W4IncomingTargetNormalization.pairing_placement data fd hc hab hOne star)
  unfold pairingSide W4IncomingTargetNormalization.targetIso
  by_cases hSupport :
      ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = star.right q e
  · rw [ite_eq_left hSupport] at hEndpoints ⊢
    exact (congrArg Prod.fst hEndpoints).symm
  · rw [ite_eq_right hSupport] at hEndpoints ⊢
    exact (congrArg Prod.fst hEndpoints).symm

/-- **The pairing side `true`.** The canonical incoming endpoint carrying pairing
side `true` is the `freshVertex` image of the target isomorphism's inverse. -/
theorem pairingSide_true_eq_targetIso_symm :
    pairingSide data fd hc hab hOne star true =
      (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star).vertexEquiv.symm
        (freshVertex (contract target hab hOne)) := by
  have hEndpoints := M11IncomingOuterPartitions.incomingIso_symm_endpoints hc hab hOne
    (star.right q) (W4IncomingTargetNormalization.pairing_placement data fd hc hab hOne star)
  unfold pairingSide W4IncomingTargetNormalization.targetIso
  by_cases hSupport :
      ∀ e ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne e = star.right q e
  · rw [ite_eq_left hSupport] at hEndpoints ⊢
    exact (congrArg Prod.snd hEndpoints).symm
  · rw [ite_eq_right hSupport] at hEndpoints ⊢
    exact (congrArg Prod.snd hEndpoints).symm

end Iso

section Normalization

/-- Shorthand: the per-block auxiliary picture assignment consumed by
`W4IncomingGlobalMatching.partition_sameBlocks`. -/
abbrev Pictures {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1) (star : FourStar (contract target hab hOne) ⟨a, hab⟩) :
    Type :=
  ∀ sourceBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
    AuxR0BlockPicture (contractDatum data hc hab hOne) star sourceBlock

variable (pairing : Fin 3) (pattern : Fin degree → BlockPattern)
  (receipts : PairingReceipts (contractDatum data hc hab hOne) star pattern pairing)

/-- The candidate's assembled datum's vertex partition at the retained wall
copy is literally the pasted resolution's left partition. -/
theorem candidate_datum_vertexPartition_old_wall :
    receipts.candidate.datum.vertexPartition (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing).left := by
  show expandedVertexPartition (contractDatum data hc hab hOne) ⟨a, hab⟩
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing)
      (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing).left
  exact expandedVertexPartition_old_wall (contractDatum data hc hab hOne) ⟨a, hab⟩
    (wholeResolution (contractDatum data hc hab hOne) star pattern pairing)

/-- The candidate's assembled datum's vertex partition at the fresh copy is
literally the pasted resolution's right partition. -/
theorem candidate_datum_vertexPartition_fresh :
    receipts.candidate.datum.vertexPartition (freshVertex (contract target hab hOne)) =
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing).right := by
  show expandedVertexPartition (contractDatum data hc hab hOne) ⟨a, hab⟩
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing)
      (freshVertex (contract target hab hOne)) =
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing).right
  exact expandedVertexPartition_fresh (contractDatum data hc hab hOne) ⟨a, hab⟩
    (wholeResolution (contractDatum data hc hab hOne) star pattern pairing)

/-- Off the wall, the candidate's assembled datum's vertex partition is
literally the contracted datum's own partition. -/
theorem candidate_datum_vertexPartition_old_of_ne
    (vertex : (contract target hab hOne).V) (hOff : vertex ≠ ⟨a, hab⟩) :
    receipts.candidate.datum.vertexPartition (oldVertex (contract target hab hOne) vertex) =
      (contractDatum data hc hab hOne).vertexPartition vertex := by
  show expandedVertexPartition (contractDatum data hc hab hOne) ⟨a, hab⟩
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing)
      (oldVertex (contract target hab hOne) vertex) =
      (contractDatum data hc hab hOne).vertexPartition vertex
  exact expandedVertexPartition_old_of_ne (contractDatum data hc hab hOne) ⟨a, hab⟩ vertex
    (wholeResolution (contractDatum data hc hab hOne) star pattern pairing) hOff

/-- The candidate's assembled datum's edge partition at the new occurrence is
literally the pasted resolution's new-edge partition. -/
theorem candidate_datum_edgePartition_new :
    receipts.candidate.datum.edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right pairing) none) =
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing).newEdge := by
  show expandedEdgePartition (contractDatum data hc hab hOne) ⟨a, hab⟩ (star.right pairing)
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing)
      (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right pairing) none) =
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing).newEdge
  exact expandedEdgePartition_new (contractDatum data hc hab hOne) ⟨a, hab⟩ (star.right pairing)
    (wholeResolution (contractDatum data hc hab hOne) star pattern pairing)

/-- At every retained occurrence, the candidate's assembled datum's edge
partition is literally the contracted datum's own partition. -/
theorem candidate_datum_edgePartition_old (edge : (contract target hab hOne).edges) :
    receipts.candidate.datum.edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right pairing) (some edge)) =
      (contractDatum data hc hab hOne).edgePartition edge := by
  show expandedEdgePartition (contractDatum data hc hab hOne) ⟨a, hab⟩ (star.right pairing)
      (wholeResolution (contractDatum data hc hab hOne) star pattern pairing)
      (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right pairing) (some edge)) =
      (contractDatum data hc hab hOne).edgePartition edge
  exact expandedEdgePartition_old (contractDatum data hc hab hOne) ⟨a, hab⟩ (star.right pairing)
    (wholeResolution (contractDatum data hc hab hOne) star pattern pairing) edge

end Normalization

section MainResult

include fd star in
/-- The transported incoming datum's vertex partition matches the candidate's
at the retained wall copy, up to `SameBlocks`. -/
theorem transported_sameBlocks_wall
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : Pictures data hc hab hOne star)
    (receipts : PairingReceipts (M₀) star (blockPattern data hc hab hOne star pictures) q) :
    ((GluingTransport.transport (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
        data).vertexPartition (oldVertex (contract target hab hOne) ⟨a, hab⟩)).SameBlocks
      (receipts.candidate.datum.vertexPartition (oldVertex (contract target hab hOne) ⟨a, hab⟩)) := by
  have h1 : (GluingTransport.transport
      (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
      data).vertexPartition (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      data.vertexPartition (pairingSide data fd hc hab hOne star false) :=
    (GluingTransport.transport_vertexPartition
        (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star) data
        (oldVertex (contract target hab hOne) ⟨a, hab⟩)).trans
      (congrArg data.vertexPartition (pairingSide_false_eq_targetIso_symm data fd hc hab hOne star).symm)
  have h2 : receipts.candidate.datum.vertexPartition (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      (wholeResolution (M₀) star (blockPattern data hc hab hOne star pictures) q).left :=
    candidate_datum_vertexPartition_old_wall data hc hab hOne star q
      (blockPattern data hc hab hOne star pictures) receipts
  rw [h1, h2]
  exact (partition_sameBlocks data fd hc hab hOne star hCompat pictures).1

include fd star in
/-- The transported incoming datum's vertex partition matches the candidate's
at the fresh copy, up to `SameBlocks`. -/
theorem transported_sameBlocks_fresh
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : Pictures data hc hab hOne star)
    (receipts : PairingReceipts (M₀) star (blockPattern data hc hab hOne star pictures) q) :
    ((GluingTransport.transport (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
        data).vertexPartition (freshVertex (contract target hab hOne))).SameBlocks
      (receipts.candidate.datum.vertexPartition (freshVertex (contract target hab hOne))) := by
  have h1 : (GluingTransport.transport
      (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
      data).vertexPartition (freshVertex (contract target hab hOne)) =
      data.vertexPartition (pairingSide data fd hc hab hOne star true) :=
    (GluingTransport.transport_vertexPartition
        (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star) data
        (freshVertex (contract target hab hOne))).trans
      (congrArg data.vertexPartition (pairingSide_true_eq_targetIso_symm data fd hc hab hOne star).symm)
  have h2 : receipts.candidate.datum.vertexPartition (freshVertex (contract target hab hOne)) =
      (wholeResolution (M₀) star (blockPattern data hc hab hOne star pictures) q).right :=
    candidate_datum_vertexPartition_fresh data hc hab hOne star q
      (blockPattern data hc hab hOne star pictures) receipts
  rw [h1, h2]
  exact (partition_sameBlocks data fd hc hab hOne star hCompat pictures).2.1

include fd star in
/-- Off the wall, the transported incoming datum's vertex partition equals
the candidate's literally (hence `SameBlocks`), with no dependence on the
picture assignment or the receipts. -/
theorem transported_sameBlocks_old_of_ne
    (pictures : Pictures data hc hab hOne star)
    (receipts : PairingReceipts (M₀) star (blockPattern data hc hab hOne star pictures) q)
    (vertex : (contract target hab hOne).V) (hOff : vertex ≠ ⟨a, hab⟩) :
    ((GluingTransport.transport (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
        data).vertexPartition (oldVertex (contract target hab hOne) vertex)).SameBlocks
      (receipts.candidate.datum.vertexPartition (oldVertex (contract target hab hOne) vertex)) := by
  have h1 : (GluingTransport.transport
      (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
      data).vertexPartition (oldVertex (contract target hab hOne) vertex) =
      (M₀).vertexPartition vertex :=
    M11IncomingOuterPartitions.transported_vertexPartition_of_ne data hc hab hOne
      (star.right q) (W4IncomingTargetNormalization.pairing_placement data fd hc hab hOne star)
      vertex hOff
  have h2 := candidate_datum_vertexPartition_old_of_ne data hc hab hOne star q
    (blockPattern data hc hab hOne star pictures) receipts vertex hOff
  rw [h1, h2]
  exact SheetPartition.SameBlocks.refl _

include fd star in
/-- The transported incoming datum's edge partition matches the candidate's
at the new occurrence, up to `SameBlocks`. -/
theorem transported_sameBlocks_edge_new
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : Pictures data hc hab hOne star)
    (receipts : PairingReceipts (M₀) star (blockPattern data hc hab hOne star pictures) q) :
    ((GluingTransport.transport (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
        data).edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right q) none)).SameBlocks
      (receipts.candidate.datum.edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right q) none)) := by
  have h1 : (GluingTransport.transport
      (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
      data).edgePartition (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right q) none) =
      data.edgePartition contracted :=
    M11IncomingOuterPartitions.transported_edgePartition_new data hc hab hOne
      (star.right q) (W4IncomingTargetNormalization.pairing_placement data fd hc hab hOne star)
      fd.targetConnected fd.targetGenus
  have h2 := candidate_datum_edgePartition_new data hc hab hOne star q
    (blockPattern data hc hab hOne star pictures) receipts
  rw [h1, h2]
  exact (partition_sameBlocks data fd hc hab hOne star hCompat pictures).2.2

include fd star in
/-- At every retained occurrence, the transported incoming datum's edge
partition equals the candidate's literally (hence `SameBlocks`), with no
dependence on the picture assignment or the receipts. -/
theorem transported_sameBlocks_edge_old
    (pictures : Pictures data hc hab hOne star)
    (receipts : PairingReceipts (M₀) star (blockPattern data hc hab hOne star pictures) q)
    (edge : (contract target hab hOne).edges) :
    ((GluingTransport.transport (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
        data).edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right q) (some edge))).SameBlocks
      (receipts.candidate.datum.edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right q) (some edge))) := by
  have h1 : (GluingTransport.transport
      (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
      data).edgePartition
        (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (star.right q) (some edge)) =
      (M₀).edgePartition edge :=
    M11IncomingOuterPartitions.transported_edgePartition_retained data hc hab hOne
      (star.right q) (W4IncomingTargetNormalization.pairing_placement data fd hc hab hOne star)
      fd.targetConnected fd.targetGenus edge
  have h2 := candidate_datum_edgePartition_old data hc hab hOne star q
    (blockPattern data hc hab hOne star pictures) receipts edge
  rw [h1, h2]
  exact SheetPartition.SameBlocks.refl _

include fd star in
/-- **Exhaustive transported vertex `SameBlocks`.** Every vertex of the
expanded target -- the retained wall copy, the fresh copy, and every
off-wall vertex -- is covered. -/
theorem transported_sameBlocks_vertexPartition
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : Pictures data hc hab hOne star)
    (receipts : PairingReceipts (M₀) star (blockPattern data hc hab hOne star pictures) q) :
    ∀ vertex : (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩ (star.right q)).V,
      ((GluingTransport.transport (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
          data).vertexPartition vertex).SameBlocks
        (receipts.candidate.datum.vertexPartition vertex) := by
  rintro (vertex | ⟨⟩)
  · by_cases hOff : vertex = (⟨a, hab⟩ : (contract target hab hOne).V)
    · subst hOff
      exact transported_sameBlocks_wall data fd hc hab hOne star hCompat pictures receipts
    · exact transported_sameBlocks_old_of_ne data fd hc hab hOne star pictures receipts vertex hOff
  · exact transported_sameBlocks_fresh data fd hc hab hOne star hCompat pictures receipts

include fd star in
/-- **Exhaustive transported edge `SameBlocks`.** Every occurrence of the
expanded target -- the new occurrence and every retained one -- is covered. -/
theorem transported_sameBlocks_edgePartition
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : Pictures data hc hab hOne star)
    (receipts : PairingReceipts (M₀) star (blockPattern data hc hab hOne star pictures) q) :
    ∀ edge : (TargetExpansion.graph (contract target hab hOne) ⟨a, hab⟩ (star.right q)).edges,
      ((GluingTransport.transport (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star)
          data).edgePartition edge).SameBlocks (receipts.candidate.datum.edgePartition edge) := by
  intro edge
  obtain ⟨c, rfl⟩ := (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩
    (star.right q)).surjective edge
  cases c with
  | none => exact transported_sameBlocks_edge_new data fd hc hab hOne star hCompat pictures receipts
  | some e => exact transported_sameBlocks_edge_old data fd hc hab hOne star pictures receipts e

include fd star in
/-- **The stored-representative normalization.** The incoming datum,
transported across the canonical target isomorphism, can be brought to
*exact* equality with the actual outgoing candidate's datum by an explicit
within-block sheet relabelling -- `SheetRelabeling`, built by
`PartitionNormalization.sheetRelabeling` from disjoint transpositions of
stored representatives, one independently chosen pair per shared block at
every vertex and every occurrence. This is genuinely stronger than the
pointwise `SameBlocks` proved in `W4IncomingGlobalMatching.partition_sameBlocks`:
no relation on stored representative functions is assumed, and no row
bijection or incoming classification is smuggled into the transport -- the
relabelling permutation at each vertex/edge is the literal transposition of
the two sheets each side's own representative-choice function names. -/
theorem stored_representative_normalization
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : Pictures data hc hab hOne star)
    (receipts : PairingReceipts (M₀) star (blockPattern data hc hab hOne star pictures) q) :
    ∃ relabeling : (GluingTransport.transport
        (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star) data).SheetRelabeling,
      relabeling.apply = receipts.candidate.datum :=
  ⟨PartitionNormalization.sheetRelabeling _ _
      (transported_sameBlocks_vertexPartition data fd hc hab hOne star hCompat pictures receipts)
      (transported_sameBlocks_edgePartition data fd hc hab hOne star hCompat pictures receipts),
    PartitionNormalization.sheetRelabeling_apply _ _
      (transported_sameBlocks_vertexPartition data fd hc hab hOne star hCompat pictures receipts)
      (transported_sameBlocks_edgePartition data fd hc hab hOne star hCompat pictures receipts)⟩

end MainResult

end Incoming

end DraismaVargas.LocalCases.W4IncomingRepresentatives
