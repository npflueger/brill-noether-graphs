import DraismaVargas.LocalCases.IncomingMatchingCore
import DraismaVargas.LocalCases.W2MkkStableIncidence
import DraismaVargas.LocalCases.W3Nd2IncomingMemberMatching
import DraismaVargas.LocalCases.IncomingSourceCases

/-!
# The incoming census at a `w2Mkk`-classified wall

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).  The ambient hypotheses are `{w2-r2}` and `{w2-r2-nd3}`; the tree
vocabulary `T_∅` / `T_2` is fixed in case `{w2-r2}` ("the trees contracting to
`T_0` are `T_∅` with `val u = 1`, `val v = 3`; and `T_2` with
`val u = val v = 2`").

This is the **incoming** side of the M-kk case: the datum is an arbitrary full-dimensional
cover whose contraction of a single target edge is the `w2Mkk` wall, and the
question is which Figure 34 member it is.  Nothing here is a family, a limit
matrix or an exit; those are `W2MkkLimitColumns`, `W2MkkLimitMatrix` and
`W2MkkArbitraryExit`.

## What this file settles, and what it does not

Settled here, unconditionally:

* **Base I is precluded on the target side** (`no_member_placement_of_leaf`,
  `divalent_of_member_placement`).  Every Figure 34 member's wall-side
  assignment is literally `W2MkkSourceCandidates.orientedStar profile`'s
  (`detach_right_eq`, `joined_right_eq`), which is `false` at `t₂` and `true`
  at `t₃`; a leaf at either restored endpoint sends *both* star occurrences to
  the same side (`IncomingW2TargetPlacement.right_star_of_leaf_left` / `_right`),
  so no leaf expansion is any member's target.  With
  `SecondEquation.valencySplit_of_twoStar` this is the `T_∅`/`T_2` dichotomy of
  case `{w2-r2}` read on the incoming cover: a `w2Mkk` incoming datum whose wall data
  matches a Figure 34 member has `val u = val v = 2`.

  The converse holds too: two divalent restored endpoints *give* the placement
  (`member_placement`), by `M11IncomingTargetNormalization.joinedPlacement` at
  the oriented star.  So `Placement` and `T_2` are equivalent here, which is
  the sharp form of "Base I is precluded" available without a source census.

* **The orientation.**  `doubleEnd` is the restored endpoint carrying the `t₂`
  occurrence and `singleEnd` the one carrying `t₃`; each is `a` or `b`
  according to the reconstructed side predicate, and both carry the contracted
  occurrence.  `transported_endpoints` says that the
  member's retained end restores `doubleEnd` and its fresh end restores
  `singleEnd`, in *both* orientations at once -- this is where
  `M11IncomingOuterPartitions.transported_endpointPartitions`' `if` is
  discharged.

* **The `r = 0` background census at a divalent-divalent W2 wall**
  (`background_edge_block_left`, `background_edge_block_right`,
  `background_joined_block_left`, `background_joined_block_right`, and at the
  `t₂` endpoint `background_edge_block_doubleEnd`,
  `background_joined_block_singleEnd`).  This is the W2 analogue of
  `W3Nd2IncomingNormalization.background_whole_block_census`, and it is
  *symmetric*: at a `(2,2)` wall both `AnyBlock` orientations apply, so all
  three of `vertexPartition a`, `vertexPartition b` and
  `edgePartition contracted` are joined on every `r = 0` block, and the forest
  count `e + 1 = a + b` forces every one of the three counts to be `1`.  At the
  `(2,3)` W3 wall only one side was divalent and the count argument ran one way.

Not settled here, and stated as `SelectedCensus` rather than assumed silently:
the **selected-class** census on the distinguished block `A₀`.  That is Part I's
Base II.1 / Base II.2 analysis in case `{w2-r2}` -- which of Figure 34's three
sheet pictures the incoming cover's two restored endpoints and contracted
occurrence carry on `A₀` -- and it is the irreducibly per-case half of every
incoming instance.  `SelectedCensus` names exactly the four facts, one per
Figure 34 position, that `W2MkkIncomingMatching` consumes; `W2MkkSelectedCensus`
proves them.

## The classifier's payload

`IncomingSourceCases.W2.Classification.mkk` carries `block`, `source`,
`deleted_target`, `pair_card`, `single_succ_card`, `background`,
`first_two_le`, `second_two_le`.  `shape_of_mkk` turns `deleted_target`,
`first_two_le`, `second_two_le` into `W2MkkSourceCandidates.Shape` field for
field, and `localRamification_eq_zero_of_ne` is `background` restated in the
form `W3Nd2IncomingBackground.AnyBlock` consumes.  `pair_card` and
`single_succ_card` are `Shape.cardinality`, re-derived there from the profile's
own case disjunction, so they are not re-imposed.
-/

namespace DraismaVargas.LocalCases.W2MkkIncomingCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open TargetExpansion ResolutionM11 FullDimensionalSource WallDegeneration
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11IncomingPartitions
open W2MkkSourceCandidates
open IncomingMatchingCore

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum data hc hab hOne) star)
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum data hc hab hOne) star block)

/-! ## §1  The classifier's payload, as the M-kk bundle -/

/-- **`IncomingSourceCases.W2.Classification.mkk`'s three M-kk fields are
`W2MkkSourceCandidates.Shape`.**  Cardinality M is `deleted_target`, and the
two index bounds are `first_two_le`, `second_two_le`. -/
theorem shape_of_mkk
    (hDeleted : profile.deleted.edge.1.1.1 = star.edge profile.singleLabel)
    (hFirst : 2 ≤ (contractDatum data hc hab hOne).sourceEdgeIndex profile.first.1)
    (hSecond : 2 ≤ (contractDatum data hc hab hOne).sourceEdgeIndex profile.second.1) :
    Shape profile :=
  ⟨hDeleted, hFirst, hSecond⟩

/-- **The classifier's `background` field, in the form the `r = 0` census
consumes.**  Every wall block other than the distinguished one has vanishing
local ramification; `W3Nd2IncomingBackground.AnyBlock` asks for exactly that,
with no `W3SourceInput` and no star arity. -/
theorem localRamification_eq_zero_of_ne
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    {other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩} (hNe : other ≠ block) :
    (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0 :=
  hBackground other hNe

/-! ## §2  Every Figure 34 member's wall-side assignment is the oriented star -/

theorem detach_right_eq (shape : Shape profile) (detach : DetachData profile) :
    (detach.candidate shape).right = (orientedStar profile).right := rfl

theorem joined_right_eq (distinguished : Fin degree) :
    (joinedCandidate profile distinguished).right = (orientedStar profile).right := rfl

/-- The `t₂` occurrence is on the retained side of every Figure 34 member. -/
theorem orientedStar_right_double :
    (orientedStar profile).right (star.edge profile.doubleLabel) = false := by
  rw [← orientedStar_edge_zero profile]
  exact TwoStar.right_edge_zero _

/-- The `t₃` occurrence is on the fresh side of every Figure 34 member. -/
theorem orientedStar_right_single :
    (orientedStar profile).right (star.edge profile.singleLabel) = true := by
  rw [← orientedStar_edge_one profile]
  exact TwoStar.right_edge_one _


/-! ## §3  The target-side dichotomy: Base I is precluded, Base II gives the placement

Part I, case `{w2-r2}`, lists the two trees contracting to `T_0`: `T_∅`, with `val u = 1` and
`val v = 3`, and `T_2`, with `val u = val v = 2`.
`SecondEquation.valencySplit_of_twoStar` is that list, proved on the incoming
cover.  Figure 34's members all expand the wall with one occurrence on each
side, so only `T_2` can be an incoming M-kk cover. -/

/-- **The support half of a placement, from the two values at the star.**  The
two labelled occurrences exhaust the contracted wall's star, so agreeing with
the member's side assignment at both of them is agreement everywhere. -/
theorem support_of_star_values
    (twoStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hZero : IncomingTargetExpansion.right hc hab hOne (twoStar.edge 0) = false)
    (hOneEdge : IncomingTargetExpansion.right hc hab hOne (twoStar.edge 1) = true) :
    ∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = twoStar.right edge := by
  intro edge hAt
  obtain ⟨label, hLabel⟩ := twoStar.label.surjective ⟨edge, hAt⟩
  have hEdge : twoStar.edge label = edge := congrArg Subtype.val hLabel
  rw [← hEdge]
  have hCases : label = 0 ∨ label = 1 := by omega
  rcases hCases with rfl | rfl
  · exact hZero.trans (TwoStar.right_edge_zero twoStar).symm
  · exact hOneEdge.trans (TwoStar.right_edge_one twoStar).symm

/-- **`T_2` gives every Figure 34 member its placement.**  This is
`M11IncomingTargetNormalization.joinedPlacement` at the *oriented* star, which
is legitimate because a `TwoStar` is nothing but a labelling of the two
occurrences at a divalent wall. -/
theorem member_placement
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    Placement hc hab hOne (orientedStar profile).right :=
  M11IncomingTargetNormalization.joinedPlacement hc hab hOne (orientedStar profile)
    hLeft hRight

theorem detach_placement (shape : Shape profile) (detach : DetachData profile)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    Placement hc hab hOne (detach.candidate shape).right :=
  member_placement data hc hab hOne profile hLeft hRight

theorem joined_placement (distinguished : Fin degree)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    Placement hc hab hOne (joinedCandidate profile distinguished).right :=
  member_placement data hc hab hOne profile hLeft hRight

/-- **Base I is precluded, target side.**  A leaf at either restored endpoint
puts both wall occurrences on one side, and no Figure 34 member does that:
its assignment is `false` at `t₂` and `true` at `t₃`. -/
theorem no_member_placement_of_leaf
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    ¬ Placement hc hab hOne (orientedStar profile).right := by
  have hDouble := orientedStar_right_double (data := data) (hc := hc) (hab := hab)
    (hOne := hOne) profile
  have hSingle := orientedStar_right_single (data := data) (hc := hc) (hab := hab)
    (hOne := hOne) profile
  have hDoubleAt : star.edge profile.doubleLabel ∈
      GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
    star.edge_mem_incidentEdges profile.doubleLabel
  have hSingleAt : star.edge profile.singleLabel ∈
      GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
    star.edge_mem_incidentEdges profile.singleLabel
  rintro (hSame | hSwap)
  · rcases hLeaf with hLeft | hRight
    · have hDoubleValue := hSame _ hDoubleAt
      rw [IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeft
        profile.doubleLabel, hDouble] at hDoubleValue
      exact Bool.noConfusion hDoubleValue
    · have hSingleValue := hSame _ hSingleAt
      rw [IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hRight
        profile.singleLabel, hSingle] at hSingleValue
      exact Bool.noConfusion hSingleValue
  · rcases hLeaf with hLeft | hRight
    · have hSingleValue := hSwap _ hSingleAt
      rw [IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeft
        profile.singleLabel, hSingle] at hSingleValue
      exact Bool.noConfusion hSingleValue
    · have hDoubleValue := hSwap _ hDoubleAt
      rw [IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hRight
        profile.doubleLabel, hDouble] at hDoubleValue
      exact Bool.noConfusion hDoubleValue

include fullDim in
/-- **`T_∅` or `T_2`, decided by the member.**  An incoming cover whose wall data
is any Figure 34 member's has two divalent restored endpoints: `T_2` of case
`{w2-r2}`, the case Base II lives in.  Only the reconstructed target enters; no
source-side census is used. -/
theorem divalent_of_member_placement
    (hPlacement : Placement hc hab hOne (orientedStar profile).right) :
    (GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 := by
  rcases valencySplit_of_twoStar data hc hab hOne fullDim.valid fullDim.changeMinimal star with
    ⟨hLeft, hRight, _, _⟩ | ⟨hLeft, _, _, _⟩ | ⟨_, hRight, _, _⟩
  · exact ⟨hLeft, hRight⟩
  · exact absurd hPlacement (no_member_placement_of_leaf data hc hab hOne profile
      (Or.inl hLeft))
  · exact absurd hPlacement (no_member_placement_of_leaf data hc hab hOne profile
      (Or.inr hRight))


/-! ## §4  Which restored endpoint carries `t₂`

Figure 34 draws `u` as the `t₂` endpoint and `v` as the `t₃` endpoint.  The
incoming cover does not know that labelling: the contracted edge's two ends are
`a` and `b`, and which of them is `u` is read off the reconstructed side
predicate.  Both branches occur, and everything below is stated so that neither
is a hypothesis. -/

/-- The restored endpoint carrying the `t₂` occurrence -- Figure 34's `u`. -/
noncomputable def doubleEnd : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge profile.doubleLabel) = true
    then b else a

/-- The restored endpoint carrying the `t₃` occurrence -- Figure 34's `v`. -/
noncomputable def singleEnd : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge profile.doubleLabel) = true
    then a else b

@[simp] theorem doubleEnd_of_false
    (hFalse : IncomingTargetExpansion.right hc hab hOne
      (star.edge profile.doubleLabel) = false) :
    doubleEnd data hc hab hOne profile = a := by
  simp only [doubleEnd, hFalse, Bool.false_eq_true, if_false]

@[simp] theorem singleEnd_of_false
    (hFalse : IncomingTargetExpansion.right hc hab hOne
      (star.edge profile.doubleLabel) = false) :
    singleEnd data hc hab hOne profile = b := by
  simp only [singleEnd, hFalse, Bool.false_eq_true, if_false]

@[simp] theorem doubleEnd_of_true
    (hTrue : IncomingTargetExpansion.right hc hab hOne
      (star.edge profile.doubleLabel) = true) :
    doubleEnd data hc hab hOne profile = b := by
  simp only [doubleEnd, hTrue, if_true]

@[simp] theorem singleEnd_of_true
    (hTrue : IncomingTargetExpansion.right hc hab hOne
      (star.edge profile.doubleLabel) = true) :
    singleEnd data hc hab hOne profile = a := by
  simp only [singleEnd, hTrue, if_true]

/-- `doubleEnd` and `singleEnd` are the two restored endpoints, in one order or
the other.  Both orders occur. -/
theorem ends_cases :
    (doubleEnd data hc hab hOne profile = a ∧ singleEnd data hc hab hOne profile = b) ∨
      (doubleEnd data hc hab hOne profile = b ∧ singleEnd data hc hab hOne profile = a) := by
  rcases Bool.eq_false_or_eq_true (IncomingTargetExpansion.right hc hab hOne
    (star.edge profile.doubleLabel)) with hTrue | hFalse
  · exact Or.inr ⟨doubleEnd_of_true data hc hab hOne profile hTrue,
      singleEnd_of_true data hc hab hOne profile hTrue⟩
  · exact Or.inl ⟨doubleEnd_of_false data hc hab hOne profile hFalse,
      singleEnd_of_false data hc hab hOne profile hFalse⟩

/-- At a `T_2` wall the two star occurrences are restored to opposite
endpoints: three distinct occurrences cannot meet a divalent vertex. -/
theorem star_values_ne
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    IncomingTargetExpansion.right hc hab hOne (star.edge profile.doubleLabel) ≠
      IncomingTargetExpansion.right hc hab hOne (star.edge profile.singleLabel) := by
  have h := IncomingW2TargetPlacement.right_star_ne_of_divalent hc hab hOne
    (orientedStar profile) hLeft hRight
  rwa [orientedStar_edge_zero profile, orientedStar_edge_one profile] at h

/-- **The `if` of `M11IncomingOuterPartitions.transported_endpointPartitions`,
decided.**  The normalization leaves the two expanded ends in place exactly
when the `t₂` occurrence is restored to `a`. -/
theorem support_iff
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = (orientedStar profile).right edge) ↔
      IncomingTargetExpansion.right hc hab hOne (star.edge profile.doubleLabel) = false := by
  constructor
  · intro hSupport
    have h := hSupport _ (star.edge_mem_incidentEdges profile.doubleLabel)
    rwa [orientedStar_right_double] at h
  · intro hFalse
    have hNe := star_values_ne data hc hab hOne profile hLeft hRight
    have hTrue : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel) = true := by
      rcases Bool.eq_false_or_eq_true (IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.singleLabel)) with h | h
      · exact h
      · exact absurd (hFalse.trans h.symm) hNe
    exact support_of_star_values hc hab hOne (orientedStar profile)
      (by rw [orientedStar_edge_zero profile]; exact hFalse)
      (by rw [orientedStar_edge_one profile]; exact hTrue)

/-- **The retained end of every Figure 34 member restores `doubleEnd`, and its
fresh end restores `singleEnd`** -- in both orientations at once. -/
theorem transported_endpoints
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (hPlacement : Placement hc hab hOne (orientedStar profile).right) :
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          (orientedStar profile).right hPlacement) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      data.vertexPartition (doubleEnd data hc hab hOne profile) ∧
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          (orientedStar profile).right hPlacement) data).vertexPartition
        (freshVertex (contract target hab hOne)) =
      data.vertexPartition (singleEnd data hc hab hOne profile) := by
  classical
  have hPair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne
    (orientedStar profile).right hPlacement
  by_cases hSupport : ∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = (orientedStar profile).right edge
  · have hFalse := (support_iff data hc hab hOne profile hLeft hRight).mp hSupport
    rw [if_pos hSupport] at hPair
    rw [doubleEnd_of_false data hc hab hOne profile hFalse,
      singleEnd_of_false data hc hab hOne profile hFalse]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
  · have hTrue : IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.doubleLabel) = true := by
      rcases Bool.eq_false_or_eq_true (IncomingTargetExpansion.right hc hab hOne
        (star.edge profile.doubleLabel)) with h | h
      · exact h
      · exact absurd ((support_iff data hc hab hOne profile hLeft hRight).mpr h) hSupport
    rw [if_neg hSupport] at hPair
    rw [doubleEnd_of_true data hc hab hOne profile hTrue,
      singleEnd_of_true data hc hab hOne profile hTrue]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

/-- The `t₂` occurrence of the incoming target meets `doubleEnd`. -/
theorem flag_mem_doubleEnd :
    unfoldEdge hc hab hOne (star.edge profile.doubleLabel) ∈
      GluingDatum.incidentEdges (doubleEnd data hc hab hOne profile) := by
  rcases Bool.eq_false_or_eq_true (IncomingTargetExpansion.right hc hab hOne
    (star.edge profile.doubleLabel)) with hTrue | hFalse
  · rw [doubleEnd_of_true data hc hab hOne profile hTrue]
    exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hTrue
  · rw [doubleEnd_of_false data hc hab hOne profile hFalse]
    exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
      (star.edge_mem_incidentEdges profile.doubleLabel)).mp hFalse

/-- The contracted occurrence meets both restored endpoints, hence `doubleEnd`. -/
theorem contracted_mem_doubleEnd :
    contracted ∈ GluingDatum.incidentEdges (doubleEnd data hc hab hOne profile) := by
  rcases ends_cases data hc hab hOne profile with ⟨hDouble, _⟩ | ⟨hDouble, _⟩
  · rw [hDouble]; exact contracted_mem_incidentEdges_left hc
  · rw [hDouble]; exact contracted_mem_incidentEdges_right hc

/-- The contracted occurrence also meets `singleEnd`. -/
theorem contracted_mem_singleEnd :
    contracted ∈ GluingDatum.incidentEdges (singleEnd data hc hab hOne profile) := by
  rcases ends_cases data hc hab hOne profile with ⟨_, hSingle⟩ | ⟨_, hSingle⟩
  · rw [hSingle]; exact contracted_mem_incidentEdges_right hc
  · rw [hSingle]; exact contracted_mem_incidentEdges_left hc

/-- Both restored endpoints are divalent at a `T_2` wall, so in particular both
`doubleEnd` and `singleEnd` are. -/
theorem doubleEnd_divalent
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    (GluingDatum.incidentEdges (doubleEnd data hc hab hOne profile)).card = 2 := by
  rcases ends_cases data hc hab hOne profile with ⟨hDouble, _⟩ | ⟨hDouble, _⟩
  · rw [hDouble]; exact hLeft
  · rw [hDouble]; exact hRight

theorem singleEnd_divalent
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    (GluingDatum.incidentEdges (singleEnd data hc hab hOne profile)).card = 2 := by
  rcases ends_cases data hc hab hOne profile with ⟨_, hSingle⟩ | ⟨_, hSingle⟩
  · rw [hSingle]; exact hRight
  · rw [hSingle]; exact hLeft


/-! ## §5  The `r = 0` background census at a `T_2` W2 wall

`W3Nd2IncomingBackground.AnyBlock` and `W3Nd2IncomingNormalization.AnyBlock`
state the `{w3-r0}` census at *any* wall block of vanishing local ramification,
with the divalence of one restored endpoint as an explicit hypothesis and no
star arity anywhere.  At a `T_2` W2 wall **both** endpoints are divalent, so
both orientations apply at once and the census is symmetric: `a`, `b` and the
contracted occurrence are all joined on every `r = 0` block, and all three
induced counts are `1`.  At the `(2,3)` W3 wall only one side was divalent and
the forest count `e + 1 = a + b` ran one way; here it closes from both sides. -/

section Background

variable (hForest : ContractionForest data a b contracted)

/-- The wall datum's own partition at the merged vertex, as a relation
identity at fixed sheets.  Rewriting the partition itself is blocked by the
`WallBlock` subtype, so the transfer is done one relation at a time. -/
theorem merged_rel_eq (first second : Fin degree) :
    ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel first second =
      (mergedPartition data a b).Rel first second :=
  congrArg (fun partition : SheetPartition degree ↦ partition.Rel first second)
    (contractDatum_vertexPartition_merge data hc hab hOne)

/-- The same sheet, read as a member of its own wall block. -/
theorem merged_rel_ofSheet (sheet : Fin degree) :
    (mergedPartition data a b).Rel
      (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet).1 sheet :=
  cast (merged_rel_eq data hc hab hOne _ sheet)
    (((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).rel_repr_left sheet)

/-- A sheet outside the distinguished block names a wall block other than it. -/
theorem ofSheet_ne_block {sheet : Fin degree}
    (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ sheet ≠ block := by
  intro hEq
  exact hOff (hEq ▸ merged_rel_ofSheet data hc hab hOne sheet)

include fullDim hForest

/-- **Every occurrence at the divalent `a` carries `a`'s own block, off the
distinguished class.**  This is `hBgEdge` of
`IncomingMatchingCore.wall_blocks_of_dictionary`, left orientation. -/
theorem background_edge_block_left
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges a)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.edgePartition edge).block sheet = (data.vertexPartition a).block sheet := by
  have hIff := W3Nd2IncomingNormalization.AnyBlock.background_edge_rel_iff_of_left_divalent
    data hc hab hOne fullDim hForest hLeft
    (hBackground _ (ofSheet_ne_block data hc hab hOne hOff)) edge hEdge sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact hIff other (merged_rel_ofSheet data hc hab hOne sheet)

/-- The mirror at the divalent `b`. -/
theorem background_edge_block_right
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (edge : target.edges) (hEdge : edge ∈ GluingDatum.incidentEdges b)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.edgePartition edge).block sheet = (data.vertexPartition b).block sheet := by
  have hIff := W3Nd2IncomingNormalization.AnyBlock.background_edge_rel_iff_of_right_divalent
    data hc hab hOne fullDim hForest hRight
    (hBackground _ (ofSheet_ne_block data hc hab hOne hOff)) edge hEdge sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact hIff other (merged_rel_ofSheet data hc hab hOne sheet)

/-- **`b` carries the whole wall block, off the distinguished class.**  This is
`hBgTri` of `IncomingMatchingCore.wall_blocks_of_dictionary`, left
orientation. -/
theorem background_joined_block_right
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition b).block sheet = (mergedPartition data a b).block sheet := by
  have hJoined := (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_left_divalent
    data hc hab hOne fullDim hForest hLeft
    (hBackground _ (ofSheet_ne_block data hc hab hOne hOff))).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition_right data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

/-- The mirror: `a` carries the whole wall block. -/
theorem background_joined_block_left
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition a).block sheet = (mergedPartition data a b).block sheet := by
  have hJoined := (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_right_divalent
    data hc hab hOne fullDim hForest hRight
    (hBackground _ (ofSheet_ne_block data hc hab hOne hOff))).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

end Background


/-! ## §6  The two source-side inputs of the wall comparison, at `doubleEnd`

`IncomingMatchingCore.wall_blocks_of_dictionary` reads its background data at
the endpoint `u` carrying the flag occurrence and the contracted occurrence.
For Figure 34 that is `doubleEnd`: `t₂` is the retained direction of every
member (`W2MkkStableLift.detachWallCandidate`, `joinedWallCandidate` both take
`retainedTarget := star.edge profile.doubleLabel`).  The two lemmas below are
`hBgEdge` and `hBgTri`, uniform in the orientation. -/

section CoreInputs

variable (hForest : ContractionForest data a b contracted)

include fullDim hForest

/-- **`hBgEdge`.**  Off the distinguished block every occurrence at the `t₂`
endpoint carries that endpoint's own class. -/
theorem background_edge_block_doubleEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (edge : target.edges)
    (hEdge : edge ∈ GluingDatum.incidentEdges (doubleEnd data hc hab hOne profile))
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.edgePartition edge).block sheet =
      (data.vertexPartition (doubleEnd data hc hab hOne profile)).block sheet := by
  rcases ends_cases data hc hab hOne profile with ⟨hDouble, _⟩ | ⟨hDouble, _⟩
  · rw [hDouble] at hEdge ⊢
    exact background_edge_block_left data hc hab hOne fullDim hForest hBackground hLeft
      edge hEdge sheet hOff
  · rw [hDouble] at hEdge ⊢
    exact background_edge_block_right data hc hab hOne fullDim hForest hBackground hRight
      edge hEdge sheet hOff

/-- **`hBgTri`.**  Off the distinguished block the `t₃` endpoint carries the
whole wall block. -/
theorem background_joined_block_singleEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition (singleEnd data hc hab hOne profile)).block sheet =
      (mergedPartition data a b).block sheet := by
  rcases ends_cases data hc hab hOne profile with ⟨_, hSingle⟩ | ⟨_, hSingle⟩
  · rw [hSingle]
    exact background_joined_block_right data hc hab hOne fullDim hForest hBackground hLeft
      sheet hOff
  · rw [hSingle]
    exact background_joined_block_left data hc hab hOne fullDim hForest hBackground hRight
      sheet hOff

end CoreInputs

/-! ## §7  The flag occurrence and its partition

The flag is the incoming occurrence above `t₂`; its partition is literally the
wall datum's own occurrence partition there, because `contractDatum` is defined
by unfolding (`GluingContraction.contractDatum_edgePartition` is `rfl`). -/

/-- Figure 34's flag: the incoming occurrence above `t₂`. -/
noncomputable def flagEdge : target.edges :=
  unfoldEdge hc hab hOne (star.edge profile.doubleLabel)

/-- Its partition is the wall datum's `t₂` occurrence partition, on the nose. -/
theorem flag_block (sheet : Fin degree) :
    (data.edgePartition (flagEdge data hc hab hOne profile)).block sheet =
      ((contractDatum data hc hab hOne).edgePartition
        (star.edge profile.doubleLabel)).block sheet := rfl

theorem flagEdge_mem_doubleEnd :
    flagEdge data hc hab hOne profile ∈
      GluingDatum.incidentEdges (doubleEnd data hc hab hOne profile) :=
  flag_mem_doubleEnd data hc hab hOne profile

end DraismaVargas.LocalCases.W2MkkIncomingCensus
