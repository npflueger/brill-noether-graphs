module

public import DraismaVargas.LocalCases.IncomingMatchingCore
public import DraismaVargas.LocalCases.W2M1kStableIncidence
public import DraismaVargas.LocalCases.W2M1kLeaves
public import DraismaVargas.LocalCases.W3Nd2IncomingMemberMatching
public import DraismaVargas.LocalCases.IncomingSourceCases

@[expose] public section

/-!
# The incoming census at a `w2M1k`-classified wall

Source: Draisma--Vargas Part I, Case {w2-r2-nd3-M-1k} (abbreviated M-1k),
Figure 33 and Equation (7).  The ambient hypotheses are those of Cases
{w2-r2} and {w2-r2-nd3}; the tree vocabulary `T_∅` / `T_2` is fixed at the
start of Case {w2}: the trees contracting to `T_0` are `T_∅` with
`val u = 1`, `val v = 3`, and `T_2` with `val u = val v = 2`.

This is the **incoming** side of the M-1k case: the datum is an arbitrary full-dimensional
cover whose contraction of a single target edge is the `w2M1k` wall, and the
question is which Figure 33 member it is.

## The one structural difference from the other subcases of Case {w2}

At M-kk, M-11 and P the three (or two) members share a wall-side assignment and
**Base I is precluded**: `W2MkkSelectedCensus.divalent_endpoints` and
`W2PIncomingCensus.divalent_endpoints` are theorems, so `Placement` is one per
family and the incoming target is always `T_2`.

**At M-1k Base I.a genuinely occurs.**  Figure 33's `M⁽¹⁾` is the leaf member:
`W2M1kSourceCandidates.leaf_target_valencies` gives its expanded target valencies
`(1, 3)`, i.e. `T_∅`, and `W2M1kLeaves.leaf_right` says its wall-side assignment
is the constant `true` -- *both* wall directions go to the fresh endpoint --
while `W2M1kStableGraph.divided_right` and `joined_right` give the other two
members the two-star's own assignment, which is `false` at `star.edge 0` and
`true` at `star.edge 1`.  So:

* a leaf restored endpoint **precludes** `M⁽²⁾` and `M⁽³⁾`
  (`no_star_placement_of_leaf`), and
* two divalent restored endpoints **preclude** `M⁽¹⁾`
  (`no_true_placement_of_divalent`).

With `SecondEquation.valencySplit_of_twoStar` this is a genuine **trichotomy**
(`member_trichotomy`), not M-kk's dichotomy: the incoming target type decides
which subset of Figure 33 the cover can be, and both branches occur.  So at a
Case {w2} wall the `Placement` is *not* always one per family (with all members
sharing `right`): that fails at M-1k, and it is the whole reason this file is
not `W2MkkIncomingCensus` with names changed.

## What this file settles, and what it does not

Settled here, unconditionally:

* **The classifier's payload as the M-1k bundle** (§1).
  `IncomingSourceCases.W2.Classification.m1k` carries `block`, `source`,
  `deleted_target`, `pair_card`, `single_succ_card`, `background`, `unit_large`.
  Its `unit_large` is a *disjunction* -- which of the two doubled-direction
  occurrences is the unit one -- while `W2M1kSourceCandidates.Shape.unit_index`
  fixes it to be `first`.  `exchange` swaps the two literal occurrences of a
  `W2R2SourceProfile.SourceProfile` (every field is symmetric in them but
  `first_ne_second`), so `exists_shape_of_m1k` is total on the classifier's payload:
  either the profile itself or its exchange carries a `Shape`.
* **The target-side trichotomy** (§3), as above.
* **The orientation** (§4, §5).  In the `T_2` branch `zeroEnd` is the restored
  endpoint carrying `star.edge 0`'s occurrence and `oneEnd` the one carrying
  `star.edge 1`'s; in the `T_∅` branch `leafEnd` is the monovalent restored
  endpoint and `branchEnd` the trivalent one.  `transported_endpoints` /
  `leaf_transported_endpoints` discharge the `if` of
  `M11IncomingOuterPartitions.transported_endpointPartitions` in both branches,
  in both orders at once.

  Note the M-1k indexing: `M⁽²⁾` and `M⁽³⁾` assign sides by the **star label**,
  not by the profile's double/single label (`W2M1kSourceCandidates.dividedPattern`
  and `joinedPattern` take `leftExternal := star.edge 0`, `rightExternal :=
  star.edge 1`), so no `orientedStar` is needed and M-kk's `doubleEnd` /
  `singleEnd` become `zeroEnd` / `oneEnd`.
* **The `r = 0` background census at a divalent-divalent wall of Case {w2}**
  (§6), by the
  `AnyBlock` namespaces of `W3Nd2IncomingBackground` and
  `W3Nd2IncomingNormalization`, exactly as at M-kk: at a `(2,2)` wall both
  orientations apply, so all three of `vertexPartition a`, `vertexPartition b`
  and `edgePartition contracted` are joined on every `r = 0` block.

Not settled here, and named rather than assumed silently:

* the **selected-class** census on the distinguished block `A₀`
  (`W2M1kIncomingMatching.SelectedCensus`, proved in `W2M1kSelectedCensus`);
  and
* the **`r = 0` background census at a `(1,3)` wall**
  (`W2M1kIncomingMatching.LeafBackgroundCensus`, proved in
  `W2M1kLeafBackground`).  The `AnyBlock` lemmas all assume one restored
  endpoint is **divalent** (`background_edge_rel_iff_of_left_divalent` and its
  five siblings); at Base I.a neither endpoint is, so they do not apply there.
-/

namespace DraismaVargas.LocalCases.W2M1kIncomingCensus

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionRamification
open TargetExpansion ResolutionM11 FullDimensionalSource WallDegeneration
open W4Assembly W4StableSource W2R1Target SecondEquation
open M11IncomingPartitions
open W2M1kSourceCandidates
open IncomingMatchingCore

/-! ## §1  The classifier's payload, as the M-1k bundle -/

section Payload

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}

/-- **The two literal doubled-direction occurrences, exchanged.**  Every field
of `W2R2SourceProfile.SourceProfile` is symmetric in `first` and `second` except
`first_ne_second`, `double_fibre` and `exhaustive`, and those three are
symmetric up to `Ne.symm`, `Finset.pair_comm` and a reordering of a disjunction.

This exists because `IncomingSourceCases.W2.Classification.m1k`'s `unit_large`
field is the disjunction "`first` is the unit one, or `second` is", while
`W2M1kSourceCandidates.Shape.unit_index` fixes `first`.  Without the exchange,
`exists_shape_of_m1k` would cover only one disjunct. -/
noncomputable def exchange (profile : W2R2SourceProfile.SourceProfile data star block) :
    W2R2SourceProfile.SourceProfile data star block where
  ramification := profile.ramification
  valency := profile.valency
  doubleLabel := profile.doubleLabel
  singleLabel := profile.singleLabel
  labels_ne := profile.labels_ne
  first := profile.second
  second := profile.first
  third := profile.third
  deleted := profile.deleted
  first_ne_second := profile.first_ne_second.symm
  first_target := profile.second_target
  second_target := profile.first_target
  third_target := profile.third_target
  first_survives := profile.second_survives
  second_survives := profile.first_survives
  third_survives := profile.third_survives
  double_fibre := by
    refine profile.double_fibre.trans ?_
    ext edge
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  single_fibre := profile.single_fibre
  exhaustive := by
    intro edge
    rcases profile.exhaustive edge with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  cases := by
    rcases profile.cases with ⟨hDeleted, hPair, hSingle⟩ | ⟨hDeleted, hPair, hSingle⟩
    · refine Or.inl ⟨hDeleted, ?_, hSingle⟩
      omega
    · refine Or.inr ⟨hDeleted, ?_, hSingle⟩
      omega

@[simp] theorem exchange_first (profile : W2R2SourceProfile.SourceProfile data star block) :
    (exchange profile).first = profile.second := rfl

@[simp] theorem exchange_second (profile : W2R2SourceProfile.SourceProfile data star block) :
    (exchange profile).second = profile.first := rfl

@[simp] theorem exchange_third (profile : W2R2SourceProfile.SourceProfile data star block) :
    (exchange profile).third = profile.third := rfl

@[simp] theorem exchange_deleted (profile : W2R2SourceProfile.SourceProfile data star block) :
    (exchange profile).deleted = profile.deleted := rfl

@[simp] theorem exchange_singleLabel
    (profile : W2R2SourceProfile.SourceProfile data star block) :
    (exchange profile).singleLabel = profile.singleLabel := rfl

/-- **`IncomingSourceCases.W2.Classification.m1k`'s fields are
`W2M1kSourceCandidates.Shape`, in the orientation where `first` is the unit
occurrence.**  Cardinality M is `deleted_target`; `k` is the *other* doubled
index, and `pair_card` turns it into `|A₀| = k + 1`. -/
noncomputable def shape_of_unit_first
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hDeleted : profile.deleted.edge.1.1.1 = star.edge profile.singleLabel)
    (hUnit : data.sourceEdgeIndex profile.first.1 = 1)
    (hLarge : 2 ≤ data.sourceEdgeIndex profile.second.1) : Shape profile where
  k := data.sourceEdgeIndex profile.second.1
  one_lt_k := hLarge
  blockCard := by
    rcases profile.cases with ⟨_, hPair, _⟩ | ⟨hDouble, _, _⟩
    · rw [← hPair, hUnit, Nat.add_comm]
    · exact absurd (star.edge_injective (hDeleted.symm.trans hDouble)).symm profile.labels_ne
  deleted_single := hDeleted
  unit_index := hUnit

/-- **The same in the mirror orientation**, on the exchanged profile.  `Shape`
fixes `first` to be the unit occurrence, so when the classifier's `unit_large`
picks `second` the shape lives over `exchange profile`. -/
noncomputable def shape_of_unit_second
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hDeleted : profile.deleted.edge.1.1.1 = star.edge profile.singleLabel)
    (hUnit : data.sourceEdgeIndex profile.second.1 = 1)
    (hLarge : 2 ≤ data.sourceEdgeIndex profile.first.1) : Shape (exchange profile) :=
  shape_of_unit_first (exchange profile) hDeleted hUnit hLarge

/-- **The classifier's payload always carries an M-1k `Shape`**: either on the
profile itself or on its exchange.  This is `unit_large` discharged, and it is
the only place the classifier's disjunction is read. -/
theorem exists_shape_of_m1k (profile : W2R2SourceProfile.SourceProfile data star block)
    (hDeleted : profile.deleted.edge.1.1.1 = star.edge profile.singleLabel)
    (hUnitLarge :
      (data.sourceEdgeIndex profile.first.1 = 1 ∧
        2 ≤ data.sourceEdgeIndex profile.second.1) ∨
      (data.sourceEdgeIndex profile.second.1 = 1 ∧
        2 ≤ data.sourceEdgeIndex profile.first.1)) :
    Nonempty (Shape profile) ∨ Nonempty (Shape (exchange profile)) := by
  rcases hUnitLarge with ⟨hUnit, hLarge⟩ | ⟨hUnit, hLarge⟩
  · exact Or.inl ⟨shape_of_unit_first profile hDeleted hUnit hLarge⟩
  · exact Or.inr ⟨shape_of_unit_second profile hDeleted hUnit hLarge⟩

end Payload

/-! ## §2  The three Figure 33 members' wall-side assignments

`M⁽²⁾` and `M⁽³⁾` use the two-star's own assignment; `M⁽¹⁾` uses the constant
`true`.  All three are `rfl`. -/

section Assignments

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

theorem divided_right_eq (shape : Shape profile) (divided : DividedData profile)
    (edge : target.edges) :
    (DividedData.candidate shape divided).right edge = star.right edge := rfl

theorem joined_right_eq (geometry : GlobalM1k.Geometry data wall) (edge : target.edges) :
    (joinedCandidate star geometry).right edge = star.right edge := rfl

theorem leaf_right_eq (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (edge : target.edges) :
    (LeafPair.candidate input shape pair).right edge = true := rfl

end Assignments


/-! ## §3  The target-side trichotomy

Part I, Case {w2}, lists the two trees contracting to `T_0`: `T_∅`, with `val u = 1` and
`val v = 3`, and `T_2`, with `val u = val v = 2`.
`SecondEquation.valencySplit_of_twoStar` is that list, proved on the incoming
cover.  Figure 33 uses **both**. -/

section Trichotomy

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)

/-- **The support half of a placement, from the two values at the star.**  The
two labelled occurrences exhaust the contracted wall's star, so agreeing with a
side assignment at both of them is agreement everywhere. -/
theorem support_of_star_values
    (side : (contract target hab hOne).edges → Bool)
    (hZero : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = side (star.edge 0))
    (hOneEdge : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = side (star.edge 1)) :
    ∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = side edge := by
  intro edge hAt
  obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hAt⟩
  have hEdge : star.edge label = edge := congrArg Subtype.val hLabel
  rw [← hEdge]
  have hCases : label = 0 ∨ label = 1 := by omega
  rcases hCases with rfl | rfl
  · exact hZero
  · exact hOneEdge

/-- **`T_2` gives `M⁽²⁾` and `M⁽³⁾` their placement.**  This is
`M11IncomingTargetNormalization.joinedPlacement` at the two-star itself, which
is legitimate because the two divalent members' assignment is literally
`star.right`. -/
theorem star_placement
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    Placement hc hab hOne star.right :=
  M11IncomingTargetNormalization.joinedPlacement hc hab hOne star hLeft hRight

/-- **`T_∅` gives `M⁽¹⁾` its placement.**  This is
`M11IncomingTargetNormalization.splitPlacement`, whose conclusion is literally
`Placement hc hab hOne (fun _ ↦ true)`. -/
theorem true_placement (twoStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    Placement hc hab hOne (fun _ ↦ true) :=
  M11IncomingTargetNormalization.splitPlacement hc hab hOne twoStar hLeaf

/-- **A leaf restored endpoint precludes `M⁽²⁾` and `M⁽³⁾`.**  A leaf puts both
wall occurrences on one side, and the two-star's assignment is `false` at
`star.edge 0` and `true` at `star.edge 1`. -/
theorem no_star_placement_of_leaf
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    ¬ Placement hc hab hOne star.right := by
  have hZeroAt : star.edge 0 ∈
      GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
    star.edge_mem_incidentEdges 0
  have hOneAt : star.edge 1 ∈
      GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
    star.edge_mem_incidentEdges 1
  rintro (hSame | hSwap)
  · rcases hLeaf with hLeafLeft | hLeafRight
    · have hValue := hSame _ hZeroAt
      rw [IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeafLeft 0,
        star.right_edge_zero] at hValue
      exact Bool.noConfusion hValue
    · have hValue := hSame _ hOneAt
      rw [IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hLeafRight 1,
        star.right_edge_one] at hValue
      exact Bool.noConfusion hValue
  · rcases hLeaf with hLeafLeft | hLeafRight
    · have hValue := hSwap _ hOneAt
      rw [IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeafLeft 1,
        star.right_edge_one] at hValue
      exact Bool.noConfusion hValue
    · have hValue := hSwap _ hZeroAt
      rw [IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hLeafRight 0,
        star.right_edge_zero] at hValue
      exact Bool.noConfusion hValue

/-- **Two divalent restored endpoints preclude `M⁽¹⁾`.**  At a `T_2` wall the two
star occurrences are restored to opposite endpoints, and the constant assignment
sends them to the same one. -/
theorem no_true_placement_of_divalent
    (twoStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    ¬ Placement hc hab hOne (fun _ ↦ true) := by
  have hNe := IncomingW2TargetPlacement.right_star_ne_of_divalent hc hab hOne twoStar hLeft hRight
  have hZeroAt : twoStar.edge 0 ∈
      GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
    twoStar.edge_mem_incidentEdges 0
  have hOneAt : twoStar.edge 1 ∈
      GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩ :=
    twoStar.edge_mem_incidentEdges 1
  rintro (hSame | hSwap)
  · exact hNe ((hSame _ hZeroAt).trans (hSame _ hOneAt).symm)
  · exact hNe ((hSwap _ hZeroAt).trans (hSwap _ hOneAt).symm)

variable (fullDim : FullDimensionalSourcePresentation data coordinate)

include fullDim

/-- **The trichotomy.**  Every incoming `w2M1k` cover is `T_2` -- in which case
`M⁽²⁾` and `M⁽³⁾` have their placement and `M⁽¹⁾` has none -- or `T_∅` with the
leaf at `a`, or `T_∅` with the leaf at `b` -- in which cases `M⁽¹⁾` has its
placement and the other two have none.  Only the reconstructed target enters; no
source-side census is used. -/
theorem member_trichotomy :
    ((GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 ∧
        Placement hc hab hOne star.right ∧ ¬ Placement hc hab hOne (fun _ ↦ true)) ∨
      ((GluingDatum.incidentEdges a).card = 1 ∧ (GluingDatum.incidentEdges b).card = 3 ∧
        Placement hc hab hOne (fun _ ↦ true) ∧ ¬ Placement hc hab hOne star.right) ∨
      ((GluingDatum.incidentEdges a).card = 3 ∧ (GluingDatum.incidentEdges b).card = 1 ∧
        Placement hc hab hOne (fun _ ↦ true) ∧ ¬ Placement hc hab hOne star.right) := by
  rcases valencySplit_of_twoStar data hc hab hOne fullDim.valid fullDim.changeMinimal star with
    ⟨hLeft, hRight, _, _⟩ | ⟨hLeft, hRight, _, _⟩ | ⟨hLeft, hRight, _, _⟩
  · exact Or.inl ⟨hLeft, hRight, star_placement hc hab hOne star hLeft hRight,
      no_true_placement_of_divalent hc hab hOne star hLeft hRight⟩
  · exact Or.inr (Or.inl ⟨hLeft, hRight,
      true_placement hc hab hOne star (Or.inl hLeft),
      no_star_placement_of_leaf hc hab hOne star (Or.inl hLeft)⟩)
  · exact Or.inr (Or.inr ⟨hLeft, hRight,
      true_placement hc hab hOne star (Or.inr hRight),
      no_star_placement_of_leaf hc hab hOne star (Or.inr hRight)⟩)

/-- **An incoming cover matching `M⁽²⁾` or `M⁽³⁾` is `T_2`.**  The M-1k analogue
of `W2MkkIncomingCensus.divalent_of_member_placement`; unlike there it is *not*
unconditional, because `M⁽¹⁾` is a genuine Base I.a member. -/
theorem divalent_of_star_placement (hPlacement : Placement hc hab hOne star.right) :
    (GluingDatum.incidentEdges a).card = 2 ∧ (GluingDatum.incidentEdges b).card = 2 := by
  rcases member_trichotomy data hc hab hOne star fullDim with
    ⟨hLeft, hRight, _, _⟩ | ⟨_, _, _, hNo⟩ | ⟨_, _, _, hNo⟩
  · exact ⟨hLeft, hRight⟩
  · exact absurd hPlacement hNo
  · exact absurd hPlacement hNo

/-- **An incoming cover matching `M⁽¹⁾` is `T_∅`.** -/
theorem leaf_of_true_placement (twoStar : TwoStar (contract target hab hOne) ⟨a, hab⟩)
    (hPlacement : Placement hc hab hOne (fun _ ↦ true)) :
    (GluingDatum.incidentEdges a).card = 1 ∨ (GluingDatum.incidentEdges b).card = 1 := by
  rcases member_trichotomy data hc hab hOne twoStar fullDim with
    ⟨_, _, _, hNo⟩ | ⟨hLeft, _, _, _⟩ | ⟨_, hRight, _, _⟩
  · exact absurd hPlacement hNo
  · exact Or.inl hLeft
  · exact Or.inr hRight

end Trichotomy


/-! ## §4  The `T_2` orientation: which restored endpoint carries `star.edge 0`

Figure 33 draws `u` as the retained endpoint and `v` as the fresh one, and
`W2M1kSourceCandidates.dividedPattern` / `joinedPattern` fix `leftExternal :=
star.edge 0`, `rightExternal := star.edge 1`.  The incoming cover does not know
that labelling: which of `a`, `b` carries `star.edge 0`'s restored occurrence is
read off the reconstructed side predicate.  Both branches occur, and everything
below is stated so that neither is a hypothesis. -/

section Divalent

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)

/-- The restored endpoint carrying `star.edge 0`'s occurrence -- Figure 33's
retained end `u`. -/
noncomputable def zeroEnd : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true then b else a

/-- The restored endpoint carrying `star.edge 1`'s occurrence -- Figure 33's
fresh end `v`. -/
noncomputable def oneEnd : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true then a else b

@[simp] theorem zeroEnd_of_false
    (hFalse : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false) :
    zeroEnd hc hab hOne star = a := by
  simp only [zeroEnd, hFalse, Bool.false_eq_true, ite_false]

@[simp] theorem oneEnd_of_false
    (hFalse : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false) :
    oneEnd hc hab hOne star = b := by
  simp only [oneEnd, hFalse, Bool.false_eq_true, ite_false]

@[simp] theorem zeroEnd_of_true
    (hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true) :
    zeroEnd hc hab hOne star = b := by
  simp only [zeroEnd, hTrue, ite_true]

@[simp] theorem oneEnd_of_true
    (hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true) :
    oneEnd hc hab hOne star = a := by
  simp only [oneEnd, hTrue, ite_true]

/-- `zeroEnd` and `oneEnd` are the two restored endpoints, in one order or the
other.  Both orders occur. -/
theorem ends_cases :
    (zeroEnd hc hab hOne star = a ∧ oneEnd hc hab hOne star = b) ∨
      (zeroEnd hc hab hOne star = b ∧ oneEnd hc hab hOne star = a) := by
  rcases Bool.eq_false_or_eq_true
    (IncomingTargetExpansion.right hc hab hOne (star.edge 0)) with hTrue | hFalse
  · exact Or.inr ⟨zeroEnd_of_true hc hab hOne star hTrue, oneEnd_of_true hc hab hOne star hTrue⟩
  · exact Or.inl ⟨zeroEnd_of_false hc hab hOne star hFalse,
      oneEnd_of_false hc hab hOne star hFalse⟩

/-- **The `if` of `M11IncomingOuterPartitions.transported_endpointPartitions`,
decided, `T_2` branch.**  Normalization leaves the two expanded ends in place
exactly when `star.edge 0`'s occurrence is restored to `a`. -/
theorem support_iff
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = star.right edge) ↔
      IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false := by
  constructor
  · intro hSupport
    have h := hSupport _ (star.edge_mem_incidentEdges 0)
    rwa [star.right_edge_zero] at h
  · intro hFalse
    have hNe := IncomingW2TargetPlacement.right_star_ne_of_divalent hc hab hOne star hLeft hRight
    have hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 1) = true := by
      rcases Bool.eq_false_or_eq_true
        (IncomingTargetExpansion.right hc hab hOne (star.edge 1)) with h | h
      · exact h
      · exact absurd (hFalse.trans h.symm) hNe
    exact support_of_star_values hc hab hOne star star.right
      (by rw [star.right_edge_zero]; exact hFalse)
      (by rw [star.right_edge_one]; exact hTrue)

/-- **The retained end of `M⁽²⁾` and `M⁽³⁾` restores `zeroEnd`, and its fresh
end restores `oneEnd`** -- in both orientations at once. -/
theorem transported_endpoints
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (hPlacement : Placement hc hab hOne star.right) :
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          star.right hPlacement) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      data.vertexPartition (zeroEnd hc hab hOne star) ∧
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          star.right hPlacement) data).vertexPartition
        (freshVertex (contract target hab hOne)) =
      data.vertexPartition (oneEnd hc hab hOne star) := by
  classical
  have hPair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne
    star.right hPlacement
  by_cases hSupport : ∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = star.right edge
  · have hFalse := (support_iff hc hab hOne star hLeft hRight).mp hSupport
    rw [ite_eq_left hSupport] at hPair
    rw [zeroEnd_of_false hc hab hOne star hFalse, oneEnd_of_false hc hab hOne star hFalse]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
  · have hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true := by
      rcases Bool.eq_false_or_eq_true
        (IncomingTargetExpansion.right hc hab hOne (star.edge 0)) with h | h
      · exact h
      · exact absurd ((support_iff hc hab hOne star hLeft hRight).mpr h) hSupport
    rw [ite_eq_right hSupport] at hPair
    rw [zeroEnd_of_true hc hab hOne star hTrue, oneEnd_of_true hc hab hOne star hTrue]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

/-- Figure 33's flag: the incoming occurrence above `star.edge 0`. -/
noncomputable def flagEdge : target.edges := unfoldEdge hc hab hOne (star.edge 0)

/-- Its partition is the wall datum's `star.edge 0` occurrence partition, on the
nose: `contractDatum` is defined by unfolding. -/
theorem flag_block (sheet : Fin degree) :
    (data.edgePartition (flagEdge hc hab hOne star)).block sheet =
      ((contractDatum data hc hab hOne).edgePartition (star.edge 0)).block sheet := rfl

theorem flagEdge_mem_zeroEnd :
    flagEdge hc hab hOne star ∈
      GluingDatum.incidentEdges (zeroEnd hc hab hOne star) := by
  rcases Bool.eq_false_or_eq_true
    (IncomingTargetExpansion.right hc hab hOne (star.edge 0)) with hTrue | hFalse
  · rw [zeroEnd_of_true hc hab hOne star hTrue]
    exact (IncomingW2TargetPlacement.right_eq_true_iff hc hab hOne _).mp hTrue
  · rw [zeroEnd_of_false hc hab hOne star hFalse]
    exact (IncomingW2TargetPlacement.right_eq_false_iff_of_incident hc hab hOne _
      (star.edge_mem_incidentEdges 0)).mp hFalse

/-- The contracted occurrence meets both restored endpoints, hence `zeroEnd`. -/
theorem contracted_mem_zeroEnd :
    contracted ∈ GluingDatum.incidentEdges (zeroEnd hc hab hOne star) := by
  rcases ends_cases hc hab hOne star with ⟨hZero, _⟩ | ⟨hZero, _⟩
  · rw [hZero]; exact contracted_mem_incidentEdges_left hc
  · rw [hZero]; exact contracted_mem_incidentEdges_right hc

theorem contracted_mem_oneEnd :
    contracted ∈ GluingDatum.incidentEdges (oneEnd hc hab hOne star) := by
  rcases ends_cases hc hab hOne star with ⟨_, hOneE⟩ | ⟨_, hOneE⟩
  · rw [hOneE]; exact contracted_mem_incidentEdges_right hc
  · rw [hOneE]; exact contracted_mem_incidentEdges_left hc

end Divalent


/-! ## §5  The `T_∅` orientation: which restored endpoint is the leaf

`M⁽¹⁾` sends both wall directions to the fresh endpoint, so its retained end --
`TargetExpansion.oldVertex` -- is the monovalent one.  `leafEnd` is the incoming
cover's monovalent restored endpoint and `branchEnd` the trivalent one. -/

section Leaf

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : TwoStar (contract target hab hOne) ⟨a, hab⟩)

/-- The monovalent restored endpoint -- Figure 33's target leaf. -/
noncomputable def leafEnd : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true then a else b

/-- The trivalent restored endpoint. -/
noncomputable def branchEnd : target.V :=
  if IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true then b else a

@[simp] theorem leafEnd_of_true
    (hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true) :
    leafEnd hc hab hOne star = a := by simp only [leafEnd, hTrue, ite_true]

@[simp] theorem branchEnd_of_true
    (hTrue : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true) :
    branchEnd hc hab hOne star = b := by simp only [branchEnd, hTrue, ite_true]

@[simp] theorem leafEnd_of_false
    (hFalse : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false) :
    leafEnd hc hab hOne star = b := by
  simp only [leafEnd, hFalse, Bool.false_eq_true, ite_false]

@[simp] theorem branchEnd_of_false
    (hFalse : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false) :
    branchEnd hc hab hOne star = a := by
  simp only [branchEnd, hFalse, Bool.false_eq_true, ite_false]

theorem leaf_ends_cases :
    (leafEnd hc hab hOne star = a ∧ branchEnd hc hab hOne star = b) ∨
      (leafEnd hc hab hOne star = b ∧ branchEnd hc hab hOne star = a) := by
  rcases Bool.eq_false_or_eq_true
    (IncomingTargetExpansion.right hc hab hOne (star.edge 0)) with hTrue | hFalse
  · exact Or.inl ⟨leafEnd_of_true hc hab hOne star hTrue,
      branchEnd_of_true hc hab hOne star hTrue⟩
  · exact Or.inr ⟨leafEnd_of_false hc hab hOne star hFalse,
      branchEnd_of_false hc hab hOne star hFalse⟩

/-- `leafEnd` really is the monovalent endpoint. -/
theorem leafEnd_card_one (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
    (GluingDatum.incidentEdges b).card = 1) :
    (GluingDatum.incidentEdges (leafEnd hc hab hOne star)).card = 1 := by
  rcases hLeaf with hLeafLeft | hLeafRight
  · rw [leafEnd_of_true hc hab hOne star
      (IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeafLeft 0)]
    exact hLeafLeft
  · rw [leafEnd_of_false hc hab hOne star
      (IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hLeafRight 0)]
    exact hLeafRight

/-- **The `if` of `M11IncomingOuterPartitions.transported_endpointPartitions`,
decided, `T_∅` branch.** -/
theorem leaf_support_iff
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1) :
    (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = true) ↔
      IncomingTargetExpansion.right hc hab hOne (star.edge 0) = true := by
  constructor
  · intro hSupport
    exact hSupport _ (star.edge_mem_incidentEdges 0)
  · intro hTrue
    rcases hLeaf with hLeafLeft | hLeafRight
    · exact support_of_star_values hc hab hOne star (fun _ ↦ true)
        (IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeafLeft 0)
        (IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hLeafLeft 1)
    · rw [IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star
        hLeafRight 0] at hTrue
      exact Bool.noConfusion hTrue

/-- **`M⁽¹⁾`'s retained end restores `leafEnd` and its fresh end restores
`branchEnd`** -- in both orientations at once. -/
theorem leaf_transported_endpoints
    (hLeaf : (GluingDatum.incidentEdges a).card = 1 ∨
      (GluingDatum.incidentEdges b).card = 1)
    (hPlacement : Placement hc hab hOne (fun _ ↦ true)) :
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          (fun _ ↦ true) hPlacement) data).vertexPartition
        (oldVertex (contract target hab hOne) ⟨a, hab⟩) =
      data.vertexPartition (leafEnd hc hab hOne star) ∧
    (GluingTransport.transport (M11IncomingTargetNormalization.incomingIso hc hab hOne
          (fun _ ↦ true) hPlacement) data).vertexPartition
        (freshVertex (contract target hab hOne)) =
      data.vertexPartition (branchEnd hc hab hOne star) := by
  classical
  have hPair := M11IncomingOuterPartitions.transported_endpointPartitions data hc hab hOne
    (fun _ ↦ true) hPlacement
  by_cases hSupport : ∀ edge ∈ GluingDatum.incidentEdges
      (target := contract target hab hOne) ⟨a, hab⟩,
      IncomingTargetExpansion.right hc hab hOne edge = true
  · have hTrue := (leaf_support_iff hc hab hOne star hLeaf).mp hSupport
    rw [ite_eq_left hSupport] at hPair
    rw [leafEnd_of_true hc hab hOne star hTrue, branchEnd_of_true hc hab hOne star hTrue]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩
  · have hFalse : IncomingTargetExpansion.right hc hab hOne (star.edge 0) = false := by
      rcases Bool.eq_false_or_eq_true
        (IncomingTargetExpansion.right hc hab hOne (star.edge 0)) with h | h
      · exact absurd ((leaf_support_iff hc hab hOne star hLeaf).mpr h) hSupport
      · exact h
    rw [ite_eq_right hSupport] at hPair
    rw [leafEnd_of_false hc hab hOne star hFalse, branchEnd_of_false hc hab hOne star hFalse]
    exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

/-- The contracted occurrence meets the leaf endpoint -- it is its only
incidence. -/
theorem contracted_mem_leafEnd :
    contracted ∈ GluingDatum.incidentEdges (leafEnd hc hab hOne star) := by
  rcases leaf_ends_cases hc hab hOne star with ⟨hLeafE, _⟩ | ⟨hLeafE, _⟩
  · rw [hLeafE]; exact contracted_mem_incidentEdges_left hc
  · rw [hLeafE]; exact contracted_mem_incidentEdges_right hc

theorem contracted_mem_branchEnd :
    contracted ∈ GluingDatum.incidentEdges (branchEnd hc hab hOne star) := by
  rcases leaf_ends_cases hc hab hOne star with ⟨_, hBranch⟩ | ⟨_, hBranch⟩
  · rw [hBranch]; exact contracted_mem_incidentEdges_right hc
  · rw [hBranch]; exact contracted_mem_incidentEdges_left hc

end Leaf


/-! ## §6  The `r = 0` background census at a `T_2` wall of Case {w2}

`W3Nd2IncomingBackground.AnyBlock` and `W3Nd2IncomingNormalization.AnyBlock`
state the `{w3-r0}` census at *any* wall block of vanishing local ramification,
with the divalence of one restored endpoint as an explicit hypothesis and no
star arity anywhere.  At a `T_2` wall of Case {w2} **both** endpoints are
divalent, so both orientations apply at once and the census is symmetric.

The `AnyBlock` lemmas have no `T_∅` analogue: each needs one endpoint divalent,
and at Base I.a neither is.  That half is the background census
`W2M1kIncomingMatching.LeafBackgroundCensus`, proved in `W2M1kLeafBackground`. -/

section Background

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  {block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}

/-- The wall datum's own partition at the merged vertex, as a relation identity
at fixed sheets. -/
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

variable (hForest : ContractionForest data a b contracted)

include fullDim hForest

/-- **Every occurrence at the divalent `a` carries `a`'s own block, off the
distinguished class.** -/
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

/-- **`b` carries the whole wall block, off the distinguished class.** -/
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
  have hJoined :=
    (W3Nd2IncomingNormalization.AnyBlock.background_trivalent_joined_of_right_divalent
      data hc hab hOne fullDim hForest hRight
      (hBackground _ (ofSheet_ne_block data hc hab hOne hOff))).2
  have hRel := merged_rel_ofSheet data hc hab hOne sheet
  ext other
  rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
  exact ⟨fun h ↦ (vertexPartition_refines_mergedPartition data a b).rel h,
    fun h ↦ hJoined sheet other hRel (hRel.trans h)⟩

/-- **`hBgEdge` at `zeroEnd`.**  Off the distinguished block every occurrence at
the retained endpoint carries that endpoint's own class. -/
theorem background_edge_block_zeroEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (edge : target.edges)
    (hEdge : edge ∈ GluingDatum.incidentEdges (zeroEnd hc hab hOne star))
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.edgePartition edge).block sheet =
      (data.vertexPartition (zeroEnd hc hab hOne star)).block sheet := by
  rcases ends_cases hc hab hOne star with ⟨hZero, _⟩ | ⟨hZero, _⟩
  · rw [hZero] at hEdge ⊢
    exact background_edge_block_left data hc hab hOne fullDim hForest hBackground hLeft
      edge hEdge sheet hOff
  · rw [hZero] at hEdge ⊢
    exact background_edge_block_right data hc hab hOne fullDim hForest hBackground hRight
      edge hEdge sheet hOff

/-- **`hBgTri` at `oneEnd`.**  Off the distinguished block the fresh endpoint
carries the whole wall block. -/
theorem background_joined_block_oneEnd
    (hBackground : ∀ other : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      other ≠ block → (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ other = 0)
    (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2)
    (sheet : Fin degree) (hOff : ¬ (mergedPartition data a b).Rel block.1 sheet) :
    (data.vertexPartition (oneEnd hc hab hOne star)).block sheet =
      (mergedPartition data a b).block sheet := by
  rcases ends_cases hc hab hOne star with ⟨_, hOneE⟩ | ⟨_, hOneE⟩
  · rw [hOneE]
    exact background_joined_block_right data hc hab hOne fullDim hForest hBackground hLeft
      sheet hOff
  · rw [hOneE]
    exact background_joined_block_left data hc hab hOne fullDim hForest hBackground hRight
      sheet hOff

end Background

end DraismaVargas.LocalCases.W2M1kIncomingCensus
