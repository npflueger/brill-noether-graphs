import DraismaVargasCount.RegrowthWallInput
import DraismaVargasCount.W3FourCountBalance
import DraismaVargasCount.W3ShiftMultiplicityBalance
import DraismaVargasCount.W2M1kIncomingTame
import DraismaVargasCount.W2MkkIncomingDenominator
import DraismaVargasCount.InheritedLimitIncidence
import DraismaVargasCount.W3ShiftSixMemberMultiplicity
import DraismaVargas.LocalCases.NonTrivalentValencyTwoExit

/-!
# Four incoming-member balances at a regrowth

Source: Draisma--Vargas Part I (arXiv:1909.12924), Figures 28, 29, 33, 34 and Equations
(2), (3), (7), (8), read against `prop-signed-mult` of Vargas, Part II
(arXiv:2609.09109).  `RegrowthWallInput` §6 composes five balances at a regrowth's limit
(`w4`, `w3Nd3CoarseFine`, `w3Nd2CoarseFine`, `w2R1`, `w2P`) and `M11StarParityFree` the
sixth (`w2M11`); this file composes the remaining four, so **every one of the ten tags
has its balance at every regrowth, with no hypothesis beyond the tag**.  These balances
are the multiplicity input of the star parity in step 2 of `Assembly`.

## The finding, in one paragraph

No new geometry is needed, but for three of the four tags the recipe of
`RegrowthWallInput.exists_w2P_balance` ("feed the tag's `exists_matched_tracking` into the
balance") does **not** typecheck as stated, because the family Part I identifies the
regrowth's cover in is not literally the family the balance is stated on.
`w3Four`: the identification's family is `W3TrackedCensus`'s anchored Figure 28 family,
whose extra sheets come from the incoming cover's census, while
`W3FourCountBalance.exists_sum_signedMult_eq_zero` builds its own family with the grow
profiles' default extra sheets and both split members over branch-swapped bases.
`w2M1k`: `W2M1kLimitColumns.limitColumns` picks its `LeafPair`/`DividedData` by
`Classical.choice`, while the identified member lives over the census's own pair (at a
leaf endpoint the pair is determined by the incoming sheets).  `w3Shift`: the pair
balance lives over the wall datum the identification returns, which in Position II.a is
the twice-branch-swapped copy of `w.limit`, and it is one of Equation (3)'s three pairs.
The bridge is one observation, `regrowthPresentation`: **every member of every family at
a regrowth's limit that has a stable-incidence dictionary from the limit and the limit's
source genus is presented, at any nonsingular labelling, by the regrowth's own cover** --
`StableGraphFullDimensional.presentationOfEquivalence` from `w.frame.fullDim` along
`InheritedLimitIncidence.stableEquivalence` (the incidence dictionary of the
contraction itself).  Each balance needs one full-dimensional member only to reach a
nonsingular member, and when every perturbed member is singular every term is zero; so the
incoming-member input of the balance is free at a regrowth.  `w2Mkk` composes literally:
its family takes the detach data and the distinguished sheet as parameters.

## What is proved

* **Transport.**  `limit_connected`, `limit_genus`, `limit_sourceGenus`, `expanded_card`,
  `regrowthPresentation` (+ `_labelling`, `rfl`).
* **`w3Shift`.**  `exists_w3Shift_balance` -- one Figure 29 pair
  (`W3ShiftMultiplicityBalance.sum_signedMult_eq_zero`) with the regrowth's own cover as its
  incoming member, matrix `w.frame.matrix`.  `exists_w3Shift_equation3` -- the full
  six-member Equation (3) over `w.limit` (`W3ShiftSixMemberMultiplicity`'s constructed
  family, `sixFamily`), in **every** common coordinate system, and every nonsingular member
  has a full-dimensional presentation in `Fin p`.  `sixMember_labelling_reselect` --
  re-selecting the common coordinates at another member changes nothing.
* **`w2Mkk`.**  `exists_w2Mkk_balance` -- Equation (8) on
  `W2MkkLimitColumns.limitColumns input shape detach (pinSheet profile)`, whose member at the
  returned position is the regrowth's own cover with matrix `w.frame.matrix`, at every
  initial labelling in `Fin p` and in the canonical `Option` coordinates (`mkk_balances`).
  `apply_cast` is the one-line cast lemma it uses.
* **`w2M1k`.**  `exists_w2M1k_balance` -- Equation (7) on `W2M1kLimitColumns.limitColumns`,
  at every initial labelling in `Fin p` and canonically, together with the orientation
  (`alignedOrientation` at a `LeafPair` or `separatedOrientation` at a `DividedData`) and
  position at which the regrowth's own cover is a member, with matrix `w.frame.matrix`.
  `m1k_sum_signedMult_eq_zero_of_source`, `m1k_balances` -- Equation (7) on the
  `limitColumns` family from any member-shaped full-dimensional source with a dictionary
  from the wall datum.
* **`w3Four`.**  `exists_w3Four_balance` -- Equation (2) on `W3FourCountBalance`'s own
  family, with every nonsingular member presented in `Fin p`.  The root and its three
  `TargetBranchRegion.edgeMoved` receipts are derived from the classification
  (`TargetSeparation.farEndpoint` at the `other` direction, the wall's connectedness and
  genus zero), exactly as `InteriorBridgesTrivalent.exists_four_matched_tracking_of_classification`
  derives them.

## What is NOT proved here

* **Nothing about any star.**  The four families are Part I's; nothing here identifies
  them with star classes, and no `FamilyStarParity` clause is proved (the star censuses
  are the modules `W3FourStarCensusProof`, `W2M1kStarCensusProof`, and so on).
* **`w3Four`: the regrowth's cover is not shown to be a member of the balance's family.**
  It is a member of the anchored family (different extra sheets); the balance's family is
  reached only by transport through the wall datum's dictionaries.  A star census wanting
  the cover *as* a balance member must either identify the two families or prove the
  balance on the anchored one.
* **`w3Shift` pair version: the pair's wall datum is not related to `w.limit`** in the
  statement (it is `w.limit` or `W3ShiftClosure.clearPairData` of it, inside the proof of
  `InteriorBridgesTrivalent.exists_shift_matched_tracking_of_classification`, and not
  exported).  The six-member version has no such gap.
* **`w2M1k`: the orientation carrying the cover is not identified with `limitColumns`**
  (a chosen pair); the balance on `limitColumns` is reached by transport.
* **No concrete regrowth carrying any of the four tags is constructed here.**  The
  theorems have no hypothesis beyond the tag, so there is no hypothesis package to
  inhabit; whether each tag occurs at genus six is not examined here (in computer
  experiments with genus-six walls, `w3Shift` and `w2Mkk` walls were not observed).
* The canonical (`Option`-coordinate) forms use local classical `DecidableEq` instances,
  mirroring the Part I files; the `Fin p` forms have no such dependence.

## Three tempting inferences, checked

* (i) *"Each is composition plus bookkeeping."*  **Half true**: no new geometry, but not
  the recipe of `exists_w2P_balance` for `w3Four`, `w2M1k` or the full `w3Shift`
  Equation (3): the identified member and the balance's family differ (paragraph above),
  bridged by `regrowthPresentation` / dictionary transport and the singular case split.
* (ii) *"The w3Four root receipts are in the classification"*: **not** in the
  classification's payload and not returned by `W3FourArbitraryExit`, but **derivable**
  from the `four` constructor alone plus the wall's connectedness and genus zero
  (`TargetSeparation.farEndpoint_ne`, `edgeMoved_eq_false`, `edgeMoved_self_eq_true`).
* (iii) *"The w2Mkk detach data are in the tracking payload"*: **not** in
  `W2MkkGraphTracking.exists_w2Mkk_payload`'s output, but
  `W2MkkSourceCandidates.exists_detachData` supplies one from the shape, and **any**
  choice works because both the family and the identification take it as a parameter.

## Consumers

The star censuses of the `w3Four`, `w3Shift`, `w2M1k` and `w2Mkk` walls, feeding
`RegrowthWallInput.FamilyStarParity` (step 2 of `Assembly`).
-/

namespace DraismaVargas.Count.RegrowthBalances

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction
open ClassifiedContinuation (SourceCase)
open WallStar (Regrowth Nondegenerate)
open W4WallExhaustion (mergeVertex)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-- The limit target of a regrowth is connected. -/
theorem limit_connected (w : Regrowth core y degree) :
    graph_connected (w.frame.limitTarget w.column) :=
  graph_connected_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column) w.frame.fullDim.targetConnected

/-- The limit target of a regrowth has genus zero. -/
theorem limit_genus (w : Regrowth core y degree) :
    genus (w.frame.limitTarget w.column) = 0 :=
  (genus_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
    (w.frame.numEdges_edgeOf w.column)).trans w.frame.fullDim.targetGenus

/-! ## The regrowth's own cover as a source for every member of a family at its limit -/

section Transport

/-- The limit's source genus is the regrowth's: the contraction is a forest. -/
theorem limit_sourceGenus (w : Regrowth core y degree) (hy : Nondegenerate y) :
    genus w.limit.sourceGraph = genus w.frame.data.sourceGraph :=
  NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum w.frame.data rfl
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
    (InheritedLimitRows.forest w hy)

/-- An expanded target at the limit has as many edges as the regrowth's own target. -/
theorem expanded_card (w : Regrowth core y degree)
    (right : (w.frame.limitTarget w.column).edges → Bool) :
    (TargetExpansion.graph (w.frame.limitTarget w.column) (mergeVertex w) right).edges.card =
      w.frame.target.edges.card := by
  rw [TargetExpansion.graph_edge_card]
  have hContract := GraphContraction.card_edges_contract (G := w.frame.target)
    (fst_ne_snd (w.frame.edgeOf w.column)) (w.frame.numEdges_edgeOf w.column)
  have hPos : 0 < Multiset.card w.frame.target.edges :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨_, Multiset.coe_mem (x := w.frame.edgeOf w.column)⟩
  have h : (w.frame.limitTarget w.column).edges.card = w.frame.target.edges.card - 1 :=
    hContract
  omega

/-- **The regrowth's own cover presents every nonsingular member of every family at its
limit.**  Any datum over an expanded limit target with a stable-incidence dictionary from
the limit and the limit's source genus, and any nonsingular labelling of it, is a
full-dimensional presentation: `StableGraphFullDimensional.presentationOfEquivalence`
from the regrowth's own frame (`w.frame.fullDim`) along
`InheritedLimitIncidence.stableEquivalence` followed by the dictionary. -/
noncomputable def regrowthPresentation (w : Regrowth core y degree) (hy : Nondegenerate y)
    {right : (w.frame.limitTarget w.column).edges → Bool}
    {D : GluingDatum (TargetExpansion.graph (w.frame.limitTarget w.column) (mergeVertex w) right)
      degree}
    (dictionary : StableGraphIncidence.Equivalence w.limit D) (hValid : D.Valid)
    (hSourceGenus : genus D.sourceGraph = genus w.limit.sourceGraph)
    (labelling : W4StableSource.StableLengthMatrixLabelling D (Fin p))
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    FullDimensionalSource.FullDimensionalSourcePresentation D (Fin p) :=
  StableGraphFullDimensional.presentationOfEquivalence w.frame.fullDim
    ((InheritedLimitIncidence.stableEquivalence w hy).trans dictionary) hValid
    (W3FourStableIncidence.expanded_targetConnected (limit_connected w) right)
    (W3FourStableIncidence.expanded_targetGenus (limit_genus w) right)
    (expanded_card w right) (hSourceGenus.trans (limit_sourceGenus w hy)) labelling hDet

@[simp] theorem regrowthPresentation_labelling (w : Regrowth core y degree)
    (hy : Nondegenerate y) {right : (w.frame.limitTarget w.column).edges → Bool}
    {D : GluingDatum (TargetExpansion.graph (w.frame.limitTarget w.column) (mergeVertex w) right)
      degree}
    (dictionary : StableGraphIncidence.Equivalence w.limit D) (hValid : D.Valid)
    (hSourceGenus : genus D.sourceGraph = genus w.limit.sourceGraph)
    (labelling : W4StableSource.StableLengthMatrixLabelling D (Fin p))
    (hDet : (GluingDatum.LengthMatrixPresentation.matrix labelling.presentation).det ≠ 0) :
    (regrowthPresentation w hy dictionary hValid hSourceGenus labelling hDet).labelling =
      labelling := rfl

end Transport

section Shift

open W3ShiftSourceCandidates

/-- **One Figure 29 pair of Equation (3) at every regrowth tagged `w3Shift`**
(`W3ShiftMultiplicityBalance.sum_signedMult_eq_zero`), with the pair's incoming member the
regrowth's own cover: `InteriorBridgesTrivalent.exists_shift_matched_tracking_of_classification`
identifies it as `shiftMembers shrink incoming` with the regrowth's own matrix.  The pair
lives over the wall datum that identification returns -- `w.limit` itself in Position II.b,
its twice-branch-swapped gauge copy in Position II.a -- and the relation between the two is
not exported by the identification; `exists_w3Shift_equation3` is the full six-member
Equation (3) over `w.limit` itself. -/
theorem exists_w3Shift_balance (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w3Shift) :
    ∃ (star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (wallDatum : GluingDatum (w.frame.limitTarget w.column) degree)
      (input : ThirdEquation.W3SourceInput wallDatum star)
      (shift : ShiftProfile input) (shrink : ShrinkData shift) (incoming : Fin 2)
      (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
        (W3ShiftLimitRows.shiftMembers shrink incoming).datum (Fin p)),
      GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
          w.frame.matrix ∧
        ∑ position : Fin 2, signedMult (W3ShiftStableIncidence.outgoingLabelling shrink
          input.valid incoming incomingFD position).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w2 _ _ profile => cases profile <;> cases htag
  | w3 star input profile =>
    obtain ⟨wallDatum, wallInput, shift, shrink, index, fd, hMatrix, -, -⟩ :=
      InteriorBridgesTrivalent.exists_shift_matched_tracking_of_classification w.frame.data
        (InteriorProgress.hc_column w.frame.fullDim w.column)
        (InteriorProgress.hab_column w.frame.fullDim w.column)
        (InteriorProgress.hOne_column w.frame.fullDim w.column) w.frame.fullDim
        (InheritedLimitRows.forest w hy) (InheritedLimitRows.danglingCompatible w hy) star input
        (InteriorGraphTracking.Tracks.self w.frame.fullDim) profile htag
    exact ⟨star, wallDatum, wallInput, shift, shrink, index, fd, hMatrix,
      W3ShiftMultiplicityBalance.sum_signedMult_eq_zero shrink wallInput.valid index fd⟩

/-- **Re-selecting the six-member coordinates at another member changes nothing**: the
common coordinates read off member `i`'s own labelling in the coordinates selected at
`selected` are those same coordinates. -/
theorem sixMember_labelling_reselect {target : CFGraph} {wall : target.V}
    {data : GluingDatum target degree} {star : ThirdEquation.ThreeStar target wall}
    {input : ThirdEquation.W3SourceInput data star} {shifts : Fin 3 → ShiftProfile input}
    (pairs : ∀ direction, W3ShiftSixMemberBalance.PairPackage (shifts direction))
    {coordinate : Type*} (selected i j : W3ShiftSixMemberMatrices.MemberIndex)
    (initial : W4StableSource.StableLengthMatrixLabelling
      (W3ShiftSixMemberMatrices.member pairs selected).datum coordinate) :
    W3ShiftSixMemberMatrices.labelling pairs i
        (W3ShiftSixMemberMatrices.labelling pairs selected initial i) j =
      W3ShiftSixMemberMatrices.labelling pairs selected initial j := by
  unfold W3ShiftSixMemberMatrices.labelling
  congr 1 <;> ext x <;>
    simp [W3ShiftSixMemberMatrices.sourceCoordinates,
      W3ShiftSixMemberMatrices.targetCoordinates]

/-- The constructed six-member family of Equation (3) at a regrowth's limit. -/
noncomputable abbrev sixFamily (w : Regrowth core y degree)
    {star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (mergeVertex w)}
    {input : ThirdEquation.W3SourceInput w.limit star}
    (profile : W3R1SourceProfile.Nd3Profile w.limit
      (ThirdEquation.W3SourceInput.distinguishedBlock input))
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : w.limit.sourceEdgeIndex profile.largest.1 <
      (w.limit.vertexPartition (mergeVertex w)).blockCard
        (ThirdEquation.W3SourceInput.distinguishedBlock input).1) :
    ∀ direction : Fin 3, W3ShiftSixMemberBalance.PairPackage
      (W3ShiftSixMemberBalance.orientation profile directions largest_lt direction) :=
  W3ShiftSixMemberMultiplicity.constructedPackages profile directions largest_lt
    (limit_connected w) (limit_genus w)

/-- **Equation (3), all six members, at every regrowth tagged `w3Shift`.**  The family is
the constructed six-member family over the regrowth's own limit
(`W3ShiftSixMemberMultiplicity.constructedPackages`), and the balance holds in **every**
common coordinate system of it, selected at any member with any labelling in the
regrowth's own `Fin p` coordinates.  The one full-dimensional member the balance
needs is produced from the regrowth's own cover (`regrowthPresentation`) at a nonsingular
member; if every member is singular every term is zero. -/
theorem exists_w3Shift_equation3 (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w3Shift) :
    ∃ (star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : ThirdEquation.W3SourceInput w.limit star)
      (profile : W3R1SourceProfile.Nd3Profile w.limit
        (ThirdEquation.W3SourceInput.distinguishedBlock input))
      (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
      (largest_lt : w.limit.sourceEdgeIndex profile.largest.1 <
        (w.limit.vertexPartition (mergeVertex w)).blockCard
          (ThirdEquation.W3SourceInput.distinguishedBlock input).1),
      (∀ (selected i : W3ShiftSixMemberMatrices.MemberIndex)
          (initial : W4StableSource.StableLengthMatrixLabelling
            (W3ShiftSixMemberMatrices.member (sixFamily w profile directions largest_lt)
              selected).datum (Fin p)),
          (W3ShiftSixMemberMatrices.squareMatrix (sixFamily w profile directions largest_lt)
            selected initial i).det ≠ 0 →
          Nonempty (FullDimensionalSource.FullDimensionalSourcePresentation
            (W3ShiftSixMemberMatrices.member (sixFamily w profile directions largest_lt)
              i).datum (Fin p))) ∧
      ∀ (selected : W3ShiftSixMemberMatrices.MemberIndex)
        (initial : W4StableSource.StableLengthMatrixLabelling
          (W3ShiftSixMemberMatrices.member (sixFamily w profile directions largest_lt)
            selected).datum (Fin p)),
        ∑ i : W3ShiftSixMemberMatrices.MemberIndex, signedMult
          (W3ShiftSixMemberMatrices.labelling (sixFamily w profile directions largest_lt)
            selected initial i).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w2 _ _ profile => cases profile <;> cases htag
  | w3 star input classification =>
    cases classification with
    | four => cases htag
    | nd3CoarseFine => cases htag
    | nd2CoarseFine => cases htag
    | shift profile directions largest_lt _ =>
      let pairs := sixFamily w profile directions largest_lt
      let fdAt : ∀ (selected i : W3ShiftSixMemberMatrices.MemberIndex)
          (initial : W4StableSource.StableLengthMatrixLabelling
            (W3ShiftSixMemberMatrices.member pairs selected).datum (Fin p)),
          (W3ShiftSixMemberMatrices.squareMatrix pairs selected initial i).det ≠ 0 →
          FullDimensionalSource.FullDimensionalSourcePresentation
            (W3ShiftSixMemberMatrices.member pairs i).datum (Fin p) :=
        fun selected i initial hDet ↦ regrowthPresentation w hy
          (W3ShiftSixMemberMatrices.memberIncidence pairs i)
          ((W3ShiftSixMemberMatrices.member pairs i).datum_valid (pairs i.1).gaugeInput.valid)
          (W3ShiftSixMemberMultiplicity.member_sourceGenus pairs i)
          (W3ShiftSixMemberMatrices.labelling pairs selected initial i) hDet
      refine ⟨star, input, profile, directions, largest_lt,
        fun selected i initial hDet ↦ ⟨fdAt selected i initial hDet⟩,
        fun selected initial ↦ ?_⟩
      by_cases hSome :
          ∃ i, (W3ShiftSixMemberMatrices.squareMatrix pairs selected initial i).det ≠ 0
      · obtain ⟨i, hDet⟩ := hSome
        have h := W3ShiftSixMemberMultiplicity.sum_signedMult_eq_zero pairs (limit_connected w)
          (limit_genus w) i (fdAt selected i initial hDet)
        have hReselect : ∀ j, W3ShiftSixMemberMatrices.labelling pairs i
            (fdAt selected i initial hDet).labelling j =
              W3ShiftSixMemberMatrices.labelling pairs selected initial j :=
          fun j ↦ sixMember_labelling_reselect pairs selected i j initial
        rw [← h]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [hReselect j]
      · push Not at hSome
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        change _ * (W3ShiftSixMemberMatrices.squareMatrix pairs selected initial i).det = 0
        rw [hSome i, mul_zero]

end Shift

/-- Reading a function of a dependent datum across an equality of the index. -/
theorem apply_cast {α : Sort*} {F : α → Sort*} {β : Sort*} (g : ∀ a, F a → β) {a b : α}
    (h : a = b) (x : F a) : g b (h ▸ x) = g a x := by
  subst h; rfl

section Mkk

open W2MkkSourceCandidates W2MkkLimitColumns

/-- The canonical coordinate order of `W2MkkIncomingDenominator` is stated with a
classical decision procedure on `Option target.edges`. -/
noncomputable local instance instDecidableEqOptionEdgesMkk {target : CFGraph} :
    DecidableEq (Option target.edges) := Classical.decEq _

/-- Both forms of Equation (8) on the `limitColumns` family, from a full-dimensional presentation
of one of its members in `Fin p` coordinates: at every initial labelling in those
coordinates (`W2MkkIncomingDenominator.sum_signedMult_eq_zero`), and in the canonical
coordinates (`sum_signedMult_canonical_eq_zero`, the member moved to `Option`
coordinates by `A04MoreTags.reindexFullDim` along its own column dictionary). -/
theorem mkk_balances {target : CFGraph.{0}} {wall : target.V}
    {data : GluingDatum target degree} {star : W2R1Target.TwoStar target wall}
    {block : W4Assembly.WallBlock data wall}
    {profile : W2R2SourceProfile.SourceProfile data star block}
    (input : SecondEquation.W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (distinguished : Fin degree)
    (hConnected : graph_connected target) (hGenus : genus target = 0) (incoming : Fin 3)
    (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
      ((limitColumns input shape detach distinguished hConnected hGenus).member incoming).datum
        (Fin p)) :
    (∀ initial : W4StableSource.StableLengthMatrixLabelling
        ((limitColumns input shape detach distinguished hConnected hGenus).member 0).datum
          (Fin p),
      ∑ position : Fin 3, signedMult
        ((limitColumns input shape detach distinguished hConnected hGenus).labelling initial
          position).presentation = 0) ∧
      ∑ position : Fin 3, signedMult
        ((limitColumns input shape detach distinguished hConnected hGenus).labelling
          ((limitColumns input shape detach distinguished hConnected
            hGenus).canonicalInitialLabelling input) position).presentation = 0 :=
  ⟨fun initial ↦ W2MkkIncomingDenominator.sum_signedMult_eq_zero input shape detach
      distinguished hConnected hGenus incoming initial incomingFD,
    W2MkkIncomingDenominator.sum_signedMult_canonical_eq_zero input shape detach distinguished
      hConnected hGenus incoming (A04MoreTags.reindexFullDim
        ((TargetExpansion.occurrenceEquiv target wall
          ((limitColumns input shape detach distinguished hConnected hGenus).member
            incoming).right).trans incomingFD.labelling.targetEdge.symm) incomingFD)⟩

/-- **Equation (8) at every regrowth tagged `w2Mkk`.**  The `mkk` payload
(`W2MkkGraphTracking.exists_w2Mkk_payload`) gives the profile, shape and `r = 0`
background; the detach data is any partner of the pinned sheet
(`W2MkkSourceCandidates.exists_detachData` -- the family and the identification both take
it as a parameter, so no choice has to agree with another); the distinguished sheet of
`M⁽³⁾` is the pinned sheet.  Part I identifies the regrowth's own cover as
`W2MkkIncomingMatching.members … position` (`W2MkkGraphTracking.exists_matched_tracking`),
which is literally the family's position `0` or `1` (by the datum's orientation) or `2`. -/
theorem exists_w2Mkk_balance (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w2Mkk) :
    ∃ (star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : SecondEquation.W2SourceInput w.limit star)
      (block : W4Assembly.WallBlock w.limit (mergeVertex w))
      (profile : W2R2SourceProfile.SourceProfile w.limit star block)
      (shape : Shape profile) (detach : DetachData profile) (distinguished : Fin degree)
      (incoming : Fin 3)
      (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
        ((limitColumns input shape detach distinguished (limit_connected w)
          (limit_genus w)).member incoming).datum (Fin p)),
      GluingDatum.LengthMatrixPresentation.matrix incomingFD.labelling.presentation =
          w.frame.matrix ∧
        (∀ initial : W4StableSource.StableLengthMatrixLabelling
            ((limitColumns input shape detach distinguished
              (limit_connected w) (limit_genus w)).member 0).datum (Fin p),
          ∑ position : Fin 3, signedMult
            ((limitColumns input shape detach distinguished
              (limit_connected w) (limit_genus w)).labelling initial position).presentation =
            0) ∧
        ∑ position : Fin 3, signedMult
          ((limitColumns input shape detach distinguished (limit_connected w)
            (limit_genus w)).labelling
            ((limitColumns input shape detach distinguished (limit_connected w)
              (limit_genus w)).canonicalInitialLabelling input) position).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w3 _ _ profile => cases profile <;> cases htag
  | w2 star input profile =>
    have hForest := InheritedLimitRows.forest w hy
    have hc := InteriorProgress.hc_column w.frame.fullDim w.column
    have hab := InteriorProgress.hab_column w.frame.fullDim w.column
    have hOne := InteriorProgress.hOne_column w.frame.fullDim w.column
    obtain ⟨block, wallProfile, wallShape, hBackground⟩ :=
      W2MkkGraphTracking.exists_w2Mkk_payload w.frame.data hc hab hOne star input profile htag
    obtain ⟨detach⟩ := exists_detachData wallShape
    have hEnds := W2MkkSelectedCensus.divalent_endpoints w.frame.data hc hab hOne
      w.frame.fullDim wallProfile wallShape
    obtain ⟨position, fd, hMatrix, -, -⟩ :=
      W2MkkGraphTracking.exists_matched_tracking w.frame.data hc hab hOne w.frame.fullDim
        hForest input wallProfile hBackground hEnds.1 hEnds.2.1 wallShape detach
        (pinSheet wallProfile)
        (W2MkkSelectedCensus.selectedCensus_dichotomy w.frame.data hc hab hOne w.frame.fullDim
          hForest wallProfile wallShape detach hBackground)
        (InteriorGraphTracking.Tracks.self w.frame.fullDim)
    let L := limitColumns input wallShape detach (pinSheet wallProfile) (limit_connected w)
      (limit_genus w)
    let F : W2MkkCommonBalance.LimitMember w.limit (mergeVertex w) → Type :=
      fun m ↦ FullDimensionalSource.FullDimensionalSourcePresentation m.datum (Fin p)
    let g : ∀ m, F m → Matrix (Fin p) (Fin p) ℚ :=
      fun _ fd ↦ GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation
    have hIncoming : ∃ (incoming : Fin 3) (fd' : F (L.member incoming)),
        g _ fd' = w.frame.matrix := by
      match position with
      | 0 =>
        by_cases hPin : (endpointPartition wallProfile).Rel (firstSheet wallProfile)
            (pinSheet wallProfile)
        · have h := (limitColumns_member_zero_of_first input wallShape detach
            (pinSheet wallProfile) (limit_connected w) (limit_genus w) hPin).symm
          exact ⟨0, h ▸ fd, (apply_cast g h fd).trans hMatrix⟩
        · have h := (limitColumns_member_one_of_second input wallShape detach
            (pinSheet wallProfile) (limit_connected w) (limit_genus w) hPin
            ((pinSheet_mem wallShape).resolve_left hPin)).symm
          exact ⟨1, h ▸ fd, (apply_cast g h fd).trans hMatrix⟩
      | 1 =>
        have h := (limitColumns_member_two input wallShape detach (pinSheet wallProfile)
          (limit_connected w) (limit_genus w)).symm
        exact ⟨2, h ▸ fd, (apply_cast g h fd).trans hMatrix⟩
    obtain ⟨incoming, fd', hMatrix'⟩ := hIncoming
    exact ⟨star, input, block, wallProfile, wallShape, detach, pinSheet wallProfile, incoming,
      fd', hMatrix', mkk_balances input wallShape detach (pinSheet wallProfile)
        (limit_connected w) (limit_genus w) incoming fd'⟩

end Mkk

section M1k

open W2M1kSourceCandidates W2M1kLimitColumns

/-- **Equation (7) on the `limitColumns` family from any member-shaped source.**  If some datum
over an expanded target has a full-dimensional presentation and a stable-incidence
dictionary from the wall datum with the wall's source genus, Equation (7) holds on
`W2M1kLimitColumns.limitColumns`: at a nonsingular perturbed position the source is
transported there (`W2M1kStableIncidence.outgoingPresentation`, the two dictionaries
composed through the wall datum) and `W2M1kIncomingTame.sum_signedMult_eq_zero` applies;
if both perturbed positions are singular,
`W2M1kMemberBalance.sum_signedMult_eq_zero_of_conditional` needs no denominator at all. -/
theorem m1k_sum_signedMult_eq_zero_of_source {target : CFGraph.{0}} {wall : target.V}
    {data : GluingDatum target degree} {star : W2R1Target.TwoStar target wall}
    {block : W4Assembly.WallBlock data wall}
    {profile : W2R2SourceProfile.SourceProfile data star block}
    (input : SecondEquation.W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (initial : W4StableSource.StableLengthMatrixLabelling
      ((limitColumns input shape hConnected hGenus).member 0).datum coordinate)
    {sourceRight : target.edges → Bool}
    {sourceDatum : GluingDatum (TargetExpansion.graph target wall sourceRight) degree}
    (dictionary : StableGraphIncidence.Equivalence data sourceDatum)
    (hSourceGenus : genus sourceDatum.sourceGraph = genus data.sourceGraph)
    (sourceFD : FullDimensionalSource.FullDimensionalSourcePresentation sourceDatum coordinate) :
    ∑ position : Fin 3, signedMult
      ((limitColumns input shape hConnected hGenus).labelling initial position).presentation =
        0 := by
  let L := limitColumns input shape hConnected hGenus
  have fdAt : ∀ j, (L.squareMatrix initial j).det ≠ 0 →
      FullDimensionalSource.FullDimensionalSourcePresentation (L.member j).datum coordinate :=
    fun j hDet ↦ W2M1kStableIncidence.outgoingPresentation (data := data)
      (dictionary.symm.trans
        (W2M1kMemberBalance.limitDictionary input shape hConnected hGenus j))
      ((L.member j).valid_of_old input.valid) hConnected hGenus hSourceGenus
      (W2M1kMemberBalance.limitMemberGenus input shape hConnected hGenus j) sourceFD
      (L.labelling initial j) hDet
  by_cases h1 : (L.squareMatrix initial 1).det = 0
  · by_cases h2 : (L.squareMatrix initial 2).det = 0
    · exact W2M1kMemberBalance.sum_signedMult_eq_zero_of_conditional input L initial
        (TrivalentWeight.leafCount_member_zero input shape hConnected hGenus)
        (TrivalentWeight.leafCount_member_one input shape hConnected hGenus)
        (TrivalentWeight.leafCount_member_two input shape hConnected hGenus)
        (fun h ↦ (h h1).elim) (fun h ↦ (h h2).elim)
    · exact W2M1kIncomingTame.sum_signedMult_eq_zero input shape hConnected hGenus 2 initial
        (fdAt 2 h2)
  · exact W2M1kIncomingTame.sum_signedMult_eq_zero input shape hConnected hGenus 1 initial
      (fdAt 1 h1)

/-- The canonical coordinate order of the divalent balances of Part I is stated with a
classical decision procedure on `Option target.edges`. -/
noncomputable local instance instDecidableEqOptionEdges {target : CFGraph} :
    DecidableEq (Option target.edges) := Classical.decEq _

/-- Both forms of Equation (7) on the `limitColumns` family -- in the source's own coordinates
at every initial labelling, and in the canonical coordinates -- from one member-shaped
full-dimensional source in `Fin p` coordinates (moved to `Option` coordinates by
`A04MoreTags.reindexFullDim` along the source's own column dictionary). -/
theorem m1k_balances {target : CFGraph.{0}} {wall : target.V}
    {data : GluingDatum target degree} {star : W2R1Target.TwoStar target wall}
    {block : W4Assembly.WallBlock data wall}
    {profile : W2R2SourceProfile.SourceProfile data star block}
    (input : SecondEquation.W2SourceInput data star) (shape : Shape profile)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    {sourceRight : target.edges → Bool}
    {sourceDatum : GluingDatum (TargetExpansion.graph target wall sourceRight) degree}
    (dictionary : StableGraphIncidence.Equivalence data sourceDatum)
    (hSourceGenus : genus sourceDatum.sourceGraph = genus data.sourceGraph)
    (sourceFD : FullDimensionalSource.FullDimensionalSourcePresentation sourceDatum (Fin p)) :
    (∀ initial : W4StableSource.StableLengthMatrixLabelling
        ((limitColumns input shape hConnected hGenus).member 0).datum (Fin p),
      ∑ position : Fin 3, signedMult
        ((limitColumns input shape hConnected hGenus).labelling initial position).presentation =
          0) ∧
      ∑ position : Fin 3, signedMult
        ((limitColumns input shape hConnected hGenus).labelling
          ((limitColumns input shape hConnected hGenus).canonicalInitialLabelling input)
            position).presentation = 0 :=
  ⟨fun initial ↦ m1k_sum_signedMult_eq_zero_of_source input shape hConnected hGenus initial
      dictionary hSourceGenus sourceFD,
    m1k_sum_signedMult_eq_zero_of_source input shape hConnected hGenus _ dictionary
      hSourceGenus (A04MoreTags.reindexFullDim
        ((TargetExpansion.occurrenceEquiv target wall sourceRight).trans
          sourceFD.labelling.targetEdge.symm) sourceFD)⟩

/-- **Equation (7) at every regrowth tagged `w2M1k`.** -/
theorem exists_w2M1k_balance (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w2M1k) :
    ∃ (star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : SecondEquation.W2SourceInput w.limit star)
      (block : W4Assembly.WallBlock w.limit (mergeVertex w))
      (profile : W2R2SourceProfile.SourceProfile w.limit star block)
      (shape : Shape profile) (orientation : W2M1kCommonBalance.LimitColumns profile shape)
      (_ : (∃ pair : LeafPair profile,
          orientation = alignedOrientation input shape pair (limit_connected w)
            (limit_genus w)) ∨
        (∃ divided : DividedData profile,
          orientation = separatedOrientation input shape divided (limit_connected w)
            (limit_genus w)))
      (source : Fin 3)
      (sourceFD : FullDimensionalSource.FullDimensionalSourcePresentation
        (orientation.member source).datum (Fin p)),
      GluingDatum.LengthMatrixPresentation.matrix sourceFD.labelling.presentation =
          w.frame.matrix ∧
        (∀ initial : W4StableSource.StableLengthMatrixLabelling
            ((limitColumns input shape (limit_connected w) (limit_genus w)).member 0).datum
              (Fin p),
          ∑ position : Fin 3, signedMult
            ((limitColumns input shape (limit_connected w) (limit_genus w)).labelling initial
              position).presentation = 0) ∧
        ∑ position : Fin 3, signedMult
          ((limitColumns input shape (limit_connected w) (limit_genus w)).labelling
            ((limitColumns input shape (limit_connected w)
              (limit_genus w)).canonicalInitialLabelling input) position).presentation = 0 := by
  cases cls with
  | w4 => cases htag
  | w3 _ _ profile => cases profile <;> cases htag
  | w2 star input profile =>
    have hForest := InheritedLimitRows.forest w hy
    have hc := InteriorProgress.hc_column w.frame.fullDim w.column
    have hab := InteriorProgress.hab_column w.frame.fullDim w.column
    have hOne := InteriorProgress.hOne_column w.frame.fullDim w.column
    have hC := limit_connected w
    have hG := limit_genus w
    obtain ⟨block, wallProfile, ⟨wallShape⟩⟩ :=
      W2M1kGraphTracking.exists_w2M1k_payload w.frame.data hc hab hOne star input profile htag
    rcases W2M1kClosureUnconditional.headline_cases w.frame.data hc hab hOne w.frame.fullDim
        wallProfile wallShape with
      ⟨-, hLeaf⟩ | ⟨⟨pair⟩, hLeftCard, hRightCard⟩ | ⟨⟨divided⟩, hLeftCard, hRightCard⟩
    · obtain ⟨pair, selected⟩ := W2M1kSelectedCensus.exists_selectedCensus_leaf w.frame.data
        hc hab hOne w.frame.fullDim wallProfile wallShape hLeaf
      obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.leaf_sameBlocks w.frame.data
        hc hab hOne w.frame.fullDim input wallProfile wallShape pair hLeaf selected
        (W2M1kLeafBackground.leafBackgroundCensus w.frame.data hc hab hOne w.frame.fullDim
          hForest input wallProfile hLeaf)
      obtain ⟨fd, hMatrix, -, -⟩ :=
        W2M1kGraphTracking.exists_matched_tracking w.frame.data hc hab hOne w.frame.fullDim
          (LeafPair.candidate input wallShape pair)
          (W2M1kIncomingMatching.leafPlacement w.frame.data hc hab hOne input wallProfile
            wallShape pair hLeaf)
          hVertices hEdges (InteriorGraphTracking.Tracks.self w.frame.fullDim)
      exact ⟨star, input, block, wallProfile, wallShape, _, Or.inl ⟨pair, rfl⟩, 0, fd, hMatrix,
        m1k_balances input wallShape hC hG
          (W2M1kGaugeFamily.alignedDictionary input wallShape pair hC hG 0)
          (W2M1kGaugeFamily.alignedMemberGenus input wallShape pair hC hG 0) fd⟩
    · obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.joined_sameBlocks w.frame.data
        hc hab hOne w.frame.fullDim hForest input wallProfile
        (W2M1kClosureUnconditional.wall_background w.frame.data hc hab hOne input wallProfile)
        hLeftCard hRightCard (pair.geometry wallShape)
        (W2M1kSelectedCensus.selectedCensus_of_aligned w.frame.data hc hab hOne w.frame.fullDim
          hForest wallProfile wallShape pair.aligned hLeftCard hRightCard)
      obtain ⟨fd, hMatrix, -, -⟩ :=
        W2M1kGraphTracking.exists_matched_tracking w.frame.data hc hab hOne w.frame.fullDim
          (joinedCandidate star (pair.geometry wallShape))
          (W2M1kIncomingMatching.joinedPlacement w.frame.data hc hab hOne
            (pair.geometry wallShape) hLeftCard hRightCard)
          hVertices hEdges (InteriorGraphTracking.Tracks.self w.frame.fullDim)
      exact ⟨star, input, block, wallProfile, wallShape, _, Or.inl ⟨pair, rfl⟩, 2, fd, hMatrix,
        m1k_balances input wallShape hC hG
          (W2M1kGaugeFamily.alignedDictionary input wallShape pair hC hG 2)
          (W2M1kGaugeFamily.alignedMemberGenus input wallShape pair hC hG 2) fd⟩
    · have hBackground := W2M1kClosureUnconditional.wall_background w.frame.data hc hab hOne
        input wallProfile
      rcases W2M1kSelectedCensus.selectedCensus_dichotomy_of_dividedData w.frame.data
          hc hab hOne w.frame.fullDim hForest wallProfile wallShape divided hLeftCard
          hRightCard with selected | selected
      · obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.divided_sameBlocks w.frame.data
          hc hab hOne w.frame.fullDim hForest input wallProfile hBackground hLeftCard hRightCard
          wallShape divided selected
        obtain ⟨fd, hMatrix, -, -⟩ :=
          W2M1kGraphTracking.exists_matched_tracking w.frame.data hc hab hOne w.frame.fullDim
            (DividedData.candidate wallShape divided)
            (W2M1kIncomingMatching.dividedPlacement w.frame.data hc hab hOne wallProfile
              wallShape divided hLeftCard hRightCard)
            hVertices hEdges (InteriorGraphTracking.Tracks.self w.frame.fullDim)
        exact ⟨star, input, block, wallProfile, wallShape, _, Or.inr ⟨divided, rfl⟩, 1, fd,
          hMatrix, m1k_balances input wallShape hC hG
            (W2M1kGaugeFamily.separatedDictionary input wallShape divided hC hG 1)
            (W2M1kGaugeFamily.separatedMemberGenus input wallShape divided hC hG 1) fd⟩
      · obtain ⟨hVertices, hEdges⟩ := W2M1kIncomingMatching.joined_sameBlocks w.frame.data
          hc hab hOne w.frame.fullDim hForest input wallProfile hBackground hLeftCard hRightCard
          (divided.geometry wallShape) selected
        obtain ⟨fd, hMatrix, -, -⟩ :=
          W2M1kGraphTracking.exists_matched_tracking w.frame.data hc hab hOne w.frame.fullDim
            (joinedCandidate star (divided.geometry wallShape))
            (W2M1kIncomingMatching.joinedPlacement w.frame.data hc hab hOne
              (divided.geometry wallShape) hLeftCard hRightCard)
            hVertices hEdges (InteriorGraphTracking.Tracks.self w.frame.fullDim)
        exact ⟨star, input, block, wallProfile, wallShape, _, Or.inr ⟨divided, rfl⟩, 2, fd,
          hMatrix, m1k_balances input wallShape hC hG
            (W2M1kGaugeFamily.separatedDictionary input wallShape divided hC hG 2)
            (W2M1kGaugeFamily.separatedMemberGenus input wallShape divided hC hG 2) fd⟩

end M1k

section Four

open W3FourSourceCandidates (growProfileFirst)

/-- Equation (2)'s family is stated (`W3FourCountBalance`) with a classical decision
procedure on the target's edges; this local instance makes the statement below elaborate
against it. -/
noncomputable local instance instDecidableEqEdgesFour {target : CFGraph} :
    DecidableEq target.edges := Classical.decEq _

/-- **Equation (2) at every regrowth tagged `w3Four`.**  The root receipts
`W3FourCountBalance.exists_sum_signedMult_eq_zero` asks for are derived from the
classification (`TargetSeparation.farEndpoint` at the `other` direction, as in
`InteriorBridgesTrivalent.exists_four_matched_tracking_of_classification`); every
nonsingular member of the balance's family has a full-dimensional presentation in the
regrowth's own coordinates, transported from the member Part I identifies the regrowth's
own cover with through the wall datum's two dictionaries. -/
theorem exists_w3Four_balance (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w3Four) :
    ∃ (star : ThirdEquation.ThreeStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : ThirdEquation.W3SourceInput w.limit star)
      (profile : W3R1SourceProfile.Nd3Profile w.limit
        (ThirdEquation.W3SourceInput.distinguishedBlock input))
      (_ : profile.first.1.1.1 ≠ profile.second.1.1.1)
      (_ : w.limit.sourceEdgeIndex profile.largest.1 =
        (w.limit.vertexPartition (mergeVertex w)).blockCard
          (ThirdEquation.W3SourceInput.distinguishedBlock input).1)
      (geometry : W3FourClosure.FourStarGeometry w.limit (mergeVertex w))
      (certified : W3FourRegrownColumnSeam.MemberCertificates w.limit (mergeVertex w) geometry),
      (∀ position : Fin 4, (GluingDatum.LengthMatrixPresentation.matrix
          (certified.receipts.receipts.presentation position)).det ≠ 0 →
        Nonempty (FullDimensionalSource.FullDimensionalSourcePresentation
          (certified.receipts.candidate position).datum (Fin p))) ∧
        ∑ position : Fin 4, signedMult (certified.receipts.receipts.presentation position) = 0 := by
  have hForest := InheritedLimitRows.forest w hy
  have hCompat := InheritedLimitRows.danglingCompatible w hy
  have hConnected := limit_connected w
  have hGenus := limit_genus w
  cases cls with
  | w4 => cases htag
  | w2 _ _ profile => cases profile <;> cases htag
  | w3 star input classification =>
    cases classification with
    | shift => cases htag
    | nd3CoarseFine => cases htag
    | nd2CoarseFine => cases htag
    | four profile directions largest_index pair_index =>
      obtain ⟨_geometry', certified', -, index, fdIndex, -, -, -, -⟩ :=
        InteriorBridgesTrivalent.exists_four_matched_tracking_of_classification w.frame.data
          (InteriorProgress.hc_column w.frame.fullDim w.column)
          (InteriorProgress.hab_column w.frame.fullDim w.column)
          (InteriorProgress.hOne_column w.frame.fullDim w.column) w.frame.fullDim hForest
          hCompat star input (InteriorGraphTracking.Tracks.self w.frame.fullDim)
          (.four profile directions largest_index pair_index) rfl
      have hOtherIncident :=
        (mem_incidentEdges_iff _ _).mp
          (growProfileFirst profile directions largest_index).otherTarget_mem
      have hGrowIncident :=
        (mem_incidentEdges_iff _ _).mp
          (growProfileFirst profile directions largest_index).growTarget_mem
      have hLargestIncident :=
        (mem_incidentEdges_iff _ _).mp
          (growProfileFirst profile directions largest_index).largestTarget_mem
      have hRoot := TargetSeparation.farEndpoint_ne hOtherIncident
      have hGrowFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus hOtherIncident
        hGrowIncident
        (Ne.symm (growProfileFirst profile directions largest_index).grow_target_ne_other)
      have hLargestFixed := TargetSeparation.edgeMoved_eq_false hConnected hGenus
        hOtherIncident hLargestIncident
        (growProfileFirst profile directions largest_index).other_target_ne_largest
      have hOtherMoved := TargetSeparation.edgeMoved_self_eq_true hOtherIncident
      obtain ⟨geometry, certified, hBalance⟩ :=
        W3FourCountBalance.exists_sum_signedMult_eq_zero profile directions largest_index _
          hRoot hGrowFixed hLargestFixed hOtherMoved hConnected hGenus
      let fdSource := A04MoreTags.reindexFullDim
        ((TargetExpansion.occurrenceEquiv _ _ (certified'.receipts.candidate index).right).trans
          fdIndex.labelling.targetEdge.symm) fdIndex
      have fdAt : ∀ position : Fin 4, (GluingDatum.LengthMatrixPresentation.matrix
          (certified.receipts.receipts.presentation position)).det ≠ 0 →
          FullDimensionalSource.FullDimensionalSourcePresentation
            (certified.receipts.candidate position).datum (Option _) :=
        fun position hDet ↦ W3FourStableIncidence.outgoingPresentation (data := w.limit)
          ((certified'.dictionary index).symm.trans (certified.dictionary position))
          (certified.receipts.candidate_valid position input.valid) hConnected hGenus
          (certified'.memberGenus index) (certified.memberGenus position) fdSource
          (certified.receipts.labelling position)
          (certified.receipts.labelling_det_ne_zero position hDet)
      refine ⟨star, input, profile, directions, largest_index, geometry, certified,
        fun position hDet ↦ ⟨A04MoreTags.reindexFullDim
          (fdIndex.labelling.targetEdge.trans
            (TargetExpansion.occurrenceEquiv _ _ (certified'.receipts.candidate index).right).symm)
          (fdAt position hDet)⟩, ?_⟩
      by_cases hSome : ∃ position : Fin 4, (GluingDatum.LengthMatrixPresentation.matrix
          (certified.receipts.receipts.presentation position)).det ≠ 0
      · obtain ⟨position, hDet⟩ := hSome
        exact hBalance position (fdAt position hDet)
      · push Not at hSome
        refine Finset.sum_eq_zero fun position _ ↦ ?_
        unfold signedMult
        rw [hSome position, mul_zero]

end Four

end DraismaVargas.Count.RegrowthBalances
