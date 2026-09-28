import DraismaVargasCount.RegrowthWallInput
import DraismaVargasCount.ResolutionExpansionFree
import DraismaVargasCount.M11IncomingDenominator
import DraismaVargasCount.StarParityFromBalance
import DraismaVargasCount.Integrality
import DraismaVargasCount.W4StarParity

/-!
# The M-11 family clause, modulo the star census

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-M-11}`: Figure 32
and Equation (6) (the three M-11 local continuations); Vargas, Part II
(arXiv:2609.09109): the star of a codimension-one wall and `prop-signed-mult`.  This
module reduces the M-11 clause of the star parity in step 2 of `Assembly` to a census
of the star, `M11StarCensus`.

## The findings

Equation (6) holds at **every** regrowth tagged `w2M11` with no receipt at all
(`exists_balance`): the odd-denominator input is
`M11IncomingDenominator.incomingRowDenominator_third_eq_one`, and the incoming member
is the regrowth's own cover matched by Part I.

The star side needs care.  A census of the star by wall-anchored candidates
(`M11WallExhaustion.Candidate`, indexed by `(placement, resolution)`) does not work.
A decoupled transport onto a wall-anchored candidate pins, at the discrete non-leaf
endpoint, the two wall occurrences' sheet permutations on the M-11 block
(`edgePerm_eq_freshPerm`), so it forces them to agree there, whereas Equation (6)'s
position `1` (Figure 32's remote split) is presented through the branch swap
`branchIso`, which moves the double direction's sheets and fixes the single
direction's.  Moreover wall-anchored candidates at one index are one class
(`cls_eq_of_candidate`), so they separate classes only through
`(placement, resolution)` (`index_injective_of_separates`).  In computer experiments
with genus-six M-11 walls, most walls have two *split* classes (the incoming position
`0` and the remote position `1`), some have a split and a joined class, and a few
have all three.  The route that works is a census of the star by Equation (6)'s
*positions*, not by wall-anchored indices: it is the named residue `M11StarCensus`,
and `familyStarParity_w2M11_of_census` proves the family clause from it.

Separately, at a **loop wall** (the two double survivors on one stable row, allowed by
Part I) the two split positions have literally the same labelled matrix, hence equal
signed multiplicity on the same side of the wall, and the joined member carries
`-2 s₀` (`signedMult_one_eq_zero`, `signedMult_two_eq`); if a loop-reversing
automorphism of the wall identified the two split positions, the census would fail
there, and the star clause would fail exactly when `s₀` is odd (`loop_parity_defect`).
Loop walls do not occur at a regrowth (`M11StarCensusProof.not_sameDoubleRow_of_regrowth`).

## What is proved

* **The index.**  `exists_payload`: a `w2M11` classification of a regrowth's limit
  carries `(star, input, block, profile, hCard)` over `w.limit`.  The index is `Fin 3`
  (Equation (6)'s positions: `0` the split, `1` the remote split, `2` the joined),
  with the family's labelling `lab` and `Nonsingular q` (the member's determinant is
  nonzero).  Every term of Equation (6) is an integer (`integral_signedMult`).
* **The balance.**  `exists_balance`: Equation (6) at every regrowth tagged `w2M11`, in
  the regrowth's own `Fin p` coordinates, with **no** receipt.
* **Wall-anchored candidates.**  `edgePerm_eq_freshPerm` (a decoupled transport pins
  every placed occurrence permutation); `sameIndexDatum`, `cls_eq_of_candidate`,
  `cls_eq_of_index_eq`, `index_injective_of_separates` (a candidate index is a class
  invariant); `branchIso` (the remote branch swap).
* **Loop walls.**  `SameDoubleRow`; `commonMatrix_one_eq_zero`,
  `squareMatrix_one_eq_zero`, `signedMult_one_eq_zero`, `signedMult_two_eq`,
  `loop_parity_defect`.
* **The parity.**  `starParityAt_of_census`: the star clause from Equation (6) and a
  census of the star by its nonsingular positions; `M11StarCensus`,
  `familyStarParity_w2M11_of_census`, `familyStarParity_w2M11`.

## What is NOT proved here (every hypothesis, explicitly)

* **`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2M11` is not proved here.**  Its residue
  is `M11StarCensus` (it implies the clause, `familyStarParity_w2M11_of_census`; it is
  strictly stronger, since it fixes the class count).  The census is proved in
  `M11StarCensusProof` and `M11StarExhaustionProof`.
* **The census is not produced here.**  Its three halves are: (a) every nonsingular
  position is realized by a star member (the position's frame: full-dimensional
  presentation `M11FullDimensional.outgoingPresentation`, core identification through
  `M11StableGraphs.between`, degeneracy at the wall request, and a labelled limit
  isomorphism -- through `branchIso.symm` at position `1`); (b) every star member is in
  the class of the position of its type (split coherent / split incoherent / joined,
  relative to the wall); (c) distinct types are distinct classes.
* Nothing here is specific to the merged block sizes `(2,1,1)`.

## Two tempting inferences, checked

* (i) *"At an M-11 wall the star has at most three classes (Equation (6)'s three
  positions), and the singular position contributes nothing, as at W4."*  **Holds in a
  modified form, off loop walls**: the classes are indexed by Equation (6)'s positions,
  not by wall-anchored `(placement, resolution)` indices -- position `1`'s class contains
  no wall-anchored candidate, since a candidate's canonical dictionary is coherent, a
  frame isomorphism induces a coherent limit isomorphism at the discrete placed endpoint,
  and position `1` is incoherent through every labelled limit isomorphism -- and the
  singular terms are `0` (`starParityAt_of_census`).  At loop walls positions `0` and `1`
  have equal signed multiplicity (`signedMult_one_eq_zero`) and could be one class.
* (ii) *"The classification of the star members is small enough to be done by `decide`
  over the finitely many local resolutions at degree 4."*  **Not as a route.**  The
  local resolutions are few, but membership is decided by the member's limit
  isomorphism's per-occurrence sheet permutations (coherence), which is global (a whole
  branch is swapped) and index-free.

## Consumers

The `w2M11` clause of `RegrowthWallInput.FamilyStarParity` (step 2 of `Assembly`),
through `M11StarCensusProof`.
-/

namespace DraismaVargas.Count.M11StarParityFree

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction
open ClassifiedContinuation (SourceCase)
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}

/-! ## 1.  The Equation (6) payload at a regrowth tagged `w2M11` -/

/-- **The M-11 payload of a regrowth.**  A classification of the regrowth's limit with
tag `w2M11` carries a two-star, a W2 source input, a two-sheet wall block and Part I's
Figure 32 source profile, all over `w.limit`. -/
theorem exists_payload (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w2M11) :
    ∃ (star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (_input : SecondEquation.W2SourceInput w.limit star)
      (block : W4Assembly.WallBlock w.limit (mergeVertex w))
      (_profile : W2R2SourceProfile.SourceProfile w.limit star block),
      (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2 := by
  cases cls with
  | w4 => cases htag
  | w3 _ _ profile => cases profile <;> cases htag
  | w2 star input profile =>
    obtain ⟨block, profile', hCard⟩ :=
      W2M11GraphTracking.exists_w2M11_payload w.frame.data
        (InteriorProgress.hc_column w.frame.fullDim w.column)
        (InteriorProgress.hab_column w.frame.fullDim w.column)
        (InteriorProgress.hOne_column w.frame.fullDim w.column) star input profile htag
    exact ⟨star, input, block, profile', hCard⟩

/-- **Equation (6) at every regrowth tagged `w2M11`**, in the regrowth's own `Fin p`
coordinates.  The incoming full-dimensional member the balance needs is the regrowth's
own cover, matched by Part I (`W2M11GraphTracking.exists_matched_tracking`); the
odd-denominator receipt of `M11MultiplicityBalance` is discharged by
`M11IncomingDenominator.incomingRowDenominator_third_eq_one`. -/
theorem exists_balance (w : Regrowth core y degree) (hy : Nondegenerate y)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w))
    (htag : cls.sourceCase = .w2M11) :
    ∃ (star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : SecondEquation.W2SourceInput w.limit star)
      (block : W4Assembly.WallBlock w.limit (mergeVertex w))
      (profile : W2R2SourceProfile.SourceProfile w.limit star block)
      (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
      (incoming : Fin 3)
      (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
        (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p)),
      ∑ position : Fin 3, signedMult (M11CommonBalance.labelling input profile hCard
        (M11FullDimensional.initialLabelling input profile hCard incoming incomingFD)
          position).presentation = 0 := by
  obtain ⟨star, input, block, profile, hCard⟩ := exists_payload w cls htag
  have hForest := InheritedLimitRows.forest w hy
  have hCompat := WallAdmissibility.danglingCompatible_of_contractionForest w.frame.data
    (InteriorProgress.hc_column w.frame.fullDim w.column)
    (InteriorProgress.hab_column w.frame.fullDim w.column)
    (InteriorProgress.hOne_column w.frame.fullDim w.column) hForest
  obtain ⟨incoming, fd, -, -, -, -, -⟩ :=
    W2M11GraphTracking.exists_matched_tracking w.frame.data
      (InteriorProgress.hc_column w.frame.fullDim w.column)
      (InteriorProgress.hab_column w.frame.fullDim w.column)
      (InteriorProgress.hOne_column w.frame.fullDim w.column) w.frame.fullDim hForest hCompat
      input profile hCard (InteriorGraphTracking.Tracks.self w.frame.fullDim)
  exact ⟨star, input, block, profile, hCard, incoming, fd,
    M11IncomingDenominator.sum_signedMult_eq_zero input profile hCard
      (graph_connected_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column) w.frame.fullDim.targetConnected)
      ((genus_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
        (w.frame.numEdges_edgeOf w.column)).trans w.frame.fullDim.targetGenus)
      incoming _ fd⟩

/-! ## 2.  A decoupled transport forces coherence at a discrete placed endpoint -/

section Coherence

open ResolutionExpansionFree

variable {target otherTarget : CFGraph} {first : GluingDatum target degree}
  {second : GluingDatum otherTarget degree} {iso : GeometricDatumIso first second}
  {wall : target.V} {otherWall : otherTarget.V} {right : target.edges → Bool}
  {otherRight : otherTarget.edges → Bool}
  {resolution otherResolution : ResolutionM11.LocalResolution degree}

/-- **A decoupled transport pins every placed occurrence permutation** to its
`freshPerm`, on each sheet that is a singleton of the (source-side) fresh endpoint
partition. -/
theorem edgePerm_eq_freshPerm
    (t : TransportFree iso wall otherWall right otherRight resolution otherResolution)
    (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨ (edge : target.V × target.V).2 = wall)
    (hSide : right edge = true) (sheet : Fin degree)
    (hSingle : ∀ x, resolution.right.Rel x sheet → x = sheet) :
    iso.edgePerm edge sheet = t.freshPerm sheet := by
  have h := t.endpoint_compatible edge hIncident sheet
  rw [if_pos hSide, if_pos hSide] at h
  exact (Equiv.symm_apply_eq _).mp (hSingle _ h)

end Coherence

/-! ## 2b.  A wall-anchored candidate is determined, up to class, by its index -/

section SameIndex

open M11WallExhaustion

variable {hy : Nondegenerate y} {wall : Regrowth core y degree}

/-- The datum isomorphism between two candidates at one index: their data are literally
the same resolution expansion (`M11WallExhaustion.Candidate.data_eq`). -/
noncomputable def sameIndexDatum
    {placement : (wall.frame.limitTarget wall.column).edges → Bool}
    {resolution : ResolutionM11.LocalResolution degree}
    (c₁ c₂ : Candidate hy wall placement resolution) :
    GeometricDatumIso c₁.regrowth.frame.data c₂.regrowth.frame.data :=
  UniformExpansionRecognition.ofEq (c₁.data_eq.trans c₂.data_eq.symm)

theorem sameIndex_source_square
    {placement : (wall.frame.limitTarget wall.column).edges → Bool}
    {resolution : ResolutionM11.LocalResolution degree}
    (c₁ c₂ : Candidate hy wall placement resolution)
    (vertex : c₁.regrowth.frame.data.SourceVertex) :
    c₂.datumIso.sourceVertexEquiv (InheritedLimitBranches.vertexMap c₂.regrowth
        ((sameIndexDatum c₁ c₂).sourceVertexEquiv vertex)) =
      c₁.datumIso.sourceVertexEquiv (InheritedLimitBranches.vertexMap c₁.regrowth vertex) := by
  have h : ((sameIndexDatum c₁ c₂).sourceVertexEquiv vertex).1 = vertex.1 :=
    UniformExpansionRecognition.ofEq_sourceVertexEquiv (c₁.data_eq.trans c₂.data_eq.symm) vertex
  refine (Candidate.member_contractSourceVertex c₂ _).trans
    (Eq.trans ?_ (Candidate.member_contractSourceVertex c₁ vertex).symm)
  rw [h]

theorem sameIndex_edge_square
    {placement : (wall.frame.limitTarget wall.column).edges → Bool}
    {resolution : ResolutionM11.LocalResolution degree}
    (c₁ c₂ : Candidate hy wall placement resolution) (edge : c₁.regrowth.limit.SourceEdge) :
    (sameIndexDatum c₁ c₂).sourceEdgeEquiv (InheritedLimitRows.edgeEmbedding c₁.regrowth edge) =
      InheritedLimitRows.edgeEmbedding c₂.regrowth
        (StarFrameIso.transfer c₁.starLimitIso c₂.starLimitIso edge) := by
  apply Subtype.ext
  have h : ((sameIndexDatum c₁ c₂).sourceEdgeEquiv
      (InheritedLimitRows.edgeEmbedding c₁.regrowth edge)).1 =
      (InheritedLimitRows.edgeEmbedding c₁.regrowth edge).1 :=
    UniformExpansionRecognition.ofEq_sourceEdgeEquiv (c₁.data_eq.trans c₂.data_eq.symm) _
  have ht := StarFrameIso.datum_sourceEdgeEquiv_transfer c₁.starLimitIso c₂.starLimitIso edge
  change c₂.datumIso.sourceEdgeEquiv _ = c₁.datumIso.sourceEdgeEquiv edge at ht
  rw [h, Candidate.member_edgeEmbedding_val c₁, Candidate.member_edgeEmbedding_val c₂, ht]

/-- **Two wall-anchored candidates at one `(placement, resolution)` index are one star
class.**  So a `Candidate`-indexed exhaustion can separate star classes only by their
`(placement, resolution)` index. -/
theorem cls_eq_of_candidate
    {placement : (wall.frame.limitTarget wall.column).edges → Bool}
    {resolution : ResolutionM11.LocalResolution degree}
    (c₁ c₂ : Candidate hy wall placement resolution) :
    c₁.starMember.cls = c₂.starMember.cls :=
  Quotient.sound ⟨StarFrameIso.ofLimitSquare c₁.starLimitIso c₂.starLimitIso
    (sameIndexDatum c₁ c₂) (sameIndex_source_square c₁ c₂) (sameIndex_edge_square c₁ c₂)⟩

theorem cls_eq_of_index_eq
    {placement₁ placement₂ : (wall.frame.limitTarget wall.column).edges → Bool}
    {resolution₁ resolution₂ : ResolutionM11.LocalResolution degree}
    (c₁ : Candidate hy wall placement₁ resolution₁) (c₂ : Candidate hy wall placement₂ resolution₂)
    (hP : placement₁ = placement₂) (hR : resolution₁ = resolution₂) :
    c₁.starMember.cls = c₂.starMember.cls := by
  subst hP hR
  exact cls_eq_of_candidate c₁ c₂

/-- **`Separates` forces the index map to be injective**: a separated candidate family
never repeats a `(placement, resolution)` index. -/
theorem index_injective_of_separates {ι : Type*}
    (P : ι → ((wall.frame.limitTarget wall.column).edges → Bool))
    (R : ι → ResolutionM11.LocalResolution degree)
    (cand : ∀ i : ι, Candidate hy wall (P i) (R i)) (hSep : Separates P R cand)
    {i j : ι} (hP : P i = P j) (hR : R i = R j) : i = j :=
  hSep (cls_eq_of_index_eq (cand i) (cand j) hP hR)

end SameIndex

/-! ## 3.  Position `1`, and why wall-anchored candidates miss it -/

/-! ### The canonical incoherent dictionary: Figure 32's remote branch swap -/

section BranchSwap

variable {target : CFGraph} {data : GluingDatum target degree} {wallV : target.V}
  {star : W2R1Target.TwoStar target wallV} {block : W4Assembly.WallBlock data wallV}

/-- The remote branch swap of an M-11 profile as a geometric datum isomorphism from the
wall datum to its swapped copy (the contraction of Equation (6)'s position `1`). -/
noncomputable def branchIso (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wallV).blockCard block.1 = 2) :
    GeometricDatumIso data (M11RemoteCandidates.swappedDatum profile hCard) :=
  GeometricDatumIso.ofStrict
    (Transport.DatumIso.ofSheetRelabeling (M11RemotePruning.branchRelabeling profile hCard))

theorem incident_of_star (label : Fin 2) :
    ((star.edge label : target.edges) : target.V × target.V).1 = wallV ∨
      ((star.edge label : target.edges) : target.V × target.V).2 = wallV := by
  have h := star.edge_mem_incidentEdges label
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using h

end BranchSwap

/-! ## 3b.  Loop walls: the two split positions coincide in Equation (6) -/

section LoopWall

variable {target : CFGraph} {wallV : target.V} {data : GluingDatum target degree}
  {star : W2R1Target.TwoStar target wallV} (input : SecondEquation.W2SourceInput data star)
  {block : W4Assembly.WallBlock data wallV}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wallV).blockCard block.1 = 2)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (initial : W4StableSource.StableLengthMatrixLabelling
    (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)

/-- **A loop wall**: the two surviving double-direction occurrences at the M-11 block
lie on one stable row.  Part I allows it (`M11CommonBalance`: "their stable rows are
allowed to coincide"); on a cubic core it means a loop at the block's source vertex. -/
def SameDoubleRow : Prop :=
  (M11SplitRowDescent.newOldEdge profile hCard).stablePath =
    (M11BranchSeparation.oppositeDouble profile hCard).stablePath

theorem commonMatrix_one_eq_zero (hConnected : graph_connected target)
    (hGenus : genus target = 0) (hRow : SameDoubleRow profile hCard) :
    M11CommonBalance.commonMatrix input profile hCard 1 =
      M11CommonBalance.commonMatrix input profile hCard 0 := by
  classical
  funext path place
  cases place with
  | none =>
    have h1 : M11CommonBalance.commonMatrix input profile hCard 1 path none =
        if path = (M11BranchSeparation.oppositeDouble profile hCard).stablePath then 2 else 0 :=
      M11RemoteLimitMatrix.matrix_new input profile hCard hConnected hGenus path
    have h0 : M11CommonBalance.commonMatrix input profile hCard 0 path none =
        if path = (M11SplitRowDescent.newOldEdge profile hCard).stablePath then 2 else 0 :=
      M11SplitLimitMatrix.matrix_new input profile hCard path
    rw [h1, h0, hRow]
  | some place =>
    rw [M11CommonBalance.commonMatrix_retained, M11CommonBalance.commonMatrix_retained]

/-- At a loop wall Equation (6)'s two split members have **the same labelled matrix**. -/
theorem squareMatrix_one_eq_zero (hConnected : graph_connected target)
    (hGenus : genus target = 0) (hRow : SameDoubleRow profile hCard) :
    M11CommonBalance.squareMatrix input profile hCard initial 1 =
      M11CommonBalance.squareMatrix input profile hCard initial 0 := by
  ext row column
  rw [M11CommonBalance.squareMatrix_common, M11CommonBalance.squareMatrix_common,
    commonMatrix_one_eq_zero input profile hCard hConnected hGenus hRow]

/-- **At a loop wall the two split positions have equal signed multiplicity** -- the
same size *and the same sign*, so they lie on the same side of the wall. -/
theorem signedMult_one_eq_zero (hConnected : graph_connected target)
    (hGenus : genus target = 0) (hRow : SameDoubleRow profile hCard) :
    signedMult (M11CommonBalance.labelling input profile hCard initial 1).presentation =
      signedMult (M11CommonBalance.labelling input profile hCard initial 0).presentation := by
  change (denominatorProduct (M11CommonBalance.labelling input profile hCard initial 1).presentation
      : ℚ) / 2 ^ leafCount (M11RemoteCandidates.candidates input profile hCard 1).outgoingTarget *
        (M11CommonBalance.squareMatrix input profile hCard initial 1).det =
    (denominatorProduct (M11CommonBalance.labelling input profile hCard initial 0).presentation
      : ℚ) / 2 ^ leafCount (M11RemoteCandidates.candidates input profile hCard 0).outgoingTarget *
        (M11CommonBalance.squareMatrix input profile hCard initial 0).det
  rw [M11MultiplicityBalance.denominatorProduct_one input profile hCard initial hConnected hGenus,
    M11MultiplicityBalance.denominatorProduct_zero, M11MultiplicityBalance.leafCount_one,
    M11MultiplicityBalance.leafCount_zero,
    squareMatrix_one_eq_zero input profile hCard initial hConnected hGenus hRow]

/-- **At a loop wall the joined member carries twice the split multiplicity, on the other
side**: Equation (6) reads `2 s₀ + s₂ = 0`. -/
theorem signedMult_two_eq (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hRow : SameDoubleRow profile hCard)
    (hbal : ∑ q : Fin 3,
      signedMult (M11CommonBalance.labelling input profile hCard initial q).presentation = 0) :
    signedMult (M11CommonBalance.labelling input profile hCard initial 2).presentation =
      -2 * signedMult (M11CommonBalance.labelling input profile hCard initial 0).presentation := by
  rw [Fin.sum_univ_three, signedMult_one_eq_zero input profile hCard initial hConnected hGenus
    hRow] at hbal
  linarith

/-- **The parity consequence at a loop wall.**  If the two split positions are *one* star
class (a loop-reversing automorphism of the wall), the census fails, and a star equal to
`{split class, joined class}` has an odd number of odd classes exactly when `s₀` is odd:
`|s₂| = 2 |s₀|` is even.  Stated on integers. -/
theorem loop_parity_defect (s₀ s₂ : ℤ) (h : s₂ = -2 * s₀) :
    Even s₂.natAbs ∧ (Odd (s₀.natAbs + s₂.natAbs) ↔ Odd s₀.natAbs) := by
  subst h
  have h2 : (-2 * s₀).natAbs = 2 * s₀.natAbs := by
    rw [Int.natAbs_mul]; rfl
  rw [h2, show s₀.natAbs + 2 * s₀.natAbs = 3 * s₀.natAbs by ring, Nat.odd_mul]
  exact ⟨even_two_mul _, ⟨fun h ↦ h.2, fun h ↦ ⟨by decide, h⟩⟩⟩

end LoopWall

/-! ## 4.  From Equation (6) to the star clause, given the M-11 star census -/

section Parity

variable {hy : Nondegenerate y} {w : Regrowth core y degree}
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  {input : SecondEquation.W2SourceInput w.limit star}
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  {profile : W2R2SourceProfile.SourceProfile w.limit star block}
  {hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2}
  {incoming : Fin 3}
  {incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
    (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p)}

variable (input profile hCard incoming incomingFD) in
/-- Equation (6)'s labelling at the position `q`, in the regrowth's own coordinates. -/
noncomputable abbrev lab (q : Fin 3) :=
  M11CommonBalance.labelling input profile hCard
    (M11FullDimensional.initialLabelling input profile hCard incoming incomingFD) q

variable (input profile hCard incoming incomingFD) in
/-- The nonsingular positions of Equation (6). -/
def Nonsingular (q : Fin 3) : Prop :=
  (GluingDatum.LengthMatrixPresentation.matrix
    (lab input profile hCard incoming incomingFD q).presentation).det ≠ 0

/-- **Every term of Equation (6) is an integer**: at a nonsingular position the member
carries a full-dimensional presentation with exactly the family's labelling
(`M11FullDimensional.outgoingPresentation`), and at a singular one the term is `0`. -/
theorem integral_signedMult (hConnected : graph_connected (w.frame.limitTarget w.column))
    (hGenus : genus (w.frame.limitTarget w.column) = 0) (q : Fin 3) :
    ∃ value : ℤ, signedMult (lab input profile hCard incoming incomingFD q).presentation =
      (value : ℚ) := by
  by_cases hq : Nonsingular input profile hCard incoming incomingFD q
  · exact isIntegralMultiplicity (M11FullDimensional.outgoingPresentation input
      profile hCard hConnected hGenus incoming q incomingFD hq)
  · refine ⟨0, ?_⟩
    unfold Nonsingular at hq
    rw [not_not] at hq
    unfold signedMult
    rw [hq, mul_zero, Int.cast_zero]

/-- **The star clause from Equation (6) and a census of the star by its nonsingular
positions.**  The singular positions contribute `0` to the balance; the census says
each nonsingular position is exactly one star class, of the position's multiplicity. -/
theorem starParityAt_of_census
    (hConnected : graph_connected (w.frame.limitTarget w.column))
    (hGenus : genus (w.frame.limitTarget w.column) = 0)
    (hbal : ∑ q : Fin 3, signedMult (lab input profile hCard incoming incomingFD q).presentation = 0)
    (e : {q : Fin 3 // Nonsingular input profile hCard incoming incomingFD q} ≃
      GeometricStar.Star hy w)
    (hmult : ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
      (signedMult (lab input profile hCard incoming incomingFD q.1).presentation).num.natAbs) :
    RegrowthWallInput.StarParityAt hy w := by
  classical
  refine StarParityFromBalance.even_card_starClass_odd_of_equiv e ?_
  have hEven := StarParityFromBalance.even_sum_num_natAbs_of_sum_eq_zero
    (fun q ↦ signedMult (lab input profile hCard incoming incomingFD q).presentation)
    (integral_signedMult hConnected hGenus) hbal
  have hSplit := Fintype.sum_subtype_add_sum_subtype
    (Nonsingular input profile hCard incoming incomingFD)
    (fun q ↦ (signedMult (lab input profile hCard incoming incomingFD q).presentation).num.natAbs)
  have hRest : ∑ q : {q // ¬ Nonsingular input profile hCard incoming incomingFD q},
      (signedMult (lab input profile hCard incoming incomingFD q.1).presentation).num.natAbs = 0 := by
    refine Finset.sum_eq_zero fun q _ ↦ ?_
    have hq := q.2
    unfold Nonsingular at hq
    rw [not_not] at hq
    unfold signedMult
    rw [hq, mul_zero]
    rfl
  rw [hRest, add_zero] at hSplit
  rw [← hSplit] at hEven
  simpa only [hmult] using hEven

end Parity

/-! ## 5.  The family clause, modulo the M-11 star census -/

/-- **The residue of `FamilyStarParity … .w2M11`: the M-11 star census.**  At every
regrowth tagged `w2M11`, for every presentation of its Equation (6) family, the star is
in bijection with the family's nonsingular positions, each class carrying its position's
multiplicity.

*Interface*: it implies `FamilyStarParity degree n p .w2M11`
(`familyStarParity_w2M11_of_census`); it is **stronger** (it fixes the class count, not
only its parity).  Wall-anchored candidates cannot produce it (§3); it is proved in
`M11StarCensusProof` and `M11StarExhaustionProof`. -/
def M11StarCensus (degree n p : ℕ) : Prop :=
  ∀ (core : Core n p) (y : Fin p → ℚ) (hy : Nondegenerate y) (w : Regrowth core y degree)
    (cls : IncomingSourceCases.Classification w.limit (mergeVertex w)),
    cls.sourceCase = .w2M11 →
    ∀ (star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w))
      (input : SecondEquation.W2SourceInput w.limit star)
      (block : W4Assembly.WallBlock w.limit (mergeVertex w))
      (profile : W2R2SourceProfile.SourceProfile w.limit star block)
      (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
      (incoming : Fin 3)
      (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
        (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p)),
      ∃ e : {q : Fin 3 // Nonsingular input profile hCard incoming incomingFD q} ≃
          GeometricStar.Star hy w,
        ∀ q, (GeometricStar.Star.toFibre (e q)).multNat =
          (signedMult (lab input profile hCard incoming incomingFD q.1).presentation).num.natAbs

/-- **`FamilyStarParity … .w2M11` from the M-11 star census**: Equation (6) at the
regrowth (`exists_balance`, no receipt) read mod two through the census. -/
theorem familyStarParity_w2M11_of_census (h : M11StarCensus degree n p) :
    RegrowthWallInput.FamilyStarParity degree n p .w2M11 := by
  intro core y hy w cls htag
  obtain ⟨star, input, block, profile, hCard, incoming, fd, hbal⟩ :=
    exists_balance w hy cls htag
  obtain ⟨e, hmult⟩ := h core y hy w cls htag star input block profile hCard incoming fd
  exact starParityAt_of_census
    (graph_connected_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column) w.frame.fullDim.targetConnected)
    ((genus_contract w.frame.target (fst_ne_snd (w.frame.edgeOf w.column))
      (w.frame.numEdges_edgeOf w.column)).trans w.frame.fullDim.targetGenus)
    hbal e hmult

/-- The `w2M11` family clause at genus six and degree four, modulo the census. -/
theorem familyStarParity_w2M11 (h : M11StarCensus (2 + 2) (4 * 2 + 2) (6 * 2 + 3)) :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2M11 :=
  familyStarParity_w2M11_of_census h

end DraismaVargas.Count.M11StarParityFree
