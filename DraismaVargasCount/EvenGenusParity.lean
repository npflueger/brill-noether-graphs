module

public import DraismaVargasCount.BallotEndSwapGeneral
public import DraismaVargasCount.StarSupplyAssembly
public import DraismaVargasCount.CensusAssembly
public import DraismaVargasCount.ValencyTwoPairing
public import DraismaVargasCount.ValencyFourRealisation
public import DraismaVargasCount.SimpleWallSupply
public import DraismaVargasCount.StepSupplyGenusSix

@[expose] public section

/-!
# The mod-2 Draisma--Vargas count in every even genus at least six

Over a general metric graph of even genus `g`, the tropical morphisms of degree `g/2 + 1` to
metric trees, counted with multiplicity, number the Catalan number `C_{g/2}` (A. Vargas,
*Catalan-many tropical morphisms to trees; Part II: A space and a count*, arXiv:2609.09109, the
main theorem; the morphisms are those constructed in J. Draisma and A. Vargas,
*Catalan-many tropical morphisms to trees; Part I: Constructions*, arXiv:1909.12924). This module
proves the mod-2 form of that count in every even genus at least six.

**Theorem** (`openOddCount_mod_two`). For every `k ≥ 2`, over every connected cubic core of genus
`2k + 2` and every positive general request `y`, in the sense of `CountSchedule.C34`, the number
of open classes of odd multiplicity in degree `k + 2` has the parity of `catalan (k + 1)`:

  `GeometricFibre.openOddCount core y (k + 2) % 2 = catalan (k + 1) % 2`.

At `k = 2` (genus six, `C₃ = 5`) this is the propagation step of the genus-six count,
`Assembly.c34_genusSix`; it is recovered here as `c34_two`. At `k = 3` (genus eight, `C₄ = 14`)
the count is even (`evenC34_three`).

## The proof

The argument is that of `DraismaVargasCount.Assembly`, steps 1 to 4, with every input proved at
general degree and core size.

1. **Base count** (`baseCount`, `openOddCount_caterpillar`). Over the caterpillar of loops
   `catCore k`, of genus `2k + 2`, at every positive request, there are exactly
   `catalan (k + 1)` open classes and every member has multiplicity one
   (`BallotEndSwapGeneral.card_open`, `BallotEndSwapGeneral.absMult_eq_one`). So the open odd
   count there is `catalan (k + 1)`.
2. **The caterpillar is a base core** (`catCore_cubic`, `catCore_connected`, `catCubicCore`).
   Cubicity is the valency census of the caterpillar gluing datum, read through
   `FibreCaterpillar.catIdent`. Connectedness holds because every vertex of `catCore k` other
   than `0` is the head of a slot whose tail has a smaller index (`exists_parent_slot`).
3. **Trivalent walls** (`trivalentWalls`). `SimpleWallSupply.InConeSupplySimple` holds at every
   degree and core size: each of the ten wall-family star parities of Draisma--Vargas Part I is
   proved upstream in that generality (`familyStarParity`).
4. **Type changes** (`typeChanges`). `SimpleWallSupply.TypeChangeSupplyPositive` holds whenever
   the degree and the number of vertices are at least three, from the general valency clauses
   `ValencyTwoPairing.v2ClauseSupply` and `ValencyFourRealisation.v4InputsSupply`.
5. **Transport** (`even_of_base_positive`, `mod_two_eq_of_positiveGeneral`).
   `SimpleWallSupply.odd_of_positiveGeneral` carries oddness in either direction between any two
   positive general sites of cubic cores with the same indices, so evenness is carried by
   contraposition, and the parity of the open odd count is the same at all of them.

A connected cubic core of genus `2k + 2` has `4k + 2` vertices and `6k + 3` slots
(`index_of_genus`), so for `k ≥ 2` the side conditions `3 ≤ k + 2`, `3 ≤ 4k + 2` and
`2 ≤ (6k + 3) + 1 - (4k + 2)` all hold.

## Corollaries

* `c34_iff`: for `k ≥ 2`, `CountSchedule.C34 k` holds exactly when `catalan (k + 1)` is odd. The
  docstring of `CountSchedule.C34` explains why it cannot hold for every `k`.
* `EvenC34`, `evenC34_iff`: the even form of `CountSchedule.C34`, which holds for `k ≥ 2` exactly
  when `catalan (k + 1)` is even.
* `c34_two : CountSchedule.C34 2` (genus six) and `evenC34_three : EvenC34 3` (genus eight).
-/

namespace DraismaVargas.Count.EvenGenusParity

open DraismaVargas.Count
open DraismaVargas.Count.FibreCaterpillar (catCore)
open DraismaVargas.Infrastructure.CaterpillarTree (parentIndex)
open DraismaVargas.LocalCases.CaterpillarDatum (caterpillarDatum)
open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)
open DraismaVargas.LocalCases.StablePathCount (incidenceCount sum_incidenceCount_vertex)
open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.LocalCases.ClassifiedContinuation (SourceCase)

/-! ## 1.  Indices -/

/-- **A connected cubic core of genus `2k + 2` has `4k + 2` vertices and `6k + 3` slots**, from
the handshake identity `3n = 2p`. -/
theorem index_of_genus {k n p : ℕ} {core : Core n p} (h : core.Cubic)
    (hg : p + 1 - n = 2 * k + 2) : n = 4 * k + 2 ∧ p = 6 * k + 3 := by
  have := StepSupplyGenusSix.three_mul_eq_two_mul_of_cubic h
  omega

/-! ## 2.  The caterpillar of loops is a connected cubic core -/

/-- **The caterpillar of loops is cubic, in every genus.** The incidence degree of a core vertex
is the sum of its incidences over the slots, which `FibreCaterpillar.catIdent` matches with the
incidences of the corresponding branch vertex of the caterpillar gluing datum over its stable
paths. That sum is the surviving valency of the branch vertex, which is three. -/
theorem catCore_cubic (m : ℕ) : (catCore m).Cubic := by
  intro vertex
  obtain ⟨branch, rfl⟩ := (FibreCaterpillar.catIdent m).vertex.surjective vertex
  obtain ⟨hCore, hBranch⟩ := FibreCaterpillar.eq_coreVertex_of_branch branch.2
  calc (catCore m).incidenceDegree ((FibreCaterpillar.catIdent m).vertex branch)
      = ∑ slot, coreIncidence (catCore m) ((FibreCaterpillar.catIdent m).vertex branch) slot :=
        rfl
    _ = ∑ slot, incidenceCount (caterpillarDatum m) branch.1
          ((FibreCaterpillar.catIdent m).row.symm slot) :=
        Finset.sum_congr rfl fun slot _ ↦
          ((FibreCaterpillar.catIdent m).incidence branch slot).symm
    _ = ∑ path, incidenceCount (caterpillarDatum m) branch.1 path :=
        Equiv.sum_comp (FibreCaterpillar.catIdent m).row.symm _
    _ = 3 := by
        rw [sum_incidenceCount_vertex, hCore]
        exact FibreCaterpillar.nonDanglingValency_branch m hBranch

/-- **Every vertex of the caterpillar of loops other than `0` has a parent.** The core vertex `j`
sits over the target vertex `branchVal j` of the caterpillar tree, and the target occurrence
ending there, `branchVal j - 1`, is not a leaf edge. Its stable row is a slot with head `j` and
with tail the core vertex over the parent target vertex, whose index is smaller. -/
theorem exists_parent_slot (m : ℕ) (j : Fin (4 * m + 2)) (hj : j.val ≠ 0) :
    ∃ slot : Fin (6 * m + 3),
      (catCore m).head slot = j ∧ ((catCore m).tail slot).val < j.val := by
  have hle := FibreCaterpillar.branchVal_le m j.isLt
  have hmod := FibreCaterpillar.branchVal_mod j.val
  have hpos : 2 ≤ FibreCaterpillar.branchVal j.val := by
    unfold FibreCaterpillar.branchVal
    omega
  have hLeaf : ¬ IsLeafEdge m ⟨FibreCaterpillar.branchVal j.val - 1, by omega⟩ := by
    show ¬ ((FibreCaterpillar.branchVal j.val - 1) % 3 = 0 ∨
      FibreCaterpillar.branchVal j.val - 1 = 6 * m + 2)
    omega
  refine ⟨⟨FibreCaterpillar.branchVal j.val - 1, by omega⟩, Fin.ext ?_, ?_⟩
  · show FibreCaterpillar.branchIdx (FibreCaterpillar.catHeadVal m _) = j.val
    rw [FibreCaterpillar.catHeadVal, ite_eq_right hLeaf]
    show FibreCaterpillar.branchIdx (FibreCaterpillar.branchVal j.val - 1 + 1) = j.val
    rw [Nat.sub_add_cancel (by omega), FibreCaterpillar.branchIdx_branchVal]
  · show FibreCaterpillar.branchIdx
      (parentIndex (FibreCaterpillar.branchVal j.val - 1 + 1)) < j.val
    rw [Nat.sub_add_cancel (by omega)]
    unfold FibreCaterpillar.branchIdx parentIndex FibreCaterpillar.branchVal
    split_ifs <;> omega

/-- **The caterpillar of loops is connected, in every genus.** If no slot crossed a cut, then
membership in the cut would pass from each vertex to its parent (`exists_parent_slot`), so by
strong induction on the index every vertex would lie on the same side as `0`. -/
theorem catCore_connected (m : ℕ) : (catCore m).Connected := by
  intro S hS
  obtain ⟨v, w, hv, hw⟩ := hS
  by_contra hNone
  have hSame : ∀ slot, ((catCore m).tail slot ∈ S ↔ (catCore m).head slot ∈ S) := by
    intro slot
    constructor
    · intro ht
      by_contra hh
      exact hNone ⟨slot, Or.inl ⟨ht, hh⟩⟩
    · intro hh
      by_contra ht
      exact hNone ⟨slot, Or.inr ⟨hh, ht⟩⟩
  have hRoot : ∀ (i : ℕ) (j : Fin (4 * m + 2)), j.val = i →
      (j ∈ S ↔ (⟨0, by omega⟩ : Fin (4 * m + 2)) ∈ S) := by
    intro i
    refine Nat.strong_induction_on i fun i ih ↦ ?_
    intro j hj
    by_cases hj0 : j.val = 0
    · rw [show j = ⟨0, by omega⟩ from Fin.ext hj0]
    · obtain ⟨slot, hHead, hTail⟩ := exists_parent_slot m j hj0
      rw [← hHead, ← hSame slot]
      exact ih _ (by omega) _ rfl
  exact hw ((hRoot _ w rfl).mpr ((hRoot _ v rfl).mp hv))

/-- The caterpillar of loops of genus `2k + 2` as a bundled connected cubic core. -/
def catCubicCore (k : ℕ) : CubicCore (4 * k + 2) (6 * k + 3) where
  core := catCore k
  cubic := catCore_cubic k
  connected := catCore_connected k

@[simp] theorem catCubicCore_core (k : ℕ) : (catCubicCore k).core = catCore k := rfl

/-! ## 3.  The base count -/

/-- **The base count in genus `2k + 2`.** Over the caterpillar of loops `catCore k`, at every
positive request, there are exactly `catalan (k + 1)` open classes in degree `k + 2`, and every
member has multiplicity one. This is `BallotEndSwapGeneral.card_open` and
`BallotEndSwapGeneral.absMult_eq_one` at `m = k - 1`. -/
theorem baseCount {k : ℕ} (hk : 2 ≤ k) {request : Fin (6 * k + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    Nat.card {c : GeometricFibre (catCore k) request (k + 2) // c.Open} = catalan (k + 1) ∧
      ∀ mem : FibreMember (catCore k) request (k + 2), mem.absMult = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  exact ⟨BallotEndSwapGeneral.card_open (by omega) hRequest,
    BallotEndSwapGeneral.absMult_eq_one (by omega) request⟩

/-- **The base count, mod 2.** Every class over the caterpillar has multiplicity one, hence odd
multiplicity, so the open odd count is the number of open classes, `catalan (k + 1)`. -/
theorem openOddCount_caterpillar {k : ℕ} (hk : 2 ≤ k) {request : Fin (6 * k + 3) → ℚ}
    (hRequest : ∀ slot, 0 < request slot) :
    GeometricFibre.openOddCount (catCore k) request (k + 2) = catalan (k + 1) := by
  obtain ⟨hCard, hMult⟩ := baseCount hk hRequest
  have hOdd (c : GeometricFibre (catCore k) request (k + 2)) : c.IsOdd := by
    obtain ⟨mem, rfl⟩ := GeometricFibre.cls_surjective c
    exact (GeometricFibre.isOdd_cls_iff mem).mpr
      (FibreMember.hasOddMult_of_absMult_eq_one (hMult mem))
  rw [GeometricFibre.openOddCount, ← hCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun c ↦ and_iff_left (hOdd c))

/-! ## 4.  The trivalent walls and the type changes, at every degree and size -/

/-- **All ten wall-family star parities, at every degree, core size and request.** The
genus-six clauses of `StarSupplyAssembly` are the specialisations of these at `(4, 10, 15)`. -/
theorem familyStarParity (degree n p : ℕ) (tag : SourceCase) :
    RegrowthWallInput.FamilyStarParity degree n p tag := by
  cases tag with
  | w4 => exact W4NonDiscreteStarExhaustionProof.familyStarParity_w4_all _ _ _
  | w3Four =>
    exact W3FourStarCensusProof.familyStarParity_w3Four_of_census
      (W3FourStarExhaustionProof.w3FourStarCensus _ _ _)
  | w3Shift =>
    exact W3ShiftStarCensusProof.familyStarParity_w3Shift_of_census
      (W3ShiftStarExhaustionProof.w3ShiftStarCensus _ _ _)
  | w3Nd3CoarseFine =>
    exact W3Nd3StarCensusProof.familyStarParity_w3Nd3_of_census
      (W3Nd3StarExhaustionProof.w3Nd3StarCensus _ _ _)
  | w3Nd2CoarseFine =>
    exact W3Nd2StarCensusProof.familyStarParity_w3Nd2_of_census
      (W3Nd2StarExhaustionProof.w3Nd2StarCensus _ _ _)
  | w2M11 =>
    exact M11StarParityFree.familyStarParity_w2M11_of_census
      (M11StarExhaustionProof.m11StarCensus _ _ _)
  | w2M1k => exact W2M1kStarExhaustionProof.familyStarParity_w2M1k_general _ _ _
  | w2Mkk => exact W2MkkStarExhaustionProof.familyStarParity_w2Mkk_general _ _ _
  | w2P => exact W2PStarExhaustionProof.familyStarParity_w2P_general _ _ _
  | w2R1 => exact W2R1StarExhaustionProof.familyStarParity_w2R1_general _ _ _

/-- **The trivalent walls, at every degree and size.** Over every core, crossing a simple wall on
a segment between positive requests preserves the parity of the open odd count. Proved as
`StarSupplyAssembly.inConeSupplySimple_genusSix` is. -/
theorem trivalentWalls (degree n p : ℕ) : SimpleWallSupply.InConeSupplySimple degree n p :=
  RegrowthWallInput.inConeSupplySimple_of_familyStarParity (familyStarParity degree n p)

/-- **The type changes, in degree and size at least three.** Across every Whitehead move between
cubic cores there are positive general requests on the two sides whose open odd counts have the
same parity. Proved as `Assembly.typeChanges_genusSix` is, with the general valency clauses in
place of the genus-six ones. -/
theorem typeChanges {degree n p : ℕ} (hDegree : 3 ≤ degree) (hn : 3 ≤ n) :
    SimpleWallSupply.TypeChangeSupplyPositive degree n p :=
  FacetCensus.typeChangeSupplyPositive_of_metricCensus fun _ _ hStep ↦
    CensusAssembly.stepCensus_of_supplies (ValencyTwoPairing.v2ClauseSupply hDegree hn)
      (CensusAssembly.v4ClauseSupply_of_inputs
        (ValencyFourRealisation.v4InputsSupply hDegree hn))
      hDegree hn hStep

/-! ## 5.  The parity transport -/

/-- **The parity transport, even form.** Oddness is carried in both directions between any two
positive general sites (`SimpleWallSupply.odd_of_positiveGeneral`), so evenness is carried by
contraposition. -/
theorem even_of_base_positive {degree n p : ℕ}
    (hcone : SimpleWallSupply.InConeSupplySimple degree n p)
    (htype : SimpleWallSupply.TypeChangeSupplyPositive degree n p) (hGenus : 2 ≤ p + 1 - n)
    (base : CubicCore n p) (y₀ : Fin p → ℚ)
    (hy₀ : SimpleWallSupply.PositiveGeneral base.core degree y₀)
    (heven : Even (GeometricFibre.openOddCount base.core y₀ degree))
    (c : CubicCore n p) (y : Fin p → ℚ) (hy : SimpleWallSupply.PositiveGeneral c.core degree y) :
    Even (GeometricFibre.openOddCount c.core y degree) := by
  rcases Nat.even_or_odd (GeometricFibre.openOddCount c.core y degree) with h | h
  · exact h
  · exact absurd (SimpleWallSupply.odd_of_positiveGeneral hcone htype hGenus c base y y₀ hy hy₀ h)
      (Nat.not_odd_iff_even.mpr heven)

/-- **The parity of the open odd count is the same at every positive general site** of cubic
cores with the same indices, given the trivalent walls and the type changes. -/
theorem mod_two_eq_of_positiveGeneral {degree n p : ℕ}
    (hcone : SimpleWallSupply.InConeSupplySimple degree n p)
    (htype : SimpleWallSupply.TypeChangeSupplyPositive degree n p) (hGenus : 2 ≤ p + 1 - n)
    (c c' : CubicCore n p) (y y' : Fin p → ℚ)
    (hy : SimpleWallSupply.PositiveGeneral c.core degree y)
    (hy' : SimpleWallSupply.PositiveGeneral c'.core degree y') :
    GeometricFibre.openOddCount c'.core y' degree % 2 =
      GeometricFibre.openOddCount c.core y degree % 2 := by
  rcases Nat.even_or_odd (GeometricFibre.openOddCount c.core y degree) with h | h
  · rw [Nat.even_iff.mp h,
      Nat.even_iff.mp (even_of_base_positive hcone htype hGenus c y hy h c' y' hy')]
  · rw [Nat.odd_iff.mp h,
      Nat.odd_iff.mp (SimpleWallSupply.odd_of_positiveGeneral hcone htype hGenus c c' y y' hy hy' h)]

/-! ## 6.  The theorem -/

/-- **The mod-2 Draisma--Vargas count in every even genus at least six.** For every `k ≥ 2`, over
every connected cubic core of genus `2k + 2` and every positive general request, the number of
open classes of odd multiplicity in degree `k + 2` has the parity of the Catalan number
`catalan (k + 1)`. "General" is the form `CountSchedule.C34` uses: no frame loses a coordinate at
the request. -/
theorem openOddCount_mod_two {k : ℕ} (hk : 2 ≤ k) {n p : ℕ} (core : Core n p)
    (hCubic : core.Cubic) (hConnected : core.Connected) (hGenus : p + 1 - n = 2 * k + 2)
    (y : Fin p → ℚ) (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (f : Frame core (k + 2)) (col : Fin p), f.coordsAt y col ≠ 0) :
    GeometricFibre.openOddCount core y (k + 2) % 2 = catalan (k + 1) % 2 := by
  obtain ⟨rfl, rfl⟩ := index_of_genus hCubic hGenus
  obtain ⟨request, hRequest⟩ := SimpleWallSupply.exists_positiveGeneral (catCore k) (k + 2)
  rw [← openOddCount_caterpillar hk hRequest.1]
  exact mod_two_eq_of_positiveGeneral (trivalentWalls _ _ _)
    (typeChanges (by omega) (by omega)) (by omega) (catCubicCore k) ⟨core, hCubic, hConnected⟩
    request y hRequest ⟨hPositive, hGeneral⟩

/-! ## 7.  Corollaries: the odd and the even forms -/

/-- **The even form of `CountSchedule.C34`.** For genus `2m + 2` and degree `m + 2`: over every
connected cubic core of that genus and every general positive request, the number of open
classes of odd multiplicity is even. By `evenC34_iff` it holds for `m ≥ 2` exactly when
`catalan (m + 1)` is even; at `m = 3` that is `C₄ = 14`. -/
def EvenC34 (m : ℕ) : Prop :=
  ∀ {n p : ℕ} (core : Core n p), core.Cubic → core.Connected → p + 1 - n = 2 * m + 2 →
    ∀ y : Fin p → ℚ, (∀ i, 0 < y i) →
      (∀ (k : Frame core (m + 2)) (col : Fin p), k.coordsAt y col ≠ 0) →
        Even (GeometricFibre.openOddCount core y (m + 2))

/-- **`CountSchedule.C34 k` holds, for `k ≥ 2`, exactly when `catalan (k + 1)` is odd.** One
direction is `openOddCount_mod_two`; the other evaluates `CountSchedule.C34 k` at the caterpillar
of loops. -/
theorem c34_iff {k : ℕ} (hk : 2 ≤ k) : CountSchedule.C34 k ↔ Odd (catalan (k + 1)) := by
  constructor
  · intro h
    obtain ⟨request, hRequest⟩ := SimpleWallSupply.exists_positiveGeneral (catCore k) (k + 2)
    have hOdd := h (catCore k) (catCore_cubic k) (catCore_connected k) (by omega) request
      hRequest.1 hRequest.2
    rwa [openOddCount_caterpillar hk hRequest.1] at hOdd
  · intro h n p core hCubic hConnected hGenus y hPositive hGeneral
    rw [Nat.odd_iff] at h ⊢
    rw [openOddCount_mod_two hk core hCubic hConnected hGenus y hPositive hGeneral, h]

/-- **`EvenC34 k` holds, for `k ≥ 2`, exactly when `catalan (k + 1)` is even.** -/
theorem evenC34_iff {k : ℕ} (hk : 2 ≤ k) : EvenC34 k ↔ Even (catalan (k + 1)) := by
  constructor
  · intro h
    obtain ⟨request, hRequest⟩ := SimpleWallSupply.exists_positiveGeneral (catCore k) (k + 2)
    have hEven := h (catCore k) (catCore_cubic k) (catCore_connected k) (by omega) request
      hRequest.1 hRequest.2
    rwa [openOddCount_caterpillar hk hRequest.1] at hEven
  · intro h n p core hCubic hConnected hGenus y hPositive hGeneral
    rw [Nat.even_iff] at h ⊢
    rw [openOddCount_mod_two hk core hCubic hConnected hGenus y hPositive hGeneral, h]

/-- The fourth Catalan number. Mathlib's list of values stops at `catalan_three`. -/
theorem catalan_four : catalan 4 = 14 := by
  norm_num [catalan_eq_centralBinom_div, Nat.centralBinom, Nat.choose]

/-- **Genus six**: `CountSchedule.C34 2`, the propagation step of the genus-six count
(`Assembly.c34_genusSix`), recovered from `openOddCount_mod_two` and `C₃ = 5`. -/
theorem c34_two : CountSchedule.C34 2 :=
  (c34_iff le_rfl).mpr (by rw [catalan_three]; exact ⟨2, rfl⟩)

/-- **Genus eight, even form.** Over every connected cubic core of genus eight, at every positive
general request, the number of open classes of odd multiplicity in degree five is even, because
`C₄ = 14`. -/
theorem evenC34_three : EvenC34 3 :=
  (evenC34_iff (by norm_num)).mpr (by rw [catalan_four]; exact ⟨7, rfl⟩)

end DraismaVargas.Count.EvenGenusParity
