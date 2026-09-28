import DraismaVargasCount.BallotSlopeSeparation
import DraismaVargas.LocalCases.NonDanglingValency

/-!
# The geometric half of the slope conditions: what they actually cost

**Source.**  Vargas, Part II (arXiv:2609.09109), part (1) of `prop-caterpillar-ballot`: in
every full-dimensional tropical morphism whose deletion of dangling trees is the metric
caterpillar of loops, the slopes `s_i` on the path edges satisfy `s_1 = s_{g-1} = 2`,
`s_i ≥ 1`, and `s_i - s_{i-1} = ±1` for `i = 2, …, g-1`.  The *combinatorial* half (the
object `Slopes g` and its Catalan count) is `Count/Slopes.lean`.  This module is about the
geometric half.

## What the proof of `prop-caterpillar-ballot`(1) uses, itemised

The proof is four sentences and uses exactly four inputs at the interior spine
branch vertex `B_i`:

1. **the index at the bridge incident to `L(A_i)` is 2** -- `lm:bridge-and-loop`;
2. **`r_φ(L(B_i)) = 0`** -- via
   `lm:combinatorial-structure-caterpillar-of-loops`, i.e. the valency census;
3. **the `r_φ` formula** `r = 2(m(A) - 1) - Σ_e (m(e) - 1)`;
4. **balancing**, `m(B_i) ≥ max (s_{i-1}, s_i)`.

Inputs 3 and 4 are in Part I's library, unconditionally and in the exact
shape the proof wants:
`StableLocalProperties.localRamification_eq_nonDangling_form` is 3
(`r = nd(A) - 2 + 2|A| - Σ_{surviving} m(e)`, which is the same identity after
the substitution `Σ_e (m(e)-1) = Σ_{surviving} m(e) - nd(A)`), and
`StableLocalProperties.sourceEdgeIndex_le_blockCard` is 4.  **So the whole of the
step condition is proved here, over an arbitrary gluing datum, with 1 and 2 as
named hypotheses and nothing else.**  That is `slopeStepRel_of_trivalent_unramified`.

Input 2 is, in this library's encoding, *equivalent* to "`φ(B_i)` is trivalent
in `T`", and that equivalence is proved below rather than argued:
`localRamification_eq_zero_iff_trivalent_target`.  So the census enters this module
only through the single sentence *"`φ(B_i)` is not one of the `g` divalent images
`φ(A_j)`"*, never through the Riemann--Hurwitz count as such.

## What is proved

* `slopeStepRel_of_sum_of_le` -- the arithmetic of the proof, with no geometry:
  `a + b + 2 = 2M + 1` together with `a ≤ M` and `b ≤ M` forces
  `b = a + 1 ∨ a = b + 1`.  Both bounds are needed; the parity alone gives only
  `a ≠ b`.
* `survivingIndexSum_of_trivalent_unramified` -- at a source vertex of
  surviving valency three and vanishing local ramification the surviving
  dilation indices sum to `2|A| + 1`.  This is the displayed equation of the proof,
  `s_{i-1} + s_i = 2 m(B_i) - 1`, before any caterpillar enters.
* `slopeStepRel_of_trivalent_unramified` -- **the headline.**  The same vertex,
  with its three surviving indices named as `a`, `b` and `2`, satisfies
  `SlopeStepRel a b`.  No core, no request, no genericity, no openness, no
  oddness, no caterpillar.
* `localRamification_eq_zero_of_trivalent_target` -- change-minimality turns
  "the image is trivalent" into "every block above it is unramified".
* `one_le_localRamification_of_divalent_target`,
  `localRamification_eq_zero_iff_trivalent_target` -- the converse and the
  resulting **dichotomy at a branch vertex**: with surviving valency three,
  `r_φ(A) = 0 ↔ φ(A)` is trivalent.  So input 2 is exactly the one
  sentence "`φ(B_i)` is not one of the `g` divalent images", and nothing more of
  the census enters this module.
* `nonDanglingValency_le_two_of_leaf` -- a source vertex above a **leaf** of the
  target has surviving valency at most two, hence is never a branch vertex of
  the stable graph.  This is unconditional (validity, change-minimality and the
  dangling-no-glue property only) and is the cheap half of the dichotomy
  `val_T (φ(B_i)) ∈ {2, 3}`.
* `Slopes.ofFun`, `Slopes.slope_ofFun` -- the constructor missing from
  `Count/Slopes.lean`: a function `σ : ℕ → ℕ` with the four conditions of
  `prop-caterpillar-ballot`(1) *is* a `Slopes g`, and its extended slope function is `σ`
  on the paper's index range.
* `BallotSlopes.exists_ballotCoreDiag_of_values` -- the recognition step: a
  core-slot diagonal taking the value `2` on leaf slots, `1/2` on stem slots and
  `1 / σ i` on the spine slot of index `i` **is** `ballotCoreDiag m s` for a
  genuine `s : Slopes (2 * (m + 1))`, as soon as `σ` satisfies those conditions.

## What is not proved here

* **No member is constructed and no fibre is exhausted.**  `FibreMember`,
  `GeometricFibre`, `openOddCount`, `BallotFamily` and `BallotClassification`
  do not occur below.
* **The two inputs 1 and 2 above are hypotheses here, not theorems.**  Nothing below
  proves that a bridge has index two, nor that the image of a spine branch
  vertex is trivalent.  Both are proved elsewhere:
  `LollipopBridgeFibreWitness.exists_bridge_loopBranch` and
  `LollipopDivalent.loopImage_divalent`.  `slopeStepRel_of_trivalent_unramified` takes
  `nonDanglingValency = 3` and `localRamification = 0` as hypotheses and takes
  the *naming* of the three surviving indices as a hypothesis too.
* **Nothing identifies a slope with a matrix entry.**  That the surviving
  occurrence over a spine slot is unique, so that `1 / s_i` is the diagonal
  entry of `A_φ` there (`A_φ` diagonal), is not proved or assumed below;
  `exists_ballotCoreDiag_of_values` takes the three diagonal values as hypotheses about
  an arbitrary function `d`.
* **Nothing about the boundary conditions `s_1 = s_{g-1} = 2` is proved.**  They
  are hypotheses of `Slopes.ofFun` (`hone`, `hlast`).  Part II attributes them to
  `lm:combinatorial-structure-caterpillar-of-loops`; in this library's
  encoding they come from `lm:bridge-and-loop` and not from the census, because the first
  and last spine slots of `catCore m` are themselves the bridges of the two end
  lollipops.  (Checked against `catCore`'s endpoint maps: slot `0` is a
  self-loop at core vertex `0` and slot `1` runs from core vertex `0` to core
  vertex `1`, so core vertex `0` is a trivalent vertex incident to a loop and to
  the bridge `h_1`; symmetrically slot `6m+2` is a self-loop at core vertex
  `4m+1`, which slot `6m+1` reaches.)  Either way it is not proved here.
* `nonDanglingValency_le_two_of_leaf` assumes change-minimality *at that leaf*
  and validity; it says nothing about which source vertices lie above a leaf.
-/

namespace DraismaVargas.Count

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.NonDanglingValency

/-! ## 1.  The arithmetic of the proof of `prop-caterpillar-ballot`(1) -/

/-- **The proof of `prop-caterpillar-ballot`(1), with the geometry removed.**  If two
slopes and a bridge of index
`2` at a block of size `M` have total surviving index `2M + 1`, and each slope is
at most `M` (balancing), then the two slopes differ by exactly one.

Both bounds are load-bearing: the parity of `2M + 1` alone gives only `a ≠ b`,
and it is `a ≤ M`, `b ≤ M` that collapse `|a - b|` from "odd" to "one". -/
theorem slopeStepRel_of_sum_of_le {a b M : ℕ}
    (hsum : a + b + 2 = 2 * M + 1) (ha : a ≤ M) (hb : b ≤ M) :
    SlopeStepRel a b := by
  unfold SlopeStepRel
  omega

/-! ## 2.  The `r_φ` formula at a trivalent unramified source vertex -/

namespace SlopesGeometric

variable {target : CFGraph} {degree : ℕ}

/-- The total dilation index of the **surviving** occurrences at a source
vertex: Part II's `Σ_{e ∋ A, e not dangling} m(e)`. -/
noncomputable def survivingIndexSum (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : ℤ :=
  ∑ edge ∈ (Finset.univ : Finset (IncidentSourceEdge data vertex)).filter
    (fun edge ↦ ¬ IsDangling data edge.1), (data.sourceEdgeIndex edge.1 : ℤ)

/-- **The displayed equation of the proof of `prop-caterpillar-ballot`(1).**  At a source
vertex of surviving
valency three and vanishing local ramification the surviving dilation indices
add up to `2 |A| + 1`.  With the three indices named `s_{i-1}`, `s_i` and `2`
this is `s_{i-1} + s_i = 2 m(B_i) - 1`. -/
theorem survivingIndexSum_of_trivalent_unramified
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex)
    (hValency : nonDanglingValency data vertex = 3)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0) :
    survivingIndexSum data vertex =
      2 * ((data.vertexPartition vertex.1.1).blockCard vertex.1.2 : ℤ) + 1 := by
  have hForm := localRamification_eq_nonDangling_form data hNoGlue vertex
  rw [hZero, hValency] at hForm
  unfold survivingIndexSum
  push_cast at hForm ⊢
  linarith

/-- **The geometric half of the step condition of `prop-caterpillar-ballot`(1).**  A
source vertex of
surviving valency three and vanishing local ramification, whose three surviving
occurrences have indices `a`, `b` and `2`, has `SlopeStepRel a b`.

The two balancing hypotheses `ha`, `hb` are
`StableLocalProperties.sourceEdgeIndex_le_blockCard` at the two occurrences, and are
stated rather than derived because this lemma does not know which occurrences
carry `a` and `b`. -/
theorem slopeStepRel_of_trivalent_unramified
    (data : GluingDatum target degree) (hNoGlue : DanglingEdgeNoGlue data)
    (vertex : data.SourceVertex)
    (hValency : nonDanglingValency data vertex = 3)
    (hZero : data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0)
    {a b : ℕ}
    (hSum : survivingIndexSum data vertex = (a : ℤ) + (b : ℤ) + 2)
    (ha : a ≤ (data.vertexPartition vertex.1.1).blockCard vertex.1.2)
    (hb : b ≤ (data.vertexPartition vertex.1.1).blockCard vertex.1.2) :
    SlopeStepRel a b := by
  have hEq := survivingIndexSum_of_trivalent_unramified data hNoGlue vertex hValency hZero
  rw [hSum] at hEq
  refine slopeStepRel_of_sum_of_le (M := (data.vertexPartition vertex.1.1).blockCard vertex.1.2)
    ?_ ha hb
  exact_mod_cast hEq

/-! ## 3.  Where the vanishing of `r_φ` comes from -/

/-- **Change-minimality above a trivalent target vertex.**  `ch(v) = 3 - val(v)`
is `ChangeMinimalAt`, so a trivalent image has no change at all, and every block
above it is unramified.  This is the only form in which the valency census of
`T^CL_g` is used by `prop-caterpillar-ballot`(1). -/
theorem localRamification_eq_zero_of_trivalent_target
    (data : GluingDatum target degree) (hValid : data.Valid) (vertex : target.V)
    (hMinimal : data.ChangeMinimalAt vertex)
    (hValency : (GluingDatum.incidentEdges vertex).card = 3)
    (block : (data.vertexPartition vertex).Blocks) :
    data.localRamification vertex block = 0 := by
  refine localRamification_eq_zero_of_targetChange_eq_zero data hValid vertex ?_ block
  unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hMinimal
  rw [hValency] at hMinimal
  push_cast at hMinimal
  linarith

/-- The local ramification at one block never exceeds the change at its target
vertex, because the change is the sum of nonnegative local ramifications. -/
theorem localRamification_le_targetChange
    (data : GluingDatum target degree) (hValid : data.Valid) (vertex : target.V)
    (block : (data.vertexPartition vertex).Blocks) :
    data.localRamification vertex block ≤ data.targetChange vertex := by
  unfold GluingDatum.targetChange
  exact Finset.single_le_sum
    (f := fun b ↦ data.localRamification vertex b)
    (fun b _ ↦ data.localRamification_nonneg vertex (hValid.2 vertex) b)
    (Finset.mem_univ block)

/-- **No branch vertex lies above a leaf of the target.**  A source vertex above
a change-minimal leaf has surviving valency at most two, so it can never be a
`BranchVertex` (which asks for at least three).

The proof is the two inequalities of Part I's library read together.  Write `nd`, `M`, `r`
for the surviving valency, the block size and the local ramification.  The
occurrence count `N = r + 2 + M(val - 2)` is `r + 2 - M` at a leaf and dominates
`nd`, so `nd ≤ r + 2 - M`; and `r = nd - 2 + 2M - Σ` with `Σ ≥ nd` gives
`r ≤ 2M - 2`, whence `nd ≤ M`.  Change-minimality at the leaf gives `ch = 2` and
so `r ≤ 2`, whence `nd ≤ 4 - M`.  Adding the last two bounds gives `2 nd ≤ 4`. -/
theorem nonDanglingValency_le_two_of_leaf
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoGlue : DanglingEdgeNoGlue data) (vertex : data.SourceVertex)
    (hMinimal : data.ChangeMinimalAt vertex.1.1)
    (hValency : (GluingDatum.incidentEdges vertex.1.1).card = 1) :
    nonDanglingValency data vertex ≤ 2 := by
  have hForm := localRamification_eq_nonDangling_form data hNoGlue vertex
  have hLower := le_sum_sourceEdgeIndex_nonDangling data vertex
  have hCard := card_incidentSourceEdge_eq_localRamification_form data vertex
  have hNd : (nonDanglingValency data vertex : ℤ) ≤
      (Fintype.card (IncidentSourceEdge data vertex) : ℤ) := by
    exact_mod_cast nonDanglingValency_le_card_incidentSourceEdge data vertex
  have hChange := localRamification_le_targetChange data hValid vertex.1.1
    ⟨vertex.1.2, vertex.2⟩
  have hMin : data.targetChange vertex.1.1 = 2 := by
    unfold GluingDatum.ChangeMinimalAt GluingDatum.targetExcess at hMinimal
    rw [hValency] at hMinimal
    push_cast at hMinimal
    linarith
  rw [hValency] at hCard
  rw [hMin] at hChange
  have hFinal : (nonDanglingValency data vertex : ℤ) ≤ 2 := by
    push_cast at hForm hLower hCard hNd ⊢
    linarith
  exact_mod_cast hFinal

/-- **The converse, at a branch vertex.**  A source vertex of surviving valency
at least three above a *divalent* target vertex is ramified: there
`N(A) = r + 2`, and `nd(A) ≤ N(A)`. -/
theorem one_le_localRamification_of_divalent_target
    (data : GluingDatum target degree) (vertex : data.SourceVertex)
    (hTargetValency : (GluingDatum.incidentEdges vertex.1.1).card = 2)
    (hBranch : 3 ≤ nonDanglingValency data vertex) :
    1 ≤ data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ := by
  have hCard := card_incidentSourceEdge_eq_localRamification_form data vertex
  have hNd : (nonDanglingValency data vertex : ℤ) ≤
      (Fintype.card (IncidentSourceEdge data vertex) : ℤ) := by
    exact_mod_cast nonDanglingValency_le_card_incidentSourceEdge data vertex
  have hThree : (3 : ℤ) ≤ (nonDanglingValency data vertex : ℤ) := by exact_mod_cast hBranch
  rw [hTargetValency] at hCard
  push_cast at hCard
  linarith

/-- **The dichotomy at a branch vertex, machine-checked.**  Under validity,
change-minimality and dangling-no-glue, a source vertex of surviving valency
three lies above a target vertex of valency two or three, and
`r_φ(A) = 0` **if and only if** that image is trivalent.

This is the precise cost of input 2 of that proof: the valency census is used by
`prop-caterpillar-ballot`(1) only to say that `φ(B_i)` is *not* one of the `g`
divalent images, never as a Riemann--Hurwitz count in its own right. -/
theorem localRamification_eq_zero_iff_trivalent_target
    (data : GluingDatum target degree) (hValid : data.Valid)
    (hNoGlue : DanglingEdgeNoGlue data) (vertex : data.SourceVertex)
    (hMinimal : data.ChangeMinimalAt vertex.1.1)
    (hValency : nonDanglingValency data vertex = 3) :
    data.localRamification vertex.1.1 ⟨vertex.1.2, vertex.2⟩ = 0 ↔
      (GluingDatum.incidentEdges vertex.1.1).card = 3 := by
  have hLe := data.incidentEdges_card_le_three_of_changeMinimalAt hValid _ hMinimal
  have hPos := incidentEdges_card_pos_of_changeMinimalAt data vertex.1.1 hMinimal
  have hNotLeaf : (GluingDatum.incidentEdges vertex.1.1).card ≠ 1 := by
    intro hOne
    have := nonDanglingValency_le_two_of_leaf data hValid hNoGlue vertex hMinimal hOne
    omega
  constructor
  · intro hZero
    rcases (by omega : (GluingDatum.incidentEdges vertex.1.1).card = 2 ∨
        (GluingDatum.incidentEdges vertex.1.1).card = 3) with hTwo | hThree
    · have := one_le_localRamification_of_divalent_target data vertex hTwo (by omega)
      omega
    · exact hThree
  · intro hThree
    exact localRamification_eq_zero_of_trivalent_target data hValid _ hMinimal hThree _

end SlopesGeometric

/-! ## 4.  A slope sequence from a slope function -/

namespace Slopes

/-- **The conditions of `prop-caterpillar-ballot`(1) build a `Slopes`.**  A function
`σ : ℕ → ℕ` obeying
`σ 1 = 2`, `σ (g-1) = 2`, positivity on `1, …, g-1` and the step relation on
consecutive indices of that range *is* a slope sequence of genus `g`. -/
def ofFun (g : ℕ) (σ : ℕ → ℕ)
    (hone : σ 1 = 2) (hlast : σ (g - 1) = 2)
    (hpos : ∀ i, 1 ≤ i → i ≤ g - 1 → 1 ≤ σ i)
    (hstep : ∀ i, 1 ≤ i → i + 1 ≤ g - 1 → SlopeStepRel (σ i) (σ (i + 1))) :
    Slopes g where
  slopes := List.ofFn fun j : Fin (g - 1) ↦ σ (j.val + 1)
  length_eq := List.length_ofFn
  head_eq := by
    intro s hs
    rw [List.head?_eq_getElem?] at hs
    rcases Nat.eq_zero_or_pos (g - 1) with hg | hg
    · rw [List.getElem?_eq_none (by simp [hg])] at hs
      exact absurd hs (by simp)
    · rw [List.getElem?_eq_getElem (by simpa using hg)] at hs
      simp only [Option.mem_def, Option.some.injEq, List.getElem_ofFn] at hs
      rw [← hs]
      exact hone
  getLast_eq := by
    intro s hs
    rw [List.getLast?_eq_getElem?] at hs
    rcases Nat.eq_zero_or_pos (g - 1) with hg | hg
    · rw [List.getElem?_eq_none (by simp [hg])] at hs
      exact absurd hs (by simp)
    · rw [List.getElem?_eq_getElem (by simp; omega)] at hs
      simp only [Option.mem_def, Option.some.injEq, List.getElem_ofFn] at hs
      rw [← hs]
      simp only [List.length_ofFn]
      rw [show g - 1 - 1 + 1 = g - 1 by omega]
      exact hlast
  one_le := by
    intro s hs
    rw [List.mem_ofFn] at hs
    obtain ⟨j, rfl⟩ := hs
    exact hpos (j.val + 1) (by omega) (by omega)
  step := by
    rw [List.isChain_iff_getElem]
    intro i hi
    simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn]
    exact hstep (i + 1) (by omega) (by omega)

/-- On the paper's index range the extended slope function of `ofFun g σ …` is `σ`. -/
theorem slope_ofFun {g : ℕ} {σ : ℕ → ℕ}
    {hone : σ 1 = 2} {hlast : σ (g - 1) = 2}
    {hpos : ∀ i, 1 ≤ i → i ≤ g - 1 → 1 ≤ σ i}
    {hstep : ∀ i, 1 ≤ i → i + 1 ≤ g - 1 → SlopeStepRel (σ i) (σ (i + 1))}
    {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ g - 1) :
    (ofFun g σ hone hlast hpos hstep).slope i = σ i := by
  have hlt : i - 1 < g - 1 := by omega
  show (List.ofFn fun j : Fin (g - 1) ↦ σ (j.val + 1)).getD (i - 1) 2 = σ i
  rw [← List.getElem_eq_getD (l := List.ofFn fun j : Fin (g - 1) ↦ σ (j.val + 1))
      (i := i - 1) (h := by simpa using hlt) 2, List.getElem_ofFn]
  show σ (i - 1 + 1) = σ i
  congr 1
  omega

end Slopes

/-! ## 5.  Recognising `ballotCoreDiag` -/

namespace BallotSlopes

open DraismaVargas.LocalCases.CaterpillarPruning (IsLeafEdge)

/-- **The recognition step.**  A function on core slots that reads `2` on the
leaf slots, `1/2` on the stem slots and `1 / σ i` on the spine slot of the paper's index
`i` is `ballotCoreDiag m s` for a genuine slope sequence `s`, as soon as `σ`
satisfies the four conditions of `prop-caterpillar-ballot`(1) at `g = 2m + 2`.

This is the step that turns "the slopes of this morphism obey the ballot
conditions" into the form `DraismaVargasCount.BallotSlopeSeparation` consumes, namely an
equation between a member's `coreDiag` and `ballotCoreDiag m s`. -/
theorem exists_ballotCoreDiag_of_values {m : ℕ} (d : Fin (6 * m + 3) → ℚ)
    (σ : ℕ → ℕ)
    (hone : σ 1 = 2) (hlast : σ (2 * m + 1) = 2)
    (hpos : ∀ i, 1 ≤ i → i ≤ 2 * m + 1 → 1 ≤ σ i)
    (hstep : ∀ i, 1 ≤ i → i + 1 ≤ 2 * m + 1 → SlopeStepRel (σ i) (σ (i + 1)))
    (hleaf : ∀ slot : Fin (6 * m + 3), IsLeafEdge m slot → d slot = 2)
    (hspine : ∀ slot : Fin (6 * m + 3), slot.val % 3 = 1 →
      d slot = 1 / (σ ((slot.val + 2) / 3) : ℚ))
    (hstem : ∀ slot : Fin (6 * m + 3), slot.val % 3 = 2 → slot.val ≠ 6 * m + 2 →
      d slot = 1 / 2) :
    ∃ s : Slopes (2 * (m + 1)), d = ballotCoreDiag m s := by
  have hg : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  refine ⟨Slopes.ofFun (2 * (m + 1)) σ hone (by rw [hg]; exact hlast)
    (fun i h1 h2 ↦ hpos i h1 (by omega)) (fun i h1 h2 ↦ hstep i h1 (by omega)), ?_⟩
  funext slot
  have hlt := slot.isLt
  by_cases hleafSlot : IsLeafEdge m slot
  · rw [hleaf slot hleafSlot, ballotCoreDiag_leaf _ hleafSlot]
  · have hnot : slot.val % 3 ≠ 0 ∧ slot.val ≠ 6 * m + 2 := by
      refine ⟨fun h ↦ hleafSlot (Or.inl h), fun h ↦ hleafSlot (Or.inr h)⟩
    by_cases hspineSlot : slot.val % 3 = 1
    · rw [hspine slot hspineSlot, ballotCoreDiag_spine _ hspineSlot,
        Slopes.slope_ofFun (by omega) (by omega)]
    · rw [hstem slot (by omega) hnot.2, ballotCoreDiag_stem _ (by omega) hnot.2]

end BallotSlopes

end DraismaVargas.Count
