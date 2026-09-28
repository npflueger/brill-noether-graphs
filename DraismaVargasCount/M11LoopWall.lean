import DraismaVargasCount.M11StarParityFree
import DraismaVargas.LocalCases.M11CertifiedOpposite

/-!
# Loop walls are not M-11 walls of a full-dimensional member

Sources: Draisma–Vargas Part I, Case `{w2-r2-nd3-M-11}` (Figure 32, Equation (6));
Vargas, Part II, subsection "Maps to trees" (the pass-once condition, change-minimal
leaves, the local properties `prop-local`, case (r2), and their inheritance at limits
`lm:properties-inherit`) and the bridge-and-loop lemma `lm:bridge-and-loop`.

## The statement

At an M-11 wall whose two surviving double-direction occurrences lie on one stable row
(`M11StarParityFree.SameDoubleRow`, a *loop wall*), Equation (6)'s two split positions
could a priori be one star class, which would make the star parity clause fail when `s₀`
is odd (`M11StarParityFree.loop_parity_defect`).  This does not happen: **a loop wall is
never the limit of a full-dimensional member.**  The argument:

1. *(Part II, pass-once, inherited by limits.)*  Both loop ends lie above the double
   target edge `t₂`; pass-once lets a row repeat a target edge only if that edge meets a
   leaf, and `t₂`'s other end `w₀` is divalent, so `t₂` is a **leaf edge**.
2. *(change-minimal leaf, `prop-local` (r2).)*  Above that leaf there is exactly one
   non-dangling source vertex, with exactly two non-dangling edges, so the non-dangling
   fibre of `t₂` is the two loop ends: **column `t₂` of the limit matrix is `2 e_h`**.
3. *(This file.)*  Position `0`'s new column is also `2 e_h` (`M11SplitLimitMatrix.matrix_new`
   under `SameDoubleRow`), so its square matrix has two equal columns and `s₀ = 0`; then
   `s₁ = s₀ = 0` (`M11StarParityFree.signedMult_one_eq_zero`) and `s₂ = -2 s₀ = 0`
   (`M11StarParityFree.signedMult_two_eq`).  All three members of Equation (6) are
   singular -- but the incoming member, the regrowth's own cover, is nonsingular
   (`M11CertifiedOpposite.incomingDet_ne_zero`).

## What is proved

* `squareMatrix_zero_det_eq_zero_of_column` -- step 3's linear algebra: any retained
  column of the limit equal to `2 e_h` (`h` the new-old row) kills position `0`.  No
  loop hypothesis.
* `signedMult_eq_zero_of_loopColumn` -- at a loop wall with that column, all three
  signed multiplicities of Equation (6) vanish.
* `false_of_loopColumn` -- and that contradicts the incoming member's full rank.

## The column hypothesis `hCol`

* **Steps 1--2 are not proved in this file.**  `false_of_loopColumn` takes the column fact
  `hCol` (column `t` of the wall datum's stable matrix is `2 e_h`) as a hypothesis, for
  an arbitrary retained target edge `t`; the argument above supplies it at
  `t = star.edge profile.doubleLabel` from pass-once and the leaf fibre **of the limit**.
  The modules `DraismaVargasCount.PassOnceLollipop` (pass-once at a lollipop) and
  `DraismaVargasCount.LeafFibre` (leaf fibres) prove the analogous facts for a full-dimensional
  *presentation*, not for a contracted wall datum.  `DraismaVargasCount.M11StarCensusProof`
  carries them across: `M11StarCensusProof.joined_false` supplies `hCol` at the joined
  member, for the retained target edge at the leaf of the loop row, and
  `M11StarCensusProof.not_sameDoubleRow_of_regrowth` concludes that loop walls do not
  occur at M-11 regrowths.
* This file works with the wall datum's matrices only; it does not use
  `GeometricFibre`, `Star` or `M11StarParityFree.M11StarCensus`.
-/

namespace DraismaVargas.Count.M11LoopWall

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open W4StableSource

variable {target : CFGraph} {degree : ℕ} {wallV : target.V} {data : GluingDatum target degree}
  {star : W2R1Target.TwoStar target wallV} (input : SecondEquation.W2SourceInput data star)
  {block : W4Assembly.WallBlock data wallV}
  (profile : W2R2SourceProfile.SourceProfile data star block)
  (hCard : (data.vertexPartition wallV).blockCard block.1 = 2)
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]

/-- **Two equal columns in position `0`.**  If some retained column `t` of the wall
datum's stable matrix is twice the indicator of the new-old row -- which is exactly
position `0`'s new column -- then position `0`'s square matrix is singular. -/
theorem squareMatrix_zero_det_eq_zero_of_column
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)
    (t : target.edges)
    (hCol : ∀ path : StablePath data, StableSourceMatrix.matrix data path t =
      if path = (M11SplitRowDescent.newOldEdge profile hCard).stablePath then 2 else 0) :
    (M11CommonBalance.squareMatrix input profile hCard initial 0).det = 0 := by
  classical
  set e := M11CommonBalance.targetCoordinates input profile hCard initial
  refine Matrix.det_zero_of_column_eq (i := e.symm none) (j := e.symm (some t)) ?_ ?_
  · intro h
    exact absurd (e.symm.injective h) (by simp)
  · intro row
    rw [M11CommonBalance.squareMatrix_common, M11CommonBalance.squareMatrix_common,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      M11CommonBalance.commonMatrix_retained, hCol]
    exact M11SplitLimitMatrix.matrix_new input profile hCard _

/-- **At a loop wall with a `2 e_h` column, Equation (6) is identically zero**: all three
signed multiplicities vanish. -/
theorem signedMult_eq_zero_of_loopColumn (hConnected : graph_connected target)
    (hGenus : genus target = 0) (hRow : M11StarParityFree.SameDoubleRow profile hCard)
    (initial : StableLengthMatrixLabelling
      (M11RemoteCandidates.candidates input profile hCard 0).datum coordinate)
    (hbal : ∑ q : Fin 3,
      signedMult (M11CommonBalance.labelling input profile hCard initial q).presentation = 0)
    (t : target.edges)
    (hCol : ∀ path : StablePath data, StableSourceMatrix.matrix data path t =
      if path = (M11SplitRowDescent.newOldEdge profile hCard).stablePath then 2 else 0)
    (q : Fin 3) :
    signedMult (M11CommonBalance.labelling input profile hCard initial q).presentation = 0 := by
  have h0 : signedMult (M11CommonBalance.labelling input profile hCard initial 0).presentation
      = 0 := by
    change _ * (M11CommonBalance.squareMatrix input profile hCard initial 0).det = 0
    rw [squareMatrix_zero_det_eq_zero_of_column input profile hCard initial t hCol, mul_zero]
  fin_cases q
  · exact h0
  · exact (M11StarParityFree.signedMult_one_eq_zero input profile hCard initial hConnected
      hGenus hRow).trans h0
  · change signedMult (M11CommonBalance.labelling input profile hCard initial 2).presentation = 0
    rw [M11StarParityFree.signedMult_two_eq input profile hCard initial hConnected hGenus hRow
      hbal, h0, mul_zero]

/-- **A loop wall with a `2 e_h` column has no full-dimensional incoming member.**
Equation (6) holds at every incoming presentation
(`M11IncomingDenominator.sum_signedMult_eq_zero`), all three terms vanish
(`signedMult_eq_zero_of_loopColumn`), but the incoming term's determinant is nonzero
(`M11CertifiedOpposite.incomingDet_ne_zero`). -/
theorem false_of_loopColumn (hConnected : graph_connected target)
    (hGenus : genus target = 0) (hRow : M11StarParityFree.SameDoubleRow profile hCard)
    (incoming : Fin 3)
    (incomingFD : FullDimensionalSource.FullDimensionalSourcePresentation
      (M11RemoteCandidates.candidates input profile hCard incoming).datum coordinate)
    (t : target.edges)
    (hCol : ∀ path : StablePath data, StableSourceMatrix.matrix data path t =
      if path = (M11SplitRowDescent.newOldEdge profile hCard).stablePath then 2 else 0) :
    False := by
  set initial := M11FullDimensional.initialLabelling input profile hCard incoming incomingFD
  have hbal := M11IncomingDenominator.sum_signedMult_eq_zero input profile hCard hConnected
    hGenus incoming initial incomingFD
  have hq := signedMult_eq_zero_of_loopColumn input profile hCard hConnected hGenus hRow
    initial hbal t hCol incoming
  have hDet := M11CertifiedOpposite.incomingDet_ne_zero input profile hCard incoming incomingFD
  have hD := denominatorProduct_pos
    (M11CommonBalance.labelling input profile hCard initial incoming).presentation
  change (denominatorProduct _ : ℚ) / 2 ^ leafCount _ *
    (M11CommonBalance.squareMatrix input profile hCard initial incoming).det = 0 at hq
  rcases mul_eq_zero.mp hq with h | h
  · rcases div_eq_zero_iff.mp h with h' | h'
    · exact absurd h' (by exact_mod_cast hD.ne')
    · exact absurd h' (pow_ne_zero _ two_ne_zero)
  · exact hDet h

end DraismaVargas.Count.M11LoopWall
