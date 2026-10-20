module

public import DraismaVargasMarkedCount.MarkedCount.MarkedFrame
public import DraismaVargasCount.CrossCoreTransport
public import DraismaVargasCount.LollipopDivalentWitness
public import DraismaVargasCount.IndexPattern

@[expose] public section

/-!
# The lollipop side

**The lollipop fibre**: the geometric fibre of the lollipop core at the request `y` with tails,

  `LollipopFibre core mark y bridge loop d := GeometricFibre (attachLollipops core mark)
    (lollipopRequest y bridge loop) d`,

the object of the integer count, whose open classes and multiplicities do not depend on the positive
tails (`Correspondence.openMultCount_lollipop_tails`).

Here: the source vertex of a mark in a frame over the lollipop core (`lollipopMarkSource`), and
the local fact the multiplicity identity needs from the dichotomy at a mark (a ramified mark of a
member over the lollipop core is either a fold, `r_φ = 1`, or a transition, `r_φ = 0`): at a
mark, `0 ≤ r_φ ≤ 1`. These are `markRamification_lollipopMark_nonneg` (Riemann--Hurwitz) and
`markRamification_lollipopMark_le_one` (from change-minimality and the leaf fibre).
-/

namespace DraismaVargas.Count.MarkedCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ}

/-- **The lollipop fibre**: the geometric fibre over the lollipop core at the request `y`
with bridge lengths `bridge` and loop lengths `loop`. -/
def LollipopFibre (core : Core n p) (mark : Fin k → Fin n) (y : Fin p → ℚ)
    (bridge loop : Fin k → ℚ) (degree : ℕ) : Type 1 :=
  GeometricFibre (attachLollipops core mark) (lollipopRequest y bridge loop) degree

/-- The source vertex of mark `j` in a frame over the lollipop core: the branch vertex (surviving
valency three) identified with the old vertex `mark j`. -/
noncomputable def lollipopMarkSource {core : Core n p} {mark : Fin k → Fin n}
    (f : Frame (attachLollipops core mark) degree) (j : Fin k) : f.data.SourceVertex :=
  (f.ident.vertex.symm (oldVertex k (mark j))).1

/-- Riemann--Hurwitz at the mark. -/
theorem markRamification_lollipopMark_nonneg {core : Core n p} {mark : Fin k → Fin n}
    (f : Frame (attachLollipops core mark) degree) (j : Fin k) :
    0 ≤ markRamification f.data (lollipopMarkSource f j) :=
  markRamification_nonneg f.fullDim.valid _

/-- **Fold or transition, the part the multiplicity needs: `r_φ(u) ≤ 1` at a mark** (`r = 1` is the
fold, `r = 0` the transition). It holds at every branch vertex of a frame, and the mark is one: its
core vertex `oldVertex (mark j)` is a vertex of the lollipop core, so `ident` makes it a branch
vertex (surviving valency at least three).

*Proof.* By change-minimality (`FullDimensionalSourcePresentation.changeMinimal`),
`r(u) ≤ ch(φ(u)) = 3 - val φ(u)` (`IndexPattern.localRamification_le_targetChange`,
`IndexPattern.targetChange_eq_three_sub_valency`). If `φ(u)` were a leaf, `u` would be the core
vertex over it (`LollipopDivalentWitness.eq_coreVertex_of_surviving`), which has surviving valency
two (over a change-minimal leaf the one non-dangling vertex has valency two: Draisma--Vargas
Part I, arXiv:1909.12924, `rem-leaves-min-change`; here `LeafFibre.nonDanglingValency_coreVertex`),
not three. So `val φ(u) ≥ 2` and
`r(u) ≤ 1`. -/
theorem markRamification_lollipopMark_le_one {core : Core n p} {mark : Fin k → Fin n}
    (f : Frame (attachLollipops core mark) degree) (j : Fin k) :
    markRamification f.data (lollipopMarkSource f j) ≤ 1 := by
  have hThree : 3 ≤ nonDanglingValency f.data (lollipopMarkSource f j) :=
    (f.ident.vertex.symm (oldVertex k (mark j))).2
  set u := lollipopMarkSource f j
  have hLe := IndexPattern.localRamification_le_targetChange f.fullDim (wall := u.1.1)
    ⟨u.1.2, u.2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency f.fullDim u.1.1] at hLe
  have hPos := StableLocalProperties.incidentEdges_card_pos_of_changeMinimalAt f.data u.1.1
    (f.fullDim.changeMinimal u.1.1)
  unfold markRamification
  by_cases hCard : (GluingDatum.incidentEdges u.1.1).card = 1
  · exfalso
    have hLeaf : Count.IsLeafVertex f.target u.1.1 := hCard
    have hCore := LollipopDivalentWitness.eq_coreVertex_of_surviving f.fullDim (by omega) hLeaf
    have hTwo := LeafFibre.nonDanglingValency_coreVertex f.fullDim hLeaf
    rw [← hCore] at hTwo
    omega
  · omega

end DraismaVargas.Count.MarkedCount
