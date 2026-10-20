module

public import DraismaVargasMarkedCount.MarkedCount.Restriction
public import DraismaVargasMarkedCount.MarkedCount.Regrowth
public import DraismaVargasMarkedCount.MarkedCount.CorrRegrowRestrict
public import DraismaVargasCount.IntegerCount.WeightedCount

@[expose] public section

/-!
# The lollipop lemma on classes

**The lollipop lemma**: restriction and regrowth are mutually inverse on classes,

  `lollipopClassEquiv hc : FrameClass (attachLollipops core mark) d ≃ MarkedFrameClass core mark d`,

request-free, preserving the multiplicity (`markedAbsMult_lollipopClassEquiv`), and matching
openness at `y` with openness at `y` with any positive tails (`openAt_lollipopClassEquiv_iff`). So
the open classes over the lollipop core at `(y, β, λ)` are the marked fibre at `y`
(`lollipopFibreEquiv`), for **every** positive `β, λ` (no tail needs to be long: the bridge and loop
columns are supported on their own rows, so the tails do not enter the other coordinates), and

  `markedCount core mark y d = openMultCount (attachLollipops core mark) (y, β, λ) d`

(`markedCount_eq_openMultCount`), the weighted count `openMultCount` on the lollipop core.
Corollaries: the weighted count on the lollipop core does not depend on the tails
(`openMultCount_lollipop_tails`), and the marked fibre is finite (`finite_markedFibre`).

**Genericity**, with every mark in the core ramified: `general_lollipop_of_general` (forward:
if no marked frame has a zero coordinate at `y`, then no frame of the lollipop core has one at
`(y, β, λ)` for nonzero tails; this is the direction the marked count uses) and
`general_of_general_lollipop` (the converse). With an unramified mark in the core the converse
would fail: genericity of the lollipop core does not see the position of the unramified mark,
which may sit at a vertex of a once-marked frame. That case cannot be stated here, because
unramified marks are never put into the core.

## The inverse laws

`restrictFrame_regrowFrame` and `regrowFrame_restrictFrame`, the two inverse laws up to
isomorphism, hold for every number `k` of marks; they are proved in the helper modules
`CorrRestrictRegrow` (`restrictRegrowIso`) and `CorrRegrowRestrict` (`regrowRestrictIso`).
Everything else here is proved from them and from the modules on marked frames, the lollipop
side, restriction and regrowth.
-/

namespace DraismaVargas.Count.MarkedCount

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open DraismaVargas.Count.CrossCoreTransport (FrameClass)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n}

/-! ## 1.  The inverse laws -/

/-- **Restriction after regrowth is the identity**, up to isomorphism over the marked core (half
of the bijection of the lollipop lemma).

*Proof* (`CorrRestrictRegrow.restrictRegrowIso`). In the regrowth, the branch that restriction finds
is the one regrowth attached (`w_j = wSV j`, `φ(w_j) = midV j`, `φ(C_j) = tipV j`), so the kept
target vertices are the old ones. Restriction keeps the partitions, and regrowth kept those of
`κ` on the old part, so the isomorphism is the old-vertex inclusion read backwards, with identity
sheet permutations. -/
theorem restrictFrame_regrowFrame (hc : IsMarkedCubic core mark)
    (κ : MarkedFrame core mark degree) :
    Nonempty (MarkedFrameIso (restrictFrame hc (regrowFrame hc κ)) κ) :=
  ⟨CorrRestrictRegrow.restrictRegrowIso hc κ⟩

/-- **Regrowth after restriction is the identity**, up to isomorphism over the lollipop core, with
`P :=` the sheets of `e_b`.

*Proof* (`CorrRegrowRestrict.regrowRestrictIso`). By the bridge-and-loop lemma and the dangling
bookkeeping over the branch (`RestrictLollipop`, `RestrictBranch`), the fibre of a lollipop frame
over the branch `B_j` is determined by the 2-subset `P_f` of sheets of `e_b`: `{P_f} ∪ singletons`
over `t_b`, `u'` and `v_C`, discrete over `t_l`. Regrowth's `pair a b` reproduces it after an
in-block sheet permutation `{a, b} ↦ P_f` at each piece of the branch (two transpositions inside the
block `S` of the mark, and `swap a b` where a piece names `P_f` by its other sheet), the identity
elsewhere, so the two data are isomorphic over the identity of the lollipop core. -/
theorem regrowFrame_restrictFrame (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) :
    Nonempty (FrameIso (regrowFrame hc (restrictFrame hc f)) f) :=
  ⟨CorrRegrowRestrict.regrowRestrictIso hc f⟩

/-! ## 2.  The bijection on classes -/

/-- **The lollipop lemma, on classes**: restriction, with inverse regrowth. -/
noncomputable def lollipopClassEquiv (hc : IsMarkedCubic core mark) :
    FrameClass (attachLollipops core mark) degree ≃ MarkedFrameClass core mark degree where
  toFun := Quotient.lift (fun f ↦ MarkedFrameClass.mk (restrictFrame hc f))
    fun _ _ h ↦ h.elim fun iso ↦ MarkedFrameClass.mk_eq_mk_of_iso (restrictFrame_respects hc iso)
  invFun := Quot.lift (fun κ ↦ FrameClass.mk (regrowFrame hc κ))
    fun _ _ h ↦ h.elim fun iso ↦ FrameClass.mk_eq_mk_iff.mpr (regrowFrame_respects hc iso)
  left_inv x := Quotient.inductionOn x fun f ↦
    FrameClass.mk_eq_mk_iff.mpr (regrowFrame_restrictFrame hc f)
  right_inv x := Quot.inductionOn x fun κ ↦
    MarkedFrameClass.mk_eq_mk_of_iso (restrictFrame_regrowFrame hc κ)

@[simp] theorem lollipopClassEquiv_mk (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) :
    lollipopClassEquiv hc (FrameClass.mk f) = MarkedFrameClass.mk (restrictFrame hc f) := rfl

/-- **The multiplicity is preserved**: `|Mult_H(φ)| = |Mult(ψ; marks)|`. -/
theorem markedAbsMult_lollipopClassEquiv (hc : IsMarkedCubic core mark)
    (x : FrameClass (attachLollipops core mark) degree) :
    (lollipopClassEquiv hc x).markedAbsMult = x.absMult :=
  Quotient.inductionOn x fun f ↦ markedAbsMult_restrictFrame hc f

/-- A lollipop frame is open at `(y, β, λ)`, `β, λ > 0`, iff its restriction is open at `y`
(the block structure of restriction: `z = (z', 2β, λ/2)`). -/
theorem openAt_restrictFrame_iff (hc : IsMarkedCubic core mark)
    (f : Frame (attachLollipops core mark) degree) {y : Fin p → ℚ} {bridge loop : Fin k → ℚ}
    (hb : ∀ j, 0 < bridge j) (hl : ∀ j, 0 < loop j) :
    (restrictFrame hc f).OpenAt y ↔ f.OpenAt (lollipopRequest y bridge loop) := by
  obtain ⟨col, bridgeCol, loopCol, hCover, hCoords⟩ := coordsAt_restrictFrame hc f
  obtain ⟨hCol, hBridge, hLoop⟩ := hCoords y bridge loop
  constructor
  · intro h c
    rcases hCover c with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hCol]
      exact h i
    · rw [hBridge]
      linarith [hb j]
    · rw [hLoop]
      linarith [hl j]
  · intro h i
    rw [← hCol]
    exact h _

/-- **Openness matches**, for every positive tails. -/
theorem openAt_lollipopClassEquiv_iff (hc : IsMarkedCubic core mark) {y : Fin p → ℚ}
    {bridge loop : Fin k → ℚ} (hb : ∀ j, 0 < bridge j) (hl : ∀ j, 0 < loop j)
    (x : FrameClass (attachLollipops core mark) degree) :
    (lollipopClassEquiv hc x).OpenAt y ↔ x.OpenAt (lollipopRequest y bridge loop) :=
  Quotient.inductionOn x fun f ↦ openAt_restrictFrame_iff hc f hb hl

/-- **The lollipop lemma, on fibres**: the open classes over the lollipop core at
`(y, β, λ)` are the marked fibre at `y`, for every positive `β, λ`. -/
noncomputable def lollipopFibreEquiv (hc : IsMarkedCubic core mark) {y : Fin p → ℚ}
    {bridge loop : Fin k → ℚ} (hb : ∀ j, 0 < bridge j) (hl : ∀ j, 0 < loop j) :
    {x : FrameClass (attachLollipops core mark) degree //
        x.OpenAt (lollipopRequest y bridge loop)} ≃ MarkedFibre core mark y degree :=
  (lollipopClassEquiv hc).subtypeEquiv fun x ↦ (openAt_lollipopClassEquiv_iff hc hb hl x).symm

/-! ## 3.  The count -/

/-- **The marked count is the weighted count on the lollipop core**, at any positive tails. -/
theorem markedCount_eq_openMultCount (hc : IsMarkedCubic core mark) {y : Fin p → ℚ}
    {bridge loop : Fin k → ℚ} (hb : ∀ j, 0 < bridge j) (hl : ∀ j, 0 < loop j) :
    markedCount core mark y degree =
      (IntegerCount.openMultCount (attachLollipops core mark) (lollipopRequest y bridge loop)
        degree : ℚ) := by
  rw [IntegerCount.openMultCount_cast_eq_frameSum, markedCount,
    ← finsum_comp_equiv (lollipopFibreEquiv hc hb hl)]
  exact finsum_congr fun x ↦ markedAbsMult_lollipopClassEquiv hc x.1

/-- **Tail independence** (no tail needs to be long): the weighted count on the lollipop core
is the same at all positive tails. -/
theorem openMultCount_lollipop_tails (hc : IsMarkedCubic core mark) (y : Fin p → ℚ)
    {bridge loop bridge' loop' : Fin k → ℚ} (hb : ∀ j, 0 < bridge j) (hl : ∀ j, 0 < loop j)
    (hb' : ∀ j, 0 < bridge' j) (hl' : ∀ j, 0 < loop' j) :
    IntegerCount.openMultCount (attachLollipops core mark) (lollipopRequest y bridge loop)
        degree =
      IntegerCount.openMultCount (attachLollipops core mark) (lollipopRequest y bridge' loop')
        degree := by
  have h := (markedCount_eq_openMultCount (degree := degree) (y := y) hc hb hl).symm.trans
    (markedCount_eq_openMultCount hc hb' hl')
  exact_mod_cast h

/-- The marked fibre is finite (so `markedCount` is an honest finite sum): it is a set of open
classes of the lollipop core. -/
theorem finite_markedFibre (hc : IsMarkedCubic core mark) (y : Fin p → ℚ) :
    Finite (MarkedFibre core mark y degree) := by
  have hb : ∀ j : Fin k, (0 : ℚ) < 1 := fun _ ↦ one_pos
  have : Finite (FrameClass (attachLollipops core mark) degree) :=
    Finite.of_equiv _ (CrossCoreTransport.fibreEquiv (attachLollipops core mark) degree
      (lollipopRequest y (fun _ ↦ 1) fun _ ↦ 1)).symm
  exact Finite.of_equiv _ (lollipopFibreEquiv (y := y) hc hb hb)

/-! ## 4.  Genericity -/

/-- **Genericity passes to the lollipop core**: if no marked frame has a zero coordinate at `y`,
then no frame of the lollipop core has a zero coordinate at `(y, β, λ)`, for any nonzero
tails. -/
theorem general_lollipop_of_general (hc : IsMarkedCubic core mark) {y : Fin p → ℚ}
    (hGeneral : ∀ (κ : MarkedFrame core mark degree) (col : Fin p), κ.coordsAt y col ≠ 0)
    {bridge loop : Fin k → ℚ} (hb : ∀ j, bridge j ≠ 0) (hl : ∀ j, loop j ≠ 0) :
    ∀ (f : Frame (attachLollipops core mark) degree) (col : Fin (p + (k + k))),
      f.coordsAt (lollipopRequest y bridge loop) col ≠ 0 := by
  intro f c
  obtain ⟨col, bridgeCol, loopCol, hCover, hCoords⟩ := coordsAt_restrictFrame hc f
  obtain ⟨hCol, hBridge, hLoop⟩ := hCoords y bridge loop
  rcases hCover c with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [hCol]
    exact hGeneral _ i
  · rw [hBridge]
    exact mul_ne_zero two_ne_zero (hb j)
  · rw [hLoop]
    exact div_ne_zero (hl j) two_ne_zero

/-- **Genericity passes back from the lollipop core** (every mark in the core ramified): if no frame
of the lollipop core has a zero coordinate at `(y, β, λ)` for some tails, then no marked frame has a
zero coordinate at `y`. -/
theorem general_of_general_lollipop (hc : IsMarkedCubic core mark) {y : Fin p → ℚ}
    {bridge loop : Fin k → ℚ}
    (hH : ∀ (f : Frame (attachLollipops core mark) degree) (col : Fin (p + (k + k))),
      f.coordsAt (lollipopRequest y bridge loop) col ≠ 0) :
    ∀ (κ : MarkedFrame core mark degree) (col : Fin p), κ.coordsAt y col ≠ 0 := by
  intro κ c
  obtain ⟨iso⟩ := restrictFrame_regrowFrame hc κ
  obtain ⟨σ, hσ⟩ := iso.exists_column
  obtain ⟨col, _, _, _, hCoords⟩ := coordsAt_restrictFrame hc (regrowFrame hc κ)
  obtain ⟨hCol, _, _⟩ := hCoords y bridge loop
  rw [← σ.apply_symm_apply c, hσ, ← hCol]
  exact hH _ _

end DraismaVargas.Count.MarkedCount
