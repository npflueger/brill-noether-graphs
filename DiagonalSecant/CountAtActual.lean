module

public import DiagonalSecant.Defs

@[expose] public section

/-!
# The count near the actual request: genericity along the chain, and the full-type slice

`typedCount_onceMarked` (`DraismaVargasMarkedCount/MarkedCountGeneral/MarkedCount.lean`) is
stated under `OnceGeneral core s a y`, which asks that **every** typed frame of **every** type `≤ a` in
**every** degree has nonzero coordinates at `y`, and the same for every unmarked frame of `Γ` at
the merged request in every degree. The closure can only supply genericity for the frames it can
see through the tailed core `H`: the typed frames of the types `a − 2m` in the degrees `d − m`
(which regrow to frames of `H`, `Regrowth.regrowTailed`), and the unmarked frames of `Γ` in the one
degree `d − a/2` at which the drop of a type-`0` mark is used. (Typed frames of other parities
and degrees do not exist, but no Lean lemma says so: the source genus of a typed frame is not
related to the core's genus anywhere, so the vacuity is not available.) This module restates the
count under exactly that genericity (`ChainGeneral`), re-running the proof of
`typedCount_onceMarked`, and derives it from the generality of `H` by regrowth.

The second half is the **full-type slice** of the tail count of the two-point ramified count: at
a positive request on `H` general for `H`, the frames of `H` of full type (`IsFullType`) have
`Σ |Mult| = N(g; a, 0)`, because `tailedClassEquiv` restricted to `J = 0` is a bijection onto the
typed fibre of type `a` with `#SlopeData (tailType a) 0 = ballot a 0 = 1`, and `|Mult|` is an
integer, so an odd value gives a full-type open member of odd multiplicity.
-/

namespace DiagonalSecant

open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.SegmentWalls (Frame)
open Utilities.Certificate.ExplicitPotential (Core)
open GenusSixExistence.Tripod.Gadget (subdivide)

variable {n p : ℕ}

/-! ## 1.  Genericity along the chain -/

/-- **Genericity along the chain**: no typed frame of type `a − 2m` in degree `d − m`,
`2m ≤ a`, has a zero coordinate at `y`. These are exactly the typed frames the proof of
`typedCount_onceMarked` looks at (`catalan_eq_once` at every level of the induction), and
exactly the lower types that regrow into `H` (`Regrowth.regrowTailed`). -/
def ChainGeneral (core : Core n p) (s : Fin p) (a d : ℕ) (y : Fin (p + 1) → ℚ) : Prop :=
  ∀ m, 2 * m ≤ a →
    ∀ (κ : TypedFrame (subdivide core s) (onceMark n) ![a - 2 * m] (d - m)) (col : Fin (p + 1)),
      κ.coordsAt y col ≠ 0

/-- Chain genericity passes to a lower level of the induction. -/
theorem ChainGeneral.lower {core : Core n p} {s : Fin p} {a d : ℕ} {y : Fin (p + 1) → ℚ}
    (h : ChainGeneral core s a d y) {j : ℕ} (hj : 2 * j ≤ a) :
    ChainGeneral core s (a - 2 * j) (d - j) y := by
  intro m hm κ col
  have h1 : a - 2 * j - 2 * m = a - 2 * (j + m) := by omega
  have h2 : d - j - m = d - (j + m) := by omega
  have ht : (![a - 2 * j - 2 * m] : Fin 1 → ℕ) = ![a - 2 * (j + m)] := by rw [h1]
  have := h (j + m) (by omega) (TypedFrame.cast ht h2 κ) col
  rwa [TypedFrame.coordsAt_cast] at this

/-- **The drop clause at one degree**: no unmarked frame of `Γ` in degree `d₀` has a zero
coordinate at the merged request. `typedCount_onceMarked` uses it only at `d₀ = d − a/2`, the
degree of the type-`0` level. -/
def DropGeneral (core : Core n p) (s : Fin p) (d₀ : ℕ) (y : Fin (p + 1) → ℚ) : Prop :=
  ∀ (f : Frame core d₀) (col : Fin p), f.coordsAt (mergeRequest s y) col ≠ 0

/-- `catalan_eq_once` (`MarkedCount.lean`) under chain genericity: its one use of
`OnceTypedGeneral`, at the lower types `lowerType cc J = ![a − 2 J 0]` in degrees
`d − shed J = d − J 0`, is a clause of `ChainGeneral` (`m := J 0`), after a cast. -/
theorem catalan_eq_once_chain {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg4 : 4 ≤ g) (s : Fin p)
    {a d : ℕ} (ha : 1 ≤ a) (hd : g + a + 2 = 2 * d) (h6 : 6 ≤ g + a) {y : Fin (p + 1) → ℚ}
    (hy : ∀ i, 0 < y i) (hGen : ChainGeneral core s a d y) :
    (catalan (d - 1) : ℚ) = ∑ j ∈ Finset.range (a / 2 + 1), (ballot a j : ℚ) *
      typedCount (subdivide core s) (onceMark n) ![a - 2 * j] y (d - j) := by
  set c₀ := a - 1 with hc₀
  set cc : Fin 1 → ℕ := fun _ ↦ c₀ with hcc
  set T := Tailed.canonical (subdivide core s) (onceMark n) cc
  have hc := isMarkedCubic_onceMarked hCubic s
  have hd' : IsTailDegree (n + 1) (p + 1) cc d := by
    unfold IsTailDegree
    simp only [hcc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, one_mul]
    omega
  have hEng := openMultCount_tailed T hc hd' (y := y) (yH := T.request y)
    (fun i ↦ T.request_coreSlot y i) (fun j s ↦ by rw [T.request_tailSlot]; exact one_pos)
  have hGenJ : ∀ (J : LowerIndex cc)
      (κ : TypedFrame (subdivide core s) (onceMark n) (lowerType cc J) (d - shed J))
      (col : Fin (p + 1)), κ.coordsAt y col ≠ 0 := by
    intro J κ col
    have hJ : 2 * (J 0 : ℕ) ≤ a := by
      have : (J 0 : ℕ) < (a - 1 + 1) / 2 + 1 := (J 0).isLt
      omega
    have hType : lowerType cc J = ![a - 2 * (J 0 : ℕ)] := by
      funext i
      fin_cases i
      simp only [lowerType, hcc]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
      omega
    have hShed : d - shed J = d - (J 0 : ℕ) := by simp [shed]
    have h := hGen (J 0) hJ (TypedFrame.cast hType hShed κ) col
    rwa [TypedFrame.coordsAt_cast] at h
  obtain ⟨K, rfl⟩ : ∃ K, d = K + 2 := ⟨d - 2, by omega⟩
  have hGenus : T.P + 1 - T.N = 2 * K + 2 := by
    rw [T.genus_eq (by omega)]
    simp only [hcc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, one_mul]
    omega
  have hG1 := IntegerCount.openMultCount_eq_catalan (k := K) (by omega) T.H (T.cubic hc)
    (T.connected (GenusSixExistence.Tripod.Gadget.subdivide_connected _ _ hConnected)) hGenus
    (T.request y) (T.request_pos hy)
    (general_tailed_of_general T hc (fun i ↦ T.request_coreSlot y i)
      (fun j s ↦ by rw [T.request_tailSlot]; exact one_ne_zero) hGenJ)
  rw [hG1] at hEng
  rw [show K + 2 - 1 = K + 1 by omega, hEng]
  rw [Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin ((c₀ + 1) / 2 + 1)) : LowerIndex cc ≃ _) _
    (fun j : Fin ((c₀ + 1) / 2 + 1) ↦ (ballot a j : ℚ) *
      typedCount (subdivide core s) (onceMark n) ![a - 2 * (j : ℕ)] y (K + 2 - j))]
  · rw [Fin.sum_univ_eq_sum_range (fun j ↦ (ballot a j : ℚ) *
      typedCount (subdivide core s) (onceMark n) ![a - 2 * j] y (K + 2 - j)),
      show (c₀ + 1) / 2 + 1 = a / 2 + 1 by omega]
  · intro J
    have hCard : (Fintype.card (SlopeData cc J) : ℚ) = (ballot a (J 0) : ℚ) := by
      have h := card_slopeData J
      rw [Fin.prod_univ_one] at h
      rw [show a = c₀ + 1 by omega]
      exact_mod_cast h
    have hType : lowerType cc J = ![a - 2 * (J 0 : ℕ)] := by
      funext i
      fin_cases i
      simp only [lowerType, hcc]
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
      omega
    have hShed : shed J = J 0 := by simp [shed]
    rw [hCard, hType, hShed]
    rfl

/-- `onceMarked_step` (`MarkedCount.lean`) under chain genericity. -/
theorem onceMarked_step_chain {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg4 : 4 ≤ g) (s : Fin p)
    {a d : ℕ} (ha : 1 ≤ a) (hd : g + a + 2 = 2 * d) (hL : d ≤ g) (h6 : 6 ≤ g + a)
    {y : Fin (p + 1) → ℚ} (hy : ∀ i, 0 < y i) (hGen : ChainGeneral core s a d y)
    (hIH : ∀ j ∈ Finset.range (a / 2 + 1), j ≠ 0 →
      typedCount (subdivide core s) (onceMark n) ![a - 2 * j] y (d - j) =
        (markedFormula g (d - j) (a - 2 * j) : ℚ)) :
    typedCount (subdivide core s) (onceMark n) ![a] y d = (markedFormula g d a : ℚ) := by
  have hEng := catalan_eq_once_chain hCubic hConnected hg hg4 s ha hd h6 hy hGen
  have hId := chainTail_identity_once (g := g) (a := a) (L := g + 1 - d) (by omega) (by omega)
  rw [show catalan (g + 1 - d + a) = catalan (d - 1) by congr 1; omega] at hId
  set X : ℕ → ℚ := fun j ↦
    typedCount (subdivide core s) (onceMark n) ![a - 2 * j] y (d - j) with hX
  set B : ℕ → ℚ := fun j ↦
    (((g.choose (g + 1 - d + a - j) : ℤ) - (g.choose (g + 1 - d + j - 1) : ℤ) : ℤ) : ℚ) with hB
  have hLow : ∀ j ∈ Finset.range (a / 2 + 1), j ≠ 0 → X j = B j := by
    intro j hj hj0
    have hj' := Finset.mem_range.mp hj
    simp only [hX, hB]
    rw [hIH j hj hj0]
    have h := markedFormula_lower (g := g) (d := d) (a := a) (j := j) (k := 0)
      (by omega) (by omega) hL
    simp only [Nat.sub_zero, add_zero] at h
    rw [h]
  have hSum : ∑ j ∈ Finset.range (a / 2 + 1), (ballot a j : ℚ) * (X j - B j) = 0 := by
    have hId' := congrArg (fun z : ℤ ↦ (z : ℚ)) hId
    push_cast at hId'
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hEng]
    simp only [hB]
    push_cast
    linarith
  have hSingle : ∑ j ∈ Finset.range (a / 2 + 1), (ballot a j : ℚ) * (X j - B j) = X 0 - B 0 := by
    rw [Finset.sum_eq_single_of_mem 0 (by simp) fun j hj hj0 ↦ by
      rw [hLow j hj hj0, sub_self, mul_zero]]
    simp
  have h00 : X 0 = B 0 := by linarith
  simp only [hX, hB, Nat.mul_zero, Nat.sub_zero, add_zero] at h00
  rw [h00]
  unfold markedFormula
  push_cast
  congr 3
  omega

/-- **The once-marked count under chain genericity** (`typedCount_onceMarked` with its
genericity hypothesis replaced by `ChainGeneral` and the one-degree drop clause). -/
theorem typedCount_onceMarked_chain {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg5 : 5 ≤ g) (s : Fin p)
    (a d : ℕ) (hd : g + a + 2 = 2 * d) (hL : d ≤ g) (y : Fin (p + 1) → ℚ) (hy : ∀ i, 0 < y i)
    (hGen : ChainGeneral core s a d y) (hDrop : DropGeneral core s (d - a / 2) y) :
    typedCount (subdivide core s) (onceMark n) ![a] y d = (markedFormula g d a : ℚ) := by
  induction a using Nat.strong_induction_on generalizing d with
  | _ a ih =>
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- type 0: drop `u`, then the integer count on `Γ`
    obtain ⟨K, rfl⟩ : ∃ K, d = K + 2 := ⟨d - 2, by omega⟩
    have hGen0 : ∀ (κ : TypedFrame (subdivide core s) (onceMark n) ![0] (K + 2))
        (col : Fin (p + 1)), κ.coordsAt y col ≠ 0 := by
      intro κ col
      have h := hGen 0 (by omega) (TypedFrame.cast (by simp) (by simp) κ) col
      rwa [TypedFrame.coordsAt_cast] at h
    rw [typedCount_dropOnce hCubic s hy hGen0,
      IntegerCount.openMultCount_eq_catalan (k := K) (by omega) core hCubic hConnected
        (by omega) _ (mergeRequest_pos hy) (by simpa [DropGeneral] using hDrop)]
    have hC := catalan_eq_choose_sub (m := K + 1) (by omega)
    unfold markedFormula
    rw [show g + 1 - (K + 2) + 0 = K + 1 by omega, show g - (K + 2) = K + 1 - 1 by omega,
      show g = 2 * (K + 1) by omega]
    exact_mod_cast hC
  · refine onceMarked_step_chain hCubic hConnected hg (by omega) s ha hd hL (by omega) hy hGen
      fun j hj hj0 ↦ ?_
    have hj' := Finset.mem_range.mp hj
    have hj2 : 2 * j ≤ a := by omega
    refine ih (a - 2 * j) (by omega) (d - j) (by omega) (by omega) (hGen.lower hj2) ?_
    rwa [show d - j - (a - 2 * j) / 2 = d - a / 2 by omega]

/-- **An explicit slope sequence** of genus `a` with `m` ascents: start at `a + 1 − 2m`,
ascend `m` times to `a + 1 − m`, then descend to `2`. -/
def chainSlope (a m : ℕ) : Fin a → ℕ :=
  fun i ↦ if (i : ℕ) ≤ m then a + 1 - 2 * m + i else a + 1 - i

theorem isSlopeSeq_chainSlope {a m : ℕ} (ha : 1 ≤ a) (hm : 2 * m ≤ a) :
    IsSlopeSeq a m (chainSlope a m) := by
  refine ⟨fun i ↦ ?_, fun i hi ↦ ?_, fun i i' hi ↦ ?_, fun i hi ↦ ?_⟩
  · have := i.isLt
    simp only [chainSlope]
    split_ifs <;> omega
  · have := i.isLt
    simp only [chainSlope]
    split_ifs <;> omega
  · have := i'.isLt
    simp only [chainSlope]
    split_ifs <;> omega
  · simp only [chainSlope]
    split_ifs <;> omega

/-- A typed class **has a zero coordinate at `y`**: a class invariant, since an isomorphism
permutes the coordinates (`TypedFrameIso.exists_column`). -/
def TypedFrameClass.HasZeroAt {k : ℕ} {core : Core n p} {mark : Fin k → Fin n}
    {types : Fin k → ℕ} {d : ℕ} (x : TypedFrameClass core mark types d) (y : Fin p → ℚ) :
    Prop :=
  Quot.lift (fun κ : TypedFrame core mark types d ↦ ∃ col, κ.coordsAt y col = 0)
    (fun _ _ h ↦ h.elim fun iso ↦ propext (by
      obtain ⟨σ, hσ⟩ := iso.exists_column
      exact ⟨fun ⟨c, hc⟩ ↦ ⟨σ c, by rw [hσ]; exact hc⟩,
        fun ⟨c, hc⟩ ↦ ⟨σ.symm c, by rw [← hσ, σ.apply_symm_apply]; exact hc⟩⟩)) x

/-! ## 2.  Genericity of `H` gives genericity along the chain -/

/-- **Genericity of `H` gives genericity along the chain** (for `a ≥ 1`, because every
lower-type frame regrows): if no frame of `H` has a zero coordinate at a request
with core part `y` and nonzero tails, then no typed frame along the chain has one at `y`. -/
theorem chainGeneral_of_tailed_general {core : Core n p} (hCubic : core.Cubic) (s : Fin p)
    {a d : ℕ} (ha : 1 ≤ a) (hd : IsTailDegree (n + 1) (p + 1) (tailType a) d)
    {y : Fin (p + 1) → ℚ} {yH : Fin (tailed core s a).P → ℚ}
    (hCore : ∀ i, yH ((tailed core s a).coreSlot i) = y i)
    (hTail : ∀ j t, yH ((tailed core s a).tailSlot j t) ≠ 0)
    (hH : ∀ (f : Frame (tailed core s a).H d) (col : Fin (tailed core s a).P),
      f.coordsAt yH col ≠ 0) :
    ChainGeneral core s a d y := by
  -- The tails play no role: only the core columns of the regrown frame are read.
  have _hTail := hTail
  intro m hm κ col hzero
  have hc := tailed_markedCubic hCubic s
  have hm' : m < (tailType a 0 + 1) / 2 + 1 := by simp only [tailType]; omega
  let J : LowerIndex (tailType a) := fun _ ↦ ⟨m, hm'⟩
  have hType : (![a - 2 * m] : Fin 1 → ℕ) = lowerType (tailType a) J := by
    funext j
    fin_cases j
    simp only [lowerType, tailType, J]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one]
    omega
  have hDeg : d - m = d - shed J := by simp [shed, J]
  let sl : SlopeData (tailType a) J := fun _ ↦
    ⟨chainSlope (a - 1 + 1) m, isSlopeSeq_chainSlope (by omega) (by omega)⟩
  have hR := restrictTailed_regrowTailed (tailed core s a) hc hd J
    (TypedFrame.cast hType hDeg κ) sl
  have hZ := congrArg (fun z : LowerClass (subdivide core s) (onceMark n) (tailType a) d ↦
    TypedFrameClass.HasZeroAt z.2.1 y) hR
  have hZ' : TypedFrameClass.HasZeroAt (restrictTailed (tailed core s a) hc
      (regrowTailed (tailed core s a) hc hd J (TypedFrame.cast hType hDeg κ) sl)).toClass.2.1 y := by
    simp only at hZ
    rw [hZ]
    exact ⟨col, by rw [TypedFrame.coordsAt_cast]; exact hzero⟩
  obtain ⟨col', hcol'⟩ := hZ'
  obtain ⟨cols, slotOf, weight, -, hCoords⟩ := coordsAt_restrictTailed (tailed core s a) hc
    (regrowTailed (tailed core s a) hc hd J (TypedFrame.cast hType hDeg κ) sl)
  have h := (hCoords y yH hCore).1 col'
  exact hH _ (cols col') (h.trans hcol')

/-! ## 3.  The full-type slice of the tail count -/

/-- The lower type of the zero index is the full type `a` (for `a ≥ 1`). -/
theorem lowerType_tailType_zero' {a : ℕ} (ha : 1 ≤ a) :
    lowerType (tailType a) (fun _ ↦ 0) = ![a] := by
  funext j
  fin_cases j
  show a - 1 + 1 - 2 * ((0 : Fin ((a - 1 + 1) / 2 + 1)) : ℕ) = a
  rw [Fin.val_zero]
  omega

/-- The typed count is invariant under equalities of the type vector and the degree. -/
theorem typedCount_congr {k : ℕ} {core : Core n p} {mark : Fin k → Fin n}
    {types types' : Fin k → ℕ} {y : Fin p → ℚ} {d d' : ℕ} (ht : types = types') (hd : d = d') :
    typedCount core mark types y d = typedCount core mark types' y d' := by
  subst ht hd
  rfl

/-- **The full-type slice of the tail count.** At a request on `H` with core part `y` and
positive tails, the open classes of `H` of full type have `Σ |Mult| = typedCount … ![a] y d`:
`tailedClassEquiv` restricted to `J = 0` (`IsFullType`), with `mult_tailedClassEquiv` (tail
factor `1`), `openAt_tailedClassEquiv_iff` and `#SlopeData (tailType a) 0 = ballot a 0 = 1`
(`card_slopeData`, `ballot_zero`). -/
theorem fullType_sum_eq_typedCount {core : Core n p} (hCubic : core.Cubic) (s : Fin p)
    {a d : ℕ} (ha : 1 ≤ a) (hd : IsTailDegree (n + 1) (p + 1) (tailType a) d)
    {y : Fin (p + 1) → ℚ} {yH : Fin (tailed core s a).P → ℚ}
    (hCore : ∀ i, yH ((tailed core s a).coreSlot i) = y i)
    (hTail : ∀ j t, 0 < yH ((tailed core s a).tailSlot j t)) :
    ∑ᶠ x : {x : CrossCoreTransport.FrameClass (tailed core s a).H d //
        x.OpenAt yH ∧ ∃ f, CrossCoreTransport.FrameClass.mk f = x ∧
          IsFullType (tailed core s a) (tailed_markedCubic hCubic s) f},
      x.1.absMult = typedCount (subdivide core s) (onceMark n) ![a] y d := by
  classical
  have hc := tailed_markedCubic hCubic s
  let J0 : LowerIndex (tailType a) := fun _ ↦ 0
  have hCard : Fintype.card (SlopeData (tailType a) J0) = 1 := by
    have h := card_slopeData J0
    rw [Fin.prod_univ_one] at h
    simp only [J0, Fin.val_zero, ballot_zero] at h
    exact_mod_cast h
  obtain ⟨s₀⟩ : Nonempty (SlopeData (tailType a) J0) := Fintype.card_pos_iff.mp (by omega)
  have hsub : Subsingleton (SlopeData (tailType a) J0) :=
    Fintype.card_le_one_iff_subsingleton.mp hCard.le
  set E := tailedClassEquiv (tailed core s a) hc hd with hE
  let z₀ : TypedFrameClass (subdivide core s) (onceMark n) (lowerType (tailType a) J0)
      (d - shed J0) → LowerClass (subdivide core s) (onceMark n) (tailType a) d :=
    fun w' ↦ ⟨J0, w', s₀⟩
  -- The full-type open classes are the regrowths of the open typed classes of index `0`.
  let φ : {x : TypedFrameClass (subdivide core s) (onceMark n) (lowerType (tailType a) J0)
      (d - shed J0) // x.OpenAt y} →
      {x : CrossCoreTransport.FrameClass (tailed core s a).H d //
        x.OpenAt yH ∧ ∃ f, CrossCoreTransport.FrameClass.mk f = x ∧
          IsFullType (tailed core s a) (tailed_markedCubic hCubic s) f} := fun w ↦
    ⟨E.symm (z₀ w.1), by
      refine ⟨(openAt_tailedClassEquiv_iff (tailed core s a) hc hd hCore hTail _).mp ?_, ?_⟩
      · show LowerClass.OpenAt (E (E.symm (z₀ w.1))) y
        rw [E.apply_symm_apply]
        exact w.2
      · obtain ⟨κ, hκ⟩ := TypedFrameClass.mk_surjective w.1
        refine ⟨regrowTailed (tailed core s a) hc hd J0 κ s₀, ?_, ?_⟩
        · rw [← hκ]
          rfl
        · have hR := congrArg Sigma.fst
            (restrictTailed_regrowTailed (tailed core s a) hc hd J0 κ s₀)
          intro j
          change (((restrictTailed (tailed core s a) hc
            (regrowTailed (tailed core s a) hc hd J0 κ s₀)).toClass.1 j : ℕ)) = 0
          rw [hR]
          rfl⟩
  have hφE : ∀ w, E (φ w).1 = z₀ w.1 := fun w ↦ Equiv.apply_symm_apply _ _
  have hInj : Function.Injective φ := by
    intro w w' h
    have h' := congrArg (fun x ↦ E x.1) h
    simp only [hφE] at h'
    have h'' := (Prod.mk.inj (eq_of_heq (Sigma.mk.inj_iff.mp h').2)).1
    exact Subtype.ext h''
  have key : ∀ z : LowerClass (subdivide core s) (onceMark n) (tailType a) d, z.1 = J0 →
      ∃ w' : TypedFrameClass (subdivide core s) (onceMark n) (lowerType (tailType a) J0)
        (d - shed J0), z = z₀ w' := by
    rintro ⟨J, w', sl⟩ hJ
    dsimp only at hJ
    subst hJ
    exact ⟨w', by rw [Subsingleton.elim sl s₀]⟩
  have hSurj : Function.Surjective φ := by
    rintro ⟨x, hxOpen, f, rfl, hf⟩
    have hJ : (E (CrossCoreTransport.FrameClass.mk f)).1 = J0 := hf.lowerIndex_eq
    obtain ⟨w', hw'⟩ := key _ hJ
    have hOpen : w'.OpenAt y := by
      have h := (openAt_tailedClassEquiv_iff (tailed core s a) hc hd hCore hTail _).mpr hxOpen
      rw [← hE, hw'] at h
      exact h
    refine ⟨⟨w', hOpen⟩, Subtype.ext ?_⟩
    change E.symm (z₀ w') = _
    rw [← hw', Equiv.symm_apply_apply]
  rw [← finsum_comp_equiv (Equiv.ofBijective φ ⟨hInj, hSurj⟩)]
  have hTerm : ∀ w, ((Equiv.ofBijective φ ⟨hInj, hSurj⟩) w).1.absMult = w.1.typedAbsMult := by
    intro w
    change (φ w).1.absMult = _
    rw [← mult_tailedClassEquiv (tailed core s a) hc hd, ← hE, hφE]
    rfl
  rw [finsum_congr hTerm]
  have hShed0 : shed J0 = 0 := Finset.sum_eq_zero fun _ _ ↦ rfl
  exact typedCount_congr (core := subdivide core s) (mark := onceMark n) (y := y)
    (lowerType_tailType_zero' ha) (show d - shed J0 = d by rw [hShed0, Nat.sub_zero])

/-- **An open full-type member of odd multiplicity at a general positive request**, from an odd
value of the count: the summands of `fullType_sum_eq_typedCount` are positive integers
(`FibreMember.absMult_eq_oddMult`, through `Frame.absMult`), and a finite sum of integers that is
odd has an odd term. -/
theorem exists_open_oddFullType {core : Core n p} (hCubic : core.Cubic)
    (hConnected : core.Connected) {g : ℕ} (hg : p + 1 - n = g) (hg5 : 5 ≤ g) (s : Fin p)
    {a d : ℕ} (ha : 1 ≤ a) (hd : g + a + 2 = 2 * d) (hL : d ≤ g)
    (hOdd : Odd (markedFormula g d a))
    {y : Fin (p + 1) → ℚ} (hy : ∀ i, 0 < y i) {yH : Fin (tailed core s a).P → ℚ}
    (hCore : ∀ i, yH ((tailed core s a).coreSlot i) = y i)
    (hTail : ∀ j t, 0 < yH ((tailed core s a).tailSlot j t))
    (hH : ∀ (f : Frame (tailed core s a).H d) (col : Fin (tailed core s a).P),
      f.coordsAt yH col ≠ 0)
    (hDrop : DropGeneral core s (d - a / 2) y) :
    ∃ mem : FibreMember (tailed core s a).H yH d,
      mem.Open ∧ mem.HasOddMult ∧
        IsFullType (tailed core s a) (tailed_markedCubic hCubic s) (Frame.of mem) := by
  classical
  have hdT := tailed_isTailDegree (n := n) (p := p) hg ha hd
  have hChain := chainGeneral_of_tailed_general hCubic s ha hdT hCore
    (fun j t ↦ (hTail j t).ne') hH
  have hCount := typedCount_onceMarked_chain hCubic hConnected hg hg5 s a d hd hL y hy hChain hDrop
  have hSum := fullType_sum_eq_typedCount hCubic s ha hdT hCore hTail
  rw [hCount] at hSum
  -- the open full-type classes
  set S := {x : CrossCoreTransport.FrameClass (tailed core s a).H d //
      x.OpenAt yH ∧ ∃ f, CrossCoreTransport.FrameClass.mk f = x ∧
        IsFullType (tailed core s a) (tailed_markedCubic hCubic s) f} with hS
  -- every multiplicity is a natural number
  have hNat : ∀ x : S, ∃ k : ℕ, x.1.absMult = k := by
    rintro ⟨x, -, f, rfl, -⟩
    exact ⟨fdAbsMultNat f.fullDim, fdAbsMult_eq_fdAbsMultNat f.fullDim⟩
  choose K hK using hNat
  -- some class has odd multiplicity
  obtain ⟨x, hxOdd⟩ : ∃ x : S, Odd (K x) := by
    by_contra hno
    push Not at hno
    have hEven : ∀ x : S, Even (K x) := fun x ↦ Nat.not_odd_iff_even.mp (hno x)
    have : Finite S := Subtype.finite
    let _ : Fintype S := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun x _ ↦ hK x] at hSum
    have hInt : ((∑ x : S, K x : ℕ) : ℤ) = markedFormula g d a := by
      exact_mod_cast hSum
    have hE : Even (∑ x : S, K x) := Finset.even_sum _ fun x _ ↦ hEven x
    rw [← hInt] at hOdd
    exact (Int.not_even_iff_odd.mpr hOdd) (by exact_mod_cast hE)
  have hKx := hK x
  obtain ⟨x, hxOpen, f, rfl, hf⟩ := x
  exact ⟨f.member yH, hxOpen, ⟨_, hxOdd, hKx⟩, hf⟩

end DiagonalSecant
