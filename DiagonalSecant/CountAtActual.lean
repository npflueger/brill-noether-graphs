module

public import DiagonalSecant.Defs

@[expose] public section

/-!
# The count near the actual request: genericity along the chain, and the full-type slice

`typedCount_onceMarked` (`DraismaVargasMarkedCount/MarkedCountGeneral/MarkedCount.lean`) is
stated under `OnceGeneral core s a y`, which asks that **every** typed frame of **every** type
`≤ a` in **every** degree has nonzero coordinates at `y`, and the same for every unmarked frame of
`Γ` at the merged request in every degree. The closure can only supply genericity for the frames
it can see through the tailed core `H`: the typed frames of the types `a − 2m` in the degrees
`d − m` (which regrow to frames of `H`, `Regrowth.regrowTailed`), and the unmarked frames of `Γ`
in the one degree `d − a/2` at which the drop of a type-`0` mark is used. (Typed frames of other
parities and degrees do not exist, but no Lean lemma says so: the source genus of a typed frame
is not related to the core's genus anywhere, so the vacuity is not available.) The count holds
under exactly that genericity (`typedCount_onceMarked_chain`, with `OnceChainGeneral` and
`OnceDropGeneral`), and the first half of this module derives `OnceChainGeneral` from the
generality of `H` by regrowth.

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

/-! ## 1.  Genericity of `H` gives genericity along the chain -/

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
    OnceChainGeneral core s a d y := by
  -- The tails play no role: only the core columns of the regrown frame are read.
  have _hTail := hTail
  intro m d' hm hd' types ht κ col hzero
  have hc := tailed_markedCubic hCubic s
  have hm' : m < (tailType a 0 + 1) / 2 + 1 := by simp only [tailType]; omega
  let J : LowerIndex (tailType a) := fun _ ↦ ⟨m, hm'⟩
  have hType : types = lowerType (tailType a) J := by
    funext j
    fin_cases j
    simp only [lowerType, tailType, J]
    simp only [Fin.zero_eta, Fin.isValue] at ht ⊢
    omega
  have hDeg : d' = d - shed J := by simp [shed, J, hd']
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
    (lowerType_tailType_zero ha) (show d - shed J0 = d by rw [hShed0, Nat.sub_zero])

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
    (hDrop : OnceDropGeneral core s (d - a / 2) y) :
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
