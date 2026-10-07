module

public import DraismaVargasCount.CountTransportLink
public import DraismaVargasCount.W4WallExhaustion
public import Mathlib.Algebra.BigOperators.Ring.Nat

@[expose] public section

/-!
# What evenness of `switchingCount` actually consumes

Step 2 of the genus-six count (`Assembly.trivalentWalls_genusSix`) shows that
crossing a trivalent wall preserves the parity of the open odd count.
`CountTransportLink` reduces a `CountLink` across an in-cone wall to
`Even (switchingCount core degree y y')`
(`CountTransportLink.countLink_iff_even_switchingCount`).  This file says what
*shape* of input produces that evenness.  (The walls and the count are those of
Vargas, Part II, arXiv:2609.09109, section *Invariance of the count via continuous
deformation*.)

## What is proved here

* `even_card_of_freeInvolution`, `exists_freeInvolution_of_even_card`,
  `even_card_iff_exists_freeInvolution` -- over any finite type, evenness of the
  cardinality is **equivalent** to the existence of a fixed-point-free
  involution.  Both directions.
* `even_switchingCount_iff_exists_freeInvolution` -- the same, transported to
  the switching classes.  **This is a restatement, not a reduction.**  Since
  the criterion is an equivalence, "exhibit an involution without fixed points
  on the switching set" is not a weaker obligation than the parity statement
  itself.  Only a *canonical* involution, built from the geometry, could be, and
  §6 records why the discrete four-valent walls do not supply one.
* `even_switchingCount_iff_even_sum` -- **the sharp form of what the wall step
  consumes**: over any `Finset` listing exactly the classes whose openness
  changes, the switching count is even **iff** the total `multNat` carried by
  that list is even.  So the real input is a *parity of a multiplicity sum over
  the changing classes*; in particular only the parity of `Σ Mult` is used, and
  the balancing identity `Σ Mult = 0` is strictly stronger than needed.
* `even_sum_of_oddFibres` -- **injectivity is consumed only modulo two.**  A
  candidate list whose fibre over each listed class has *odd* cardinality has
  the same sum parity as the list of classes itself.  Injectivity (all fibres
  singletons) is the special case.
* `even_sum_of_balanced`, `even_sum_natAbs_of_even_sum`,
  `even_sum_natAbs_of_sum_eq_zero` (§4b) -- two producers of the parity input: a
  balanced split, and a vanishing signed sum.
* `even_switchingCount_of_candidates` -- the three named inputs, assembled: a
  candidate family that (i) changes openness, (ii) covers every changing class
  (exhaustion), (iii) covers each one an odd number of times (only modulo two),
  and (iv) has even total multiplicity (the balancing identity, modulo two)
  forces `Even (switchingCount …)`.  Nothing else enters.
* `even_switchingCount_of_injective_candidates` -- the same with (iii)
  strengthened to `Function.Injective rep`.
* `no_freeInvolution_of_odd_card` and `W4.no_freeInvolution_star` -- **the
  involution route has no purchase on the star.**  At every discrete
  four-valent wall the labelled geometric star has *three* classes
  (`W4WallExhaustion.card_odd`), so it carries no fixed-point-free involution at
  all.  Any involution witnessing the parity must live on the *odd sub-part* of
  the star, which cannot be named before the multiplicities are known -- which is
  the multiplicity computation the involution would have to avoid.

## What is NOT proved here -- every hypothesis

* **No wall is crossed and no star is built.**  Every theorem below takes the
  candidate family, its exhaustiveness and its multiplicity balance as
  *hypotheses*.  Nothing here produces any of the three at an actual wall; the
  stars are enumerated and their multiplicities balanced wall type by wall type
  (for example `W4WallExhaustion`, `StarParityFromBalance`).
* **Nothing here identifies the changing classes with `GeometricStar.Star`.**
  `Changes` below is "openness differs between the two requests", a statement
  about a pair of requests; `GeometricStar.Star hy wall` is a set of classes at
  a *single* nondegenerate request specializing to one limit.  The bridge --
  that across an isolated wall the changing classes are exactly the classes
  whose frame is `Frame.DegenerateAt` the wall request, partitioned by their
  limits into stars -- is `WallSwitchingBridge`.
  `even_switchingCount_of_candidates` is therefore stated about a candidate
  family for the *changing* classes, not for a star.
* **`hbal` is an assumption about the candidate family, not about a star.**  If
  the family fails to be exhaustive, `hbal` says nothing about the switching
  count: all four hypotheses are needed together.
* **No claim that the hypotheses are satisfiable at any wall.**  Nothing here
  exhibits a single wall at which a candidate family with these four properties
  exists.
* `multNat` is `GeometricFibre.multNat`, the **unsigned** multiplicity
  (`FibreMember.oddMult`, i.e. `|Mult|` as a natural number), and `IsOdd` is
  `Odd multNat`.  No signed multiplicity is used, so the sign law of `ConeSide`
  is not consumed here -- it is what says *which side* a member switches on,
  which the parity step does not need.
* `W4.no_freeInvolution_star` carries exactly the hypotheses of the enumeration
  of the discrete four-valent walls (`hFour`, `hDiscrete`, the `FourStar`, the
  three candidates); it asserts nothing at a wall of any other type.
-/

namespace DraismaVargas.Count.SwitchingParity

open DraismaVargas.Infrastructure
open Utilities.Certificate.ExplicitPotential (Core)
open Finset

variable {n p : ℕ}

/-! ## 1.  Fixed-point-free involutions and even cardinality, over any finite type -/

/-- **A fixed-point-free involution forces an even cardinality.** -/
theorem even_card_of_freeInvolution {T : Type*} [Finite T] (g : T → T)
    (hinv : Function.Involutive g) (hfree : ∀ x, g x ≠ x) : Even (Nat.card T) := by
  classical
  have _ : Fintype T := Fintype.ofFinite T
  have hsum : ∑ _x : T, (1 : ZMod 2) = 0 :=
    Finset.sum_ninvolution g (fun _ ↦ by decide) (fun a _ ↦ hfree a)
      (fun a ↦ Finset.mem_univ (g a)) fun a ↦ hinv a
  have hcast : ((Nat.card T : ℕ) : ZMod 2) = 0 := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    simpa using hsum
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

/-- **Conversely, every finite type of even cardinality carries one.**  Pair the
elements off through any identification with `Fin k × Fin 2`. -/
theorem exists_freeInvolution_of_even_card {T : Type*} [Finite T] (h : Even (Nat.card T)) :
    ∃ g : T → T, Function.Involutive g ∧ ∀ x, g x ≠ x := by
  classical
  have _ : Fintype T := Fintype.ofFinite T
  obtain ⟨k, hk⟩ := h
  have hcard : Fintype.card T = k * 2 := by
    rw [← Nat.card_eq_fintype_card, hk]
    ring
  have hstep : ∀ b : Fin 2, b + 1 + 1 = b := by decide
  have hne : ∀ b : Fin 2, b + 1 ≠ b := by decide
  set e : T ≃ Fin k × Fin 2 :=
    (Fintype.equivFinOfCardEq hcard).trans finProdFinEquiv.symm with he
  refine ⟨fun x ↦ e.symm ((e x).1, (e x).2 + 1), ?_, ?_⟩
  · intro x
    simp only [Equiv.apply_symm_apply, hstep, Prod.mk.eta, Equiv.symm_apply_apply]
  · intro x hx
    refine hne (e x).2 ?_
    have hex := congrArg e hx
    rw [Equiv.apply_symm_apply] at hex
    exact congrArg Prod.snd hex

/-- **Evenness and fixed-point-free involutions are the same condition.**  This
is why the involution route is not a reduction: it is a restatement. -/
theorem even_card_iff_exists_freeInvolution {T : Type*} [Finite T] :
    Even (Nat.card T) ↔ ∃ g : T → T, Function.Involutive g ∧ ∀ x, g x ≠ x :=
  ⟨exists_freeInvolution_of_even_card,
    fun ⟨g, hinv, hfree⟩ ↦ even_card_of_freeInvolution g hinv hfree⟩

/-- **An odd finite type carries no fixed-point-free involution.** -/
theorem no_freeInvolution_of_odd_card {T : Type*} [Finite T] (h : Odd (Nat.card T)) :
    ¬ ∃ g : T → T, Function.Involutive g ∧ ∀ x, g x ≠ x := by
  rintro ⟨g, hinv, hfree⟩
  exact (Nat.not_even_iff_odd.mpr h) (even_card_of_freeInvolution g hinv hfree)

/-! ## 2.  The classes whose openness changes -/

/-- **The classes whose openness differs between the two requests.**  This is the
second conjunct of the subtype `CountTransportLink.switchingCount` counts, with
the multiplicity condition dropped. -/
def Changes (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (c : GeometricFibre core y degree) : Prop :=
  ¬ (c.Open ↔ (GeometricSegmentWalls.fibreEquiv core degree y y' c).Open)

theorem switchingCount_eq_card (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ) :
    CountTransportLink.switchingCount core degree y y' =
      Nat.card {c : GeometricFibre core y degree // c.IsOdd ∧ Changes core degree y y' c} :=
  rfl

/-- **The involution criterion for the switching count, as an equivalence.**  An
involution without fixed points on the switching classes is *exactly* the
evenness it was hoped to reduce, so on its own it is not a reduction. -/
theorem even_switchingCount_iff_exists_freeInvolution (core : Core n p) (degree : ℕ)
    (y y' : Fin p → ℚ) :
    Even (CountTransportLink.switchingCount core degree y y') ↔
      ∃ g : {c : GeometricFibre core y degree // c.IsOdd ∧ Changes core degree y y' c} →
            {c : GeometricFibre core y degree // c.IsOdd ∧ Changes core degree y y' c},
        Function.Involutive g ∧ ∀ c, g c ≠ c :=
  even_card_iff_exists_freeInvolution

/-! ## 3.  The sharp form: a parity of multiplicities over the changing classes -/

/-- **What evenness of the switching count actually consumes.**  Let `S` list
exactly the classes whose openness changes.  Then the switching count is even
**iff** the total unsigned multiplicity carried by `S` is even.  Only the parity
of that sum is used, so the balancing identity `Σ Mult = 0` is strictly stronger
than what the parity step needs. -/
theorem even_switchingCount_iff_even_sum (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (S : Finset (GeometricFibre core y degree))
    (hS : ∀ c, c ∈ S ↔ Changes core degree y y' c) :
    Even (CountTransportLink.switchingCount core degree y y') ↔
      Even (∑ c ∈ S, c.multNat) := by
  classical
  rw [Finset.even_sum_iff_even_card_odd]
  have hcount : CountTransportLink.switchingCount core degree y y' =
      #{c ∈ S | Odd (GeometricFibre.multNat c)} := by
    rw [switchingCount_eq_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ ⟨(hS c).mpr h.2, h.1⟩, fun h ↦ ⟨h.2, (hS c).mp h.1⟩⟩
  rw [hcount]

/-! ## 4.  Injectivity of a candidate list is consumed only modulo two -/

/-- **Odd fibres suffice.**  If every listed class is represented an *odd* number
of times by the candidate family, the family's total weight has the same parity
as the total weight of the classes it lists.  Injectivity is the case where
every fibre is a singleton. -/
theorem even_sum_of_oddFibres {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    (rep : ι → κ) (w : κ → ℕ)
    (hodd : ∀ c ∈ Finset.image rep Finset.univ, Odd #{i | rep i = c})
    (hsum : Even (∑ i, w (rep i))) :
    Even (∑ c ∈ Finset.image rep Finset.univ, w c) := by
  classical
  rw [Finset.sum_comp] at hsum
  simp only [smul_eq_mul] at hsum
  rw [Finset.even_sum_iff_even_card_odd] at hsum ⊢
  have hfilter :
      Finset.filter (fun c ↦ Odd (#{i | rep i = c} * w c)) (Finset.image rep Finset.univ) =
        Finset.filter (fun c ↦ Odd (w c)) (Finset.image rep Finset.univ) :=
    Finset.filter_congr fun c hc ↦ by
      simp only [Nat.odd_mul]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hodd c hc, h⟩⟩
  rwa [hfilter] at hsum

/-! ## 4b.  Two producers of the parity input, both strictly weaker obligations -/

/-- **A balanced split produces the parity input.**  If the two sides of the wall
carry equal total multiplicity -- `Σ_near |Mult| = Σ_far |Mult|` -- then the
total is even.
The converse fails, so the parity input is strictly weaker than the balance. -/
theorem even_sum_of_balanced {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → ℕ)
    (s : Finset ι) (h : ∑ i ∈ s, w i = ∑ i ∈ sᶜ, w i) : Even (∑ i, w i) := by
  refine ⟨∑ i ∈ s, w i, ?_⟩
  rw [← Finset.sum_add_sum_compl s w, ← h]

/-- **A vanishing signed sum produces the parity input.**  `|m| ≡ m (mod 2)`, so
`Even (Σ m_i)` -- in particular `Σ m_i = 0`, the balancing identity -- forces
`Σ |m_i|` to be even.  Again the converse fails: the parity of
the multiplicity sum is strictly weaker than the balancing identity. -/
theorem even_sum_natAbs_of_even_sum {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (h : Even (∑ i, f i)) : Even (∑ i, (f i).natAbs) := by
  classical
  have hterm : ∀ m : ℤ, Even (((m.natAbs : ℕ) : ℤ) - m) := by
    intro m
    rw [Int.natCast_natAbs]
    rcases le_total 0 m with hm | hm
    · rw [abs_of_nonneg hm, sub_self]
      exact ⟨0, by ring⟩
    · rw [abs_of_nonpos hm]
      exact ⟨-m, by ring⟩
  have hdiff : Even ((∑ i, ((f i).natAbs : ℤ)) - ∑ i, f i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.even_sum _ fun i _ ↦ hterm (f i)
  have htotal : Even (∑ i, ((f i).natAbs : ℤ)) := by
    have h2 := hdiff.add h
    simpa using h2
  exact_mod_cast htotal

/-- The form the balancing identity takes: a vanishing sum of signed
multiplicities over the listed members. -/
theorem even_sum_natAbs_of_sum_eq_zero {ι : Type*} [Fintype ι] (f : ι → ℤ)
    (h : ∑ i, f i = 0) : Even (∑ i, (f i).natAbs) :=
  even_sum_natAbs_of_even_sum f (by rw [h]; exact ⟨0, by ring⟩)

/-! ## 5.  The three named inputs, assembled -/

/-- **What the star enumeration and the balancing identity must supply at one
isolated wall.**  A candidate family that changes openness, covers every changing
class (exhaustion), covers each one an odd number of times (modulo two) and has
even total multiplicity (the balancing identity, modulo two) forces the switching
count to be even.  Nothing else
enters: no side law, no signed multiplicity, no classification of the members
beyond the three clauses named. -/
theorem even_switchingCount_of_candidates {ι : Type*} [Fintype ι]
    (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (rep : ι → GeometricFibre core y degree)
    (hmem : ∀ i, Changes core degree y y' (rep i))
    (hcov : ∀ c, Changes core degree y y' c → ∃ i, rep i = c)
    (hodd : ∀ i, Odd (Nat.card {j : ι // rep j = rep i}))
    (hbal : Even (∑ i, (rep i).multNat)) :
    Even (CountTransportLink.switchingCount core degree y y') := by
  classical
  have hS : ∀ c, c ∈ Finset.image rep Finset.univ ↔ Changes core degree y y' c := by
    intro c
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨fun ⟨i, hi⟩ ↦ hi ▸ hmem i, hcov c⟩
  rw [even_switchingCount_iff_even_sum core degree y y' _ hS]
  refine even_sum_of_oddFibres rep _ ?_ hbal
  intro c hc
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hc
  have h := hodd i
  rwa [Nat.card_eq_fintype_card, Fintype.card_subtype] at h

/-- **The same with injective candidates.**  An injective candidate family
is the special case in which every fibre is a singleton. -/
theorem even_switchingCount_of_injective_candidates {ι : Type*} [Fintype ι]
    (core : Core n p) (degree : ℕ) (y y' : Fin p → ℚ)
    (rep : ι → GeometricFibre core y degree)
    (hmem : ∀ i, Changes core degree y y' (rep i))
    (hcov : ∀ c, Changes core degree y y' c → ∃ i, rep i = c)
    (hinj : Function.Injective rep)
    (hbal : Even (∑ i, (rep i).multNat)) :
    Even (CountTransportLink.switchingCount core degree y y') := by
  classical
  refine even_switchingCount_of_candidates core degree y y' rep hmem hcov ?_ hbal
  intro i
  have hone : Nat.card {j : ι // rep j = rep i} = 1 :=
    Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b ↦ Subtype.ext (hinj (a.2.trans b.2.symm))⟩, ⟨⟨i, rfl⟩⟩⟩
  rw [hone]
  exact odd_one

/-! ## 6.  The discrete four-valent walls refuse the involution -/

namespace W4

open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4TargetPairings (FourStar)
open DraismaVargas.Count.WallStar (Regrowth Nondegenerate)
open DraismaVargas.Count.W4WallExhaustion (mergeVertex Candidate)

variable {degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {hy : Nondegenerate y} {wall : Regrowth core y degree}

/-- **No fixed-point-free involution exists on the star of a discrete four-valent
wall.**  `W4WallExhaustion.card_odd` gives three classes under exactly the
hypotheses of its enumeration, and three is odd.  So "pair the star up" is
unavailable there: any involution witnessing the parity must live on the *odd
sub-part* of the star, and naming that sub-part is the multiplicity computation
the involution was meant to replace. -/
theorem no_freeInvolution_star
    (hFour : (GluingDatum.incidentEdges (mergeVertex wall)).card = 4)
    (hDiscrete : wall.limit.vertexPartition (mergeVertex wall) = SheetPartition.discrete degree)
    (star : FourStar (wall.frame.limitTarget wall.column) (mergeVertex wall))
    (cand : ∀ q : Fin 3, Candidate hy wall hDiscrete star q) :
    ¬ ∃ g : GeometricStar.Star hy wall → GeometricStar.Star hy wall,
        Function.Involutive g ∧ ∀ x, g x ≠ x := by
  refine no_freeInvolution_of_odd_card ?_
  rw [Nat.card_eq_fintype_card]
  exact W4WallExhaustion.card_odd hFour hDiscrete star cand

end W4

end DraismaVargas.Count.SwitchingParity
