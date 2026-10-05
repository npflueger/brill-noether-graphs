module

public import Utilities.Subdivision.OneEdgeSplitRefinement
public import Utilities.Subdivision.SubdivisionChipDescent

@[expose] public section

/-!
# Lifting a Laplacian equivalence to every uniform refinement

A Laplacian equivalence between two subdivision presentations is a bijection of their vertices
that preserves edge multiplicities. **One** such equivalence `φ : s.graph ≃ t.graph` lifts, at
every scale `k`, to a Laplacian equivalence of the `k`-fold refinements that commutes with
`fineOf` (`exists_scaledEquiv`), and hence carries embedded divisors to embedded divisors
(`mapDiv_embed`). This is useful when a reduction supplies equivalences at every scale only
inside `Nonempty`, so that where a given vertex goes is not recorded: one equivalence at scale
one, with its named vertices, then determines compatible equivalences at all scales.

## The construction

* `pv s e a` is the vertex at path position `a` of slot `e`, clamped to the slot, so that path
  positions are plain naturals and rewriting along a slot needs no transported proofs.
* A `StepMatch s t` is a vertex equivalence together with an equivalence of unit steps that
  preserves the endpoints of every step, possibly reversing it (`flip`). Every
  `LaplacianEquiv` has one (`exists_stepMatch`): the unit steps over an unordered pair of
  vertices are as many on both sides, because both counts are `num_edges`.
* A step match refines: the fine vertex at position `k * i + r` of the coarse step `(e, i)`
  goes to position `k * i' + r` (or `k * i' + (k - r)`, if the step is flipped) of its image
  `(e', i')` (`liftV`, `liftV_pv`), and fine steps go along (`liftS`). Both are bijections, with
  inverses given by the reversed match, and they preserve unordered endpoints, so
  `OneEdgeSplitRefinement.laplacianEquivOfUnorientedUnitSteps` applies.
-/

namespace Utilities.Subdivision.ScaleLift

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph

variable {n p m q : ℕ}

/-! ## 1.  Clamped path vertices -/

/-- The vertex at path position `a` of slot `e`, clamped to the slot. -/
def pv (s : Spec n p) (e : Fin p) (a : ℕ) : s.Vertex :=
  s.pathVertex e ⟨min a (s.length e), by omega⟩

section PathVertex

variable (s : Spec n p)

theorem pv_zero (e : Fin p) : pv s e 0 = s.coreVertex (s.core.tail e) := by
  unfold pv Spec.pathVertex
  simp

theorem pv_length (e : Fin p) : pv s e (s.length e) = s.coreVertex (s.core.head e) := by
  have hpos := s.length_pos e
  unfold pv Spec.pathVertex
  simp [hpos.ne']

theorem pv_interior (e : Fin p) (a : ℕ) (h0 : 0 < a) (hL : a < s.length e) :
    pv s e a = s.interiorVertex e ⟨a - 1, by omega⟩ := by
  unfold pv Spec.pathVertex
  have hmin : min a (s.length e) = a := min_eq_left hL.le
  rw [dite_eq_right (by simp only [hmin]; omega), dite_eq_right (by simp only [hmin]; omega)]
  simp only [hmin]

theorem stepLeft_eq_pv (e : Fin p) (o : Fin (s.length e)) :
    s.stepLeft e o = pv s e o.val := by
  rw [← s.pathVertex_stepLeftPosition e o, pv]
  congr 1
  ext
  simp only [Spec.stepLeftPosition]
  have := o.isLt
  omega

theorem stepRight_eq_pv (e : Fin p) (o : Fin (s.length e)) :
    s.stepRight e o = pv s e (o.val + 1) := by
  rw [← s.pathVertex_stepRightPosition e o, pv]
  congr 1
  ext
  simp only [Spec.stepRightPosition]
  have := o.isLt
  omega

theorem pv_interiorVertex (e : Fin p) (o : Fin (s.length e - 1)) :
    pv s e (o.val + 1) = s.interiorVertex e o := by
  have := o.isLt
  rw [pv_interior s e (o.val + 1) (by omega) (by omega)]
  rfl

variable (k : ℕ) (hk : 0 < k)

theorem fineOf_pv (e : Fin p) (a : ℕ) (ha : a ≤ s.length e) :
    s.fineOf k hk (pv s e a) = pv (s.scale k hk) e (k * a) := by
  rw [pv, s.fineOf_pathVertex k hk, pv]
  congr 1
  ext
  simp only [Spec.scaledPosition_val, Spec.scale_length]
  have h1 : min a (s.length e) = a := min_eq_left ha
  have h2 : k * a ≤ k * s.length e := Nat.mul_le_mul_left k ha
  rw [h1, min_eq_left h2]

end PathVertex

/-- Two unit steps with the same slot and offset are equal. -/
theorem step_ext {s : Spec n p} {σ τ : s.Step} (h1 : σ.1 = τ.1) (h2 : σ.2.val = τ.2.val) :
    σ = τ := by
  rcases σ with ⟨e, i⟩
  rcases τ with ⟨e', i'⟩
  simp only at h1
  subst h1
  simp only at h2
  rw [Fin.ext h2]

/-! ## 2.  Step matchings -/

/-- **A step matching**: a vertex equivalence and an equivalence of unit steps carrying the
two ends of every step to the two ends of its image, reversed when `flip` holds. -/
structure StepMatch (s : Spec n p) (t : Spec m q) where
  vtx : s.Vertex ≃ t.Vertex
  step : s.Step ≃ t.Step
  flip : s.Step → Bool
  left : ∀ σ : s.Step, pv t (step σ).1 (step σ).2.val =
    vtx (pv s σ.1 (if flip σ then σ.2.val + 1 else σ.2.val))
  right : ∀ σ : s.Step, pv t (step σ).1 ((step σ).2.val + 1) =
    vtx (pv s σ.1 (if flip σ then σ.2.val else σ.2.val + 1))

namespace StepMatch

variable {s : Spec n p} {t : Spec m q}

/-- The reversed matching. -/
def symm (M : StepMatch s t) : StepMatch t s where
  vtx := M.vtx.symm
  step := M.step.symm
  flip := fun τ ↦ M.flip (M.step.symm τ)
  left := by
    intro τ
    have hl := M.left (M.step.symm τ)
    have hr := M.right (M.step.symm τ)
    rw [Equiv.apply_symm_apply] at hl hr
    cases hf : M.flip (M.step.symm τ)
    · rw [hf] at hl
      simp only [Bool.false_eq_true, ite_false] at hl ⊢
      rw [hl, Equiv.symm_apply_apply]
    · rw [hf] at hr
      simp only [ite_true] at hr ⊢
      rw [hr, Equiv.symm_apply_apply]
  right := by
    intro τ
    have hl := M.left (M.step.symm τ)
    have hr := M.right (M.step.symm τ)
    rw [Equiv.apply_symm_apply] at hl hr
    cases hf : M.flip (M.step.symm τ)
    · rw [hf] at hr
      simp only [Bool.false_eq_true, ite_false] at hr ⊢
      rw [hr, Equiv.symm_apply_apply]
    · rw [hf] at hl
      simp only [ite_true] at hl ⊢
      rw [hl, Equiv.symm_apply_apply]

theorem symm_symm_flip (M : StepMatch s t) : M.symm.symm.flip = M.flip := by
  funext σ
  show M.flip (M.step.symm (M.step σ)) = M.flip σ
  rw [Equiv.symm_apply_apply]

end StepMatch

/-! ## 3.  Every Laplacian equivalence has a step matching -/

section Existence

variable {s : Spec n p} {t : Spec m q}

/-- The unordered ends of a unit step. -/
def ends (s : Spec n p) (σ : s.Step) : Sym2 s.Vertex :=
  s(pv s σ.1 σ.2.val, pv s σ.1 (σ.2.val + 1))

theorem unitEdge_eq_pv (s : Spec n p) (σ : s.Step) :
    s.unitEdge σ = (pv s σ.1 σ.2.val, pv s σ.1 (σ.2.val + 1)) := by
  rw [Spec.unitEdge, stepLeft_eq_pv, stepRight_eq_pv]

theorem pv_ne_pv_succ (s : Spec n p) (σ : s.Step) :
    pv s σ.1 σ.2.val ≠ pv s σ.1 (σ.2.val + 1) := by
  rw [← stepLeft_eq_pv, ← stepRight_eq_pv]
  exact s.stepLeft_ne_stepRight σ.1 σ.2

theorem card_ends_fibre (s : Spec n p) (x y : s.Vertex) :
    Fintype.card {σ : s.Step // ends s σ = s(x, y)} = num_edges s.graph x y := by
  classical
  rw [s.num_edges_eq_card_filter_steps, Fintype.card_subtype]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ends, unitEdge_eq_pv,
    Sym2.eq_iff, Prod.mk.injEq]

/-- **Every Laplacian equivalence of two subdivision presentations has a step matching.** -/
theorem exists_stepMatch (φ : LaplacianEquiv s.graph t.graph) :
    ∃ M : StepMatch s t, M.vtx = φ.toEquiv := by
  classical
  let f : s.Step → Sym2 t.Vertex := fun σ ↦ Sym2.map φ.toEquiv (ends s σ)
  let g : t.Step → Sym2 t.Vertex := fun τ ↦ ends t τ
  have hcard : ∀ c : Sym2 t.Vertex,
      Fintype.card {σ // f σ = c} = Fintype.card {τ // g τ = c} := by
    intro c
    induction c using Sym2.ind with
    | h x' y' =>
      obtain ⟨x, rfl⟩ := φ.toEquiv.surjective x'
      obtain ⟨y, rfl⟩ := φ.toEquiv.surjective y'
      have hf : ∀ σ, f σ = s(φ.toEquiv x, φ.toEquiv y) ↔ ends s σ = s(x, y) := by
        intro σ
        simp only [f, ends, Sym2.map_mk, Sym2.eq_iff, φ.toEquiv.injective.eq_iff]
      rw [Fintype.card_congr (Equiv.subtypeEquivRight hf), card_ends_fibre,
        card_ends_fibre]
      exact (φ.num_edges_eq x y).symm
  let τ : s.Step ≃ t.Step :=
    Equiv.ofFiberEquiv (fun c ↦ Fintype.equivOfCardEq (hcard c))
  have hτ : ∀ σ, ends t (τ σ) = Sym2.map φ.toEquiv (ends s σ) :=
    fun σ ↦ Equiv.ofFiberEquiv_map (fun c ↦ Fintype.equivOfCardEq (hcard c)) σ
  have hpair : ∀ σ,
      (pv t (τ σ).1 (τ σ).2.val = φ.toEquiv (pv s σ.1 σ.2.val) ∧
          pv t (τ σ).1 ((τ σ).2.val + 1) = φ.toEquiv (pv s σ.1 (σ.2.val + 1))) ∨
        (pv t (τ σ).1 (τ σ).2.val = φ.toEquiv (pv s σ.1 (σ.2.val + 1)) ∧
          pv t (τ σ).1 ((τ σ).2.val + 1) = φ.toEquiv (pv s σ.1 σ.2.val)) := by
    intro σ
    have h := hτ σ
    simp only [ends, Sym2.map_mk, Sym2.eq_iff] at h
    exact h
  refine ⟨⟨φ.toEquiv, τ,
      fun σ ↦ decide (pv t (τ σ).1 (τ σ).2.val ≠ φ.toEquiv (pv s σ.1 σ.2.val)), ?_, ?_⟩, rfl⟩
  · intro σ
    by_cases hl : pv t (τ σ).1 (τ σ).2.val = φ.toEquiv (pv s σ.1 σ.2.val)
    · simp only [hl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
    · simp only [ne_eq, hl, not_false_eq_true, decide_true, ite_true]
      rcases hpair σ with h | h
      · exact absurd h.1 hl
      · exact h.1
  · intro σ
    by_cases hl : pv t (τ σ).1 (τ σ).2.val = φ.toEquiv (pv s σ.1 σ.2.val)
    · simp only [hl, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ite_false]
      rcases hpair σ with h | h
      · exact h.2
      · exfalso
        apply pv_ne_pv_succ s σ
        exact φ.toEquiv.injective (h.1.symm.trans hl).symm
    · simp only [ne_eq, hl, not_false_eq_true, decide_true, ite_true]
      rcases hpair σ with h | h
      · exact absurd h.1 hl
      · exact h.2

end Existence


/-! ## 4.  Refining a step matching -/

section Refine

variable {s : Spec n p} {t : Spec m q}

/-- The coarse step containing fine position `a` of slot `e`. -/
def coarseStep (s : Spec n p) (k : ℕ) (hk : 0 < k) (e : Fin p) (a : ℕ)
    (h : a < k * s.length e) : s.Step :=
  ⟨e, ⟨a / k, (Nat.div_lt_iff_lt_mul hk).mpr (by rw [Nat.mul_comm] at h; exact h)⟩⟩

theorem div_eq_of_lt' {k i r : ℕ} (hk : 0 < k) (hr : r < k) : (k * i + r) / k = i := by
  rw [Nat.mul_add_div hk, Nat.div_eq_of_lt hr, Nat.add_zero]

theorem mod_eq_of_lt' {k i r : ℕ} (hr : r < k) : (k * i + r) % k = r := by
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

theorem coarseStep_eq (s : Spec n p) (k : ℕ) (hk : 0 < k) (σ : s.Step) (r : ℕ) (hr : r < k)
    (h : k * σ.2.val + r < k * s.length σ.1) : coarseStep s k hk σ.1 (k * σ.2.val + r) h = σ :=
  step_ext rfl (div_eq_of_lt' hk hr)

theorem mul_add_lt {k i L r : ℕ} (hi : i < L) (hr : r < k) : k * i + r < k * L := by
  have : k * (i + 1) ≤ k * L := Nat.mul_le_mul_left k hi
  rw [Nat.mul_succ] at this
  omega

theorem mul_add_le {k i L r : ℕ} (hi : i < L) (hr : r ≤ k) : k * i + r ≤ k * L := by
  have : k * (i + 1) ≤ k * L := Nat.mul_le_mul_left k hi
  rw [Nat.mul_succ] at this
  omega

namespace StepMatch

variable (M : StepMatch s t) (k : ℕ) (hk : 0 < k)

/-- Where fine offset `r` of the coarse step `σ` goes along its image. -/
def img (σ : s.Step) (r : ℕ) : ℕ :=
  k * (M.step σ).2.val + (if M.flip σ then k - r else r)

/-- **The refined vertex map.** A fine vertex over a coarse vertex goes to the fine vertex over
its image; a fine vertex inside a coarse step goes to the matching position inside the image
step. -/
def liftV : (s.scale k hk).Vertex → (t.scale k hk).Vertex
  | Sum.inl w => t.fineOf k hk (M.vtx (Sum.inl w))
  | Sum.inr ⟨e, o⟩ =>
    if (o.val + 1) % k = 0 then
      t.fineOf k hk (M.vtx (pv s e ((o.val + 1) / k)))
    else
      pv (t.scale k hk)
        (M.step (coarseStep s k hk e (o.val + 1)
          (by have := o.isLt; simp only [Spec.scale_length] at this; omega))).1
        (M.img k (coarseStep s k hk e (o.val + 1)
          (by have := o.isLt; simp only [Spec.scale_length] at this; omega)) ((o.val + 1) % k))

theorem liftV_fineOf (x : s.Vertex) :
    M.liftV k hk (s.fineOf k hk x) = t.fineOf k hk (M.vtx x) := by
  rcases x with w | ⟨e, j⟩
  · rfl
  · have hj := j.isLt
    have hpos : 1 ≤ k * (j.val + 1) := Nat.mul_pos hk (Nat.succ_pos _)
    have ha : k * (j.val + 1) - 1 + 1 = k * (j.val + 1) := by omega
    show M.liftV k hk (Sum.inr ⟨e, ⟨k * (j.val + 1) - 1, _⟩⟩) = _
    simp only [liftV]
    rw [ite_eq_left (by rw [ha]; exact Nat.mul_mod_right k _), ha,
      Nat.mul_div_cancel_left _ hk, pv_interiorVertex]
    rfl

/-- **The refined vertex map along a coarse step.** -/
theorem liftV_pv (σ : s.Step) (r : ℕ) (hr : r ≤ k) :
    M.liftV k hk (pv (s.scale k hk) σ.1 (k * σ.2.val + r)) =
      pv (t.scale k hk) (M.step σ).1 (M.img k σ r) := by
  have hi := σ.2.isLt
  have hi' := (M.step σ).2.isLt
  have hl := M.left σ
  have hrt := M.right σ
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [Nat.add_zero, ← fineOf_pv s k hk σ.1 _ hi.le, liftV_fineOf]
    unfold img
    cases hf : M.flip σ
    · simp only [hf, Bool.false_eq_true, ite_false] at hl ⊢
      rw [← hl, fineOf_pv t k hk _ _ hi'.le, Nat.add_zero]
    · simp only [hf, ite_true] at hrt ⊢
      rw [← hrt, fineOf_pv t k hk _ _ hi', Nat.sub_zero, Nat.mul_succ]
  · rcases Nat.lt_or_ge r k with hrk | hrk
    · have hlt : k * σ.2.val + r < k * s.length σ.1 := mul_add_lt hi hrk
      rw [pv_interior (s.scale k hk) σ.1 _ (by omega) (by simpa using hlt)]
      show M.liftV k hk (Sum.inr ⟨σ.1, ⟨k * σ.2.val + r - 1, _⟩⟩) = _
      simp only [liftV]
      have ha : k * σ.2.val + r - 1 + 1 = k * σ.2.val + r := by omega
      have hmod : (k * σ.2.val + r - 1 + 1) % k = r := by rw [ha]; exact mod_eq_of_lt' hrk
      rw [ite_eq_right (by rw [hmod]; omega)]
      have hc : ∀ h, coarseStep s k hk σ.1 (k * σ.2.val + r - 1 + 1) h = σ := by
        intro h
        exact step_ext rfl (by simp only [coarseStep]; rw [ha]; exact div_eq_of_lt' hk hrk)
      rw [hc, hmod]
    · have hrk' : r = k := le_antisymm hr hrk
      rw [hrk', show k * σ.2.val + k = k * (σ.2.val + 1) by rw [Nat.mul_succ],
        ← fineOf_pv s k hk σ.1 _ hi, liftV_fineOf]
      unfold img
      cases hf : M.flip σ
      · simp only [hf, Bool.false_eq_true, ite_false] at hrt ⊢
        rw [← hrt, fineOf_pv t k hk _ _ hi', Nat.mul_succ]
      · simp only [hf, ite_true] at hl ⊢
        rw [← hl, fineOf_pv t k hk _ _ hi'.le, Nat.sub_self, Nat.add_zero]

/-- Every fine vertex is over a coarse vertex or strictly inside a coarse step. -/
theorem fine_cases (z : (s.scale k hk).Vertex) :
    (∃ x, z = s.fineOf k hk x) ∨
      ∃ σ : s.Step, ∃ r, 0 < r ∧ r < k ∧ z = pv (s.scale k hk) σ.1 (k * σ.2.val + r) := by
  rcases z with w | ⟨e, o⟩
  · exact Or.inl ⟨Sum.inl w, rfl⟩
  · have ho := o.isLt
    simp only [Spec.scale_length] at ho
    have hlt : o.val + 1 < k * s.length e := by omega
    have hz : (Sum.inr ⟨e, o⟩ : (s.scale k hk).Vertex) = pv (s.scale k hk) e (o.val + 1) :=
      (pv_interiorVertex (s.scale k hk) e o).symm
    have hdm := Nat.div_add_mod (o.val + 1) k
    by_cases hd : (o.val + 1) % k = 0
    · refine Or.inl ⟨pv s e ((o.val + 1) / k), ?_⟩
      have hle : (o.val + 1) / k ≤ s.length e :=
        ((Nat.div_lt_iff_lt_mul hk).mpr (by rw [Nat.mul_comm] at hlt; exact hlt)).le
      rw [fineOf_pv s k hk e _ hle, hz]
      congr 1
      omega
    · refine Or.inr ⟨coarseStep s k hk e (o.val + 1) hlt, (o.val + 1) % k,
        Nat.pos_of_ne_zero hd, Nat.mod_lt _ hk, ?_⟩
      rw [hz]
      simp only [coarseStep]
      congr 1
      omega

/-- The two refined maps agree when the matchings have the same data. -/
theorem liftV_congr (M₁ M₂ : StepMatch s t) (h1 : M₁.vtx = M₂.vtx) (h2 : M₁.step = M₂.step)
    (h3 : M₁.flip = M₂.flip) : M₁.liftV k hk = M₂.liftV k hk := by
  cases M₁
  cases M₂
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem liftV_symm_liftV (z : (s.scale k hk).Vertex) :
    M.symm.liftV k hk (M.liftV k hk z) = z := by
  rcases fine_cases k hk z with ⟨x, rfl⟩ | ⟨σ, r, hr0, hrk, rfl⟩
  · rw [liftV_fineOf, liftV_fineOf]
    show s.fineOf k hk (M.vtx.symm (M.vtx x)) = _
    rw [Equiv.symm_apply_apply]
  · rw [liftV_pv M k hk σ r hrk.le]
    unfold img
    rw [liftV_pv M.symm k hk (M.step σ) _ (by split_ifs <;> omega)]
    unfold img
    show pv (s.scale k hk) (M.step.symm (M.step σ)).1
        (k * (M.step.symm (M.step σ)).2.val +
          (if M.flip (M.step.symm (M.step σ)) then
            k - (if M.flip σ then k - r else r) else (if M.flip σ then k - r else r))) = _
    rw [Equiv.symm_apply_apply]
    congr 1
    split_ifs <;> omega

theorem liftV_liftV_symm (z : (t.scale k hk).Vertex) :
    M.liftV k hk (M.symm.liftV k hk z) = z := by
  have h := liftV_symm_liftV M.symm k hk z
  rwa [liftV_congr k hk M.symm.symm M rfl rfl (symm_symm_flip M)] at h

/-- **The refined step map.** -/
def liftS : (s.scale k hk).Step → (t.scale k hk).Step
  | ⟨e, j⟩ =>
    ⟨(M.step (coarseStep s k hk e j.val j.isLt)).1,
      ⟨k * (M.step (coarseStep s k hk e j.val j.isLt)).2.val +
        (if M.flip (coarseStep s k hk e j.val j.isLt) then k - 1 - j.val % k else j.val % k),
        mul_add_lt (M.step (coarseStep s k hk e j.val j.isLt)).2.isLt
          (by have := Nat.mod_lt j.val hk; split_ifs <;> omega)⟩⟩

theorem liftS_unitEdge (φ : (s.scale k hk).Step) :
    (t.scale k hk).unitEdge (M.liftS k hk φ) =
        (M.liftV k hk ((s.scale k hk).unitEdge φ).1,
          M.liftV k hk ((s.scale k hk).unitEdge φ).2) ∨
      (t.scale k hk).unitEdge (M.liftS k hk φ) =
        (M.liftV k hk ((s.scale k hk).unitEdge φ).2,
          M.liftV k hk ((s.scale k hk).unitEdge φ).1) := by
  rcases φ with ⟨e, j⟩
  set σ := coarseStep s k hk e j.val j.isLt with hσ
  have hrk := Nat.mod_lt j.val hk
  have hdm : k * σ.2.val + j.val % k = j.val := Nat.div_add_mod j.val k
  have hleft : pv (s.scale k hk) e j.val = pv (s.scale k hk) σ.1 (k * σ.2.val + j.val % k) := by
    rw [hdm]; rfl
  have hright : pv (s.scale k hk) e (j.val + 1) =
      pv (s.scale k hk) σ.1 (k * σ.2.val + (j.val % k + 1)) := by
    rw [← Nat.add_assoc, hdm]; rfl
  rw [unitEdge_eq_pv, unitEdge_eq_pv]
  simp only
  rw [hleft, hright, liftV_pv M k hk σ _ hrk.le, liftV_pv M k hk σ _ hrk]
  have h1 : (M.liftS k hk ⟨e, j⟩).1 = (M.step σ).1 := rfl
  have h2 : (M.liftS k hk ⟨e, j⟩).2.val = k * (M.step σ).2.val +
      (if M.flip σ then k - 1 - j.val % k else j.val % k) := rfl
  rw [h2, h1]
  unfold img
  cases M.flip σ
  · left
    simp only [Bool.false_eq_true, ite_false, Nat.add_assoc]
  · right
    simp only [ite_true, Prod.mk.injEq]
    constructor <;> congr 1 <;> omega

theorem liftS_congr (M₁ M₂ : StepMatch s t) (h1 : M₁.vtx = M₂.vtx) (h2 : M₁.step = M₂.step)
    (h3 : M₁.flip = M₂.flip) : M₁.liftS k hk = M₂.liftS k hk := by
  cases M₁
  cases M₂
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

/-- The refined step map, read off at any fine step inside a known coarse step. -/
theorem liftS_of (φ : (s.scale k hk).Step) (σ : s.Step) (r : ℕ) (hr : r < k)
    (h1 : φ.1 = σ.1) (h2 : φ.2.val = k * σ.2.val + r) :
    (M.liftS k hk φ).1 = (M.step σ).1 ∧
      (M.liftS k hk φ).2.val = k * (M.step σ).2.val + (if M.flip σ then k - 1 - r else r) := by
  rcases φ with ⟨e, j⟩
  simp only at h1 h2
  subst h1
  have hc : coarseStep s k hk σ.1 j.val j.isLt = σ :=
    step_ext rfl (by simp only [coarseStep]; rw [h2]; exact div_eq_of_lt' hk hr)
  have hmod : j.val % k = r := by rw [h2]; exact mod_eq_of_lt' hr
  constructor
  · show (M.step (coarseStep s k hk σ.1 j.val j.isLt)).1 = _
    rw [hc]
  · show k * (M.step (coarseStep s k hk σ.1 j.val j.isLt)).2.val +
        (if M.flip (coarseStep s k hk σ.1 j.val j.isLt) then k - 1 - j.val % k
          else j.val % k) = _
    rw [hc, hmod]

theorem liftS_symm_liftS (φ : (s.scale k hk).Step) :
    M.symm.liftS k hk (M.liftS k hk φ) = φ := by
  have hrk := Nat.mod_lt φ.2.val hk
  obtain ⟨h1, h2⟩ := M.liftS_of k hk φ (coarseStep s k hk φ.1 φ.2.val φ.2.isLt)
    (φ.2.val % k) hrk rfl (Nat.div_add_mod φ.2.val k).symm
  have hr' : (if M.flip (coarseStep s k hk φ.1 φ.2.val φ.2.isLt) then k - 1 - φ.2.val % k
      else φ.2.val % k) < k := by
    split_ifs <;> omega
  obtain ⟨h3, h4⟩ := M.symm.liftS_of k hk (M.liftS k hk φ) _ _ hr' h1 h2
  have hss : M.symm.step (M.step (coarseStep s k hk φ.1 φ.2.val φ.2.isLt)) =
      coarseStep s k hk φ.1 φ.2.val φ.2.isLt := Equiv.symm_apply_apply _ _
  have hsf : M.symm.flip (M.step (coarseStep s k hk φ.1 φ.2.val φ.2.isLt)) =
      M.flip (coarseStep s k hk φ.1 φ.2.val φ.2.isLt) := by
    show M.flip (M.step.symm (M.step _)) = _
    rw [Equiv.symm_apply_apply]
  rw [hss] at h3 h4
  rw [hsf] at h4
  refine step_ext h3 ?_
  rw [h4]
  have hval : (coarseStep s k hk φ.1 φ.2.val φ.2.isLt).2.val = φ.2.val / k := rfl
  rw [hval]
  have hdm := Nat.div_add_mod φ.2.val k
  cases hb : M.flip (coarseStep s k hk φ.1 φ.2.val φ.2.isLt) <;>
    simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem liftS_liftS_symm (φ : (t.scale k hk).Step) :
    M.liftS k hk (M.symm.liftS k hk φ) = φ := by
  have h := liftS_symm_liftS M.symm k hk φ
  rwa [liftS_congr k hk M.symm.symm M rfl rfl (symm_symm_flip M)] at h

/-- **The refined Laplacian equivalence.** -/
def scaledEquiv : LaplacianEquiv (s.scale k hk).graph (t.scale k hk).graph :=
  OneEdgeSplitRefinement.laplacianEquivOfUnorientedUnitSteps (s.scale k hk) (t.scale k hk)
    ⟨M.liftV k hk, M.symm.liftV k hk, M.liftV_symm_liftV k hk, M.liftV_liftV_symm k hk⟩
    ⟨M.liftS k hk, M.symm.liftS k hk, M.liftS_symm_liftS k hk, M.liftS_liftS_symm k hk⟩
    (M.liftS_unitEdge k hk)

theorem scaledEquiv_fineOf (x : s.Vertex) :
    M.scaledEquiv k hk (s.fineOf k hk x) = t.fineOf k hk (M.vtx x) :=
  M.liftV_fineOf k hk x

end StepMatch

end Refine

/-! ## 5.  The lift -/

/-- **A Laplacian equivalence lifts to every uniform refinement, commuting with `fineOf`.** -/
theorem exists_scaledEquiv {s : Spec n p} {t : Spec m q} (φ : LaplacianEquiv s.graph t.graph)
    (k : ℕ) (hk : 0 < k) :
    ∃ ψ : LaplacianEquiv (s.scale k hk).graph (t.scale k hk).graph,
      ∀ x : s.Vertex, ψ (s.fineOf k hk x) = t.fineOf k hk (φ x) := by
  obtain ⟨M, hM⟩ := exists_stepMatch φ
  refine ⟨M.scaledEquiv k hk, fun x ↦ ?_⟩
  rw [M.scaledEquiv_fineOf k hk x, hM]

/-- **Embedded divisors transport along the lift.** -/
theorem mapDiv_embed {s : Spec n p} {t : Spec m q} (φ : LaplacianEquiv s.graph t.graph)
    (k : ℕ) (hk : 0 < k) (ψ : LaplacianEquiv (s.scale k hk).graph (t.scale k hk).graph)
    (hψ : ∀ x : s.Vertex, ψ (s.fineOf k hk x) = t.fineOf k hk (φ x)) (D : CFDiv s.graph) :
    ψ.mapDiv (s.embed k hk D) = t.embed k hk (φ.mapDiv D) := by
  classical
  funext y
  simp only [LaplacianEquiv.mapDiv_apply, Spec.embed]
  refine Fintype.sum_equiv φ.toEquiv _ _ (fun x ↦ ?_)
  have h1 : (s.fineOf k hk x = ψ.toEquiv.symm y) ↔ (t.fineOf k hk (φ.toEquiv x) = y) := by
    rw [← hψ x]
    constructor
    · intro h
      show ψ.toEquiv (s.fineOf k hk x) = y
      rw [h, Equiv.apply_symm_apply]
    · intro h
      rw [← h]
      exact (Equiv.symm_apply_apply _ _).symm
  by_cases h : s.fineOf k hk x = ψ.toEquiv.symm y
  · rw [ite_eq_left h, ite_eq_left (h1.mp h), Equiv.symm_apply_apply]
  · rw [ite_eq_right h, ite_eq_right (fun h' ↦ h (h1.mpr h'))]

end Utilities.Subdivision.ScaleLift
