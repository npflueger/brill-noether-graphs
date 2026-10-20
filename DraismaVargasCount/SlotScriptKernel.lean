module

public import Utilities.Subdivision.CoreExpansion
public import Utilities.Gonality.GonalityTransport
public import Utilities.Subdivision.SlopeScript
public import DraismaVargasCount.RowAlgebra

@[expose] public section

/-!
# A slot-valued script on an expanded core, and its descent

Let `D` be an expansion datum and `B = D.bigSpec (small.scale k hk)` the expanded core at scale
`k`. A script on `B` is given by a value `cp v` at every core vertex and a value `sv e o` at
every offset `o` of every slot `e` (`Spec.slotValueScript`). This module proves, for any such
`cp` and `sv`, what the pencil transports need of it; nothing here refers to a member, a frame or
a row.

* **Compatibility from the ends of an oriented row** (`compat_of_ends`): if `sv e o` is a row
  potential `rv e` read at the oriented position `RowAlgebra.orient`, and `rv e` takes the values
  of `cp` at the slot's ends before the row's start and after its full length, then `sv` is
  compatible with `cp` at both ends of every slot.
* **Descent** (`eq_of_fib_eq`, `slotValueScript_eq_of_vertexMap_eq`, `eq_pullScript_descend`):
  if `cp` agrees at the two ends of every contracted slot, it is constant on every fibre of
  `D.fib` (the last clause of `ExpansionData.Conditions`), so the script is constant on the fibres
  of the contraction and is the pull-back of the descended script `descend`.
* **The pushed Laplacian, slot by slot** (`pushDiv_prin_slotValueScript`): the pushforward of
  its Laplacian at a small vertex `b` is a sum over the unit steps of every slot of the step
  difference of `sv` times the difference of the indicator `hit` of `b`.
* **Linear equivalence** (`linear_equiv_of_slots`): two divisors on `small.scale k` whose
  difference is that slot sum are linearly equivalent, by the descended script.

## What is proved

`hit` (in the namespace `DraismaVargas.Count.PencilTransportProducer`), `compat_of_ends`,
`eq_of_fib_eq`, `slotValueScript_eq_of_vertexMap_eq`, `descend`, `eq_pullScript_descend`,
`pushDiv_prin_slotValueScript`, `linear_equiv_of_slots`.
-/

namespace DraismaVargas.Count.PencilTransportProducer

open Utilities.Certificate.SubdivisionGraph Utilities.Subdivision.CoreExpansion

section Compare

variable {n p N Q : ℕ} (D : ExpansionData n p N Q) (small : Spec n p) (k : ℕ) (hk : 0 < k)

/-- The indicator of the small vertex `b` along the `kindVertex` path of `e`. -/
noncomputable def hit (e : Fin Q) (b : (small.scale k hk).Vertex) (q : ℕ) : ℤ :=
  if kindVertex (small.scale k hk) (D.fib (D.bigCore.tail e)) (D.kind e) q = b then 1 else 0

end Compare

end DraismaVargas.Count.PencilTransportProducer

namespace DraismaVargas.Count.SlotScriptKernel

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Count.PencilTransportProducer (hit)

variable {n p N Q : ℕ} (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (cp : Fin N → ℤ) (sv : Fin Q → ℕ → ℤ)

/-! ## 1.  Compatibility from the two ends of an oriented row -/

/-- **Compatibility from the ends of the row.**  Read the row potential `rv e` of slot `e` at the
oriented position of each offset.  If before the row's start it is `cp` at the end the row
starts from, and after the slot's length `cp` at the other end, the slot values are compatible
with `cp` at both ends of every slot. -/
theorem compat_of_ends (rv : Fin Q → ℤ → ℤ) (rev : Fin Q → Bool)
    (hStart : ∀ e pos, pos ≤ 0 →
      rv e pos = cp (if rev e then D.bigCore.head e else D.bigCore.tail e))
    (hFinish : ∀ e pos, ((D.bigSpec (small.scale k hk) hN hL).length e : ℤ) ≤ pos →
      rv e pos = cp (if rev e then D.bigCore.tail e else D.bigCore.head e)) :
    (D.bigSpec (small.scale k hk) hN hL).SlotValueCompatible cp
      (fun e o ↦ rv e (RowAlgebra.orient (rev e) ((D.bigSpec (small.scale k hk) hN hL).length e)
        o)) := by
  constructor
  · intro e
    change rv e (RowAlgebra.orient (rev e) ((D.bigSpec (small.scale k hk) hN hL).length e) 0) =
      cp (D.bigCore.tail e)
    cases hr : rev e
    · simpa [RowAlgebra.orient, hr] using hStart e 0 le_rfl
    · simpa [RowAlgebra.orient, hr] using hFinish e _ le_rfl
  · intro e
    change rv e (RowAlgebra.orient (rev e) ((D.bigSpec (small.scale k hk) hN hL).length e)
      ((D.bigSpec (small.scale k hk) hN hL).length e)) = cp (D.bigCore.head e)
    cases hr : rev e
    · simpa [RowAlgebra.orient, hr] using hFinish e _ le_rfl
    · simpa [RowAlgebra.orient, hr] using hStart e 0 le_rfl

/-! ## 2.  Constancy on the fibres of the contraction, and descent -/

/-- **Constancy on the fibres of `D.fib`.**  A core potential agreeing at the two ends of every
contracted slot is constant on every fibre: the fibre is connected through contracted slots (the
last clause of `ExpansionData.Conditions`). -/
theorem eq_of_fib_eq (hCond : D.Conditions small.core)
    (hc : ∀ e, D.kind e = SlotKind.contracted → cp (D.bigCore.tail e) = cp (D.bigCore.head e))
    {v w : Fin N} (h : D.fib v = D.fib w) : cp v = cp w := by
  classical
  by_contra hne
  obtain ⟨e, hcon, -, hcross⟩ := ExpansionData.fibre_of_conditions hCond (D.fib v)
    (Finset.univ.filter fun u ↦ cp u = cp v)
    ⟨v, by simp, rfl⟩ ⟨w, by simpa using fun h' ↦ hne h'.symm, h.symm⟩
  have hEq := hc e hcon
  rcases hcross with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 (hEq.symm.trans h1)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h2 (hEq.trans h1)

/-- **The script descends**: with `cp` constant on the fibres of `D.fib`, the script is constant
on the fibres of the contraction. -/
theorem slotValueScript_eq_of_vertexMap_eq (hCond : D.Conditions small.core)
    (hFib : ∀ v w, D.fib v = D.fib w → cp v = cp w)
    {x x' : (D.bigSpec (small.scale k hk) hN hL).Vertex}
    (h : ExpansionData.vertexMap D (small.scale k hk) hN hL x =
      ExpansionData.vertexMap D (small.scale k hk) hN hL x') :
    (D.bigSpec (small.scale k hk) hN hL).slotValueScript cp sv x =
      (D.bigSpec (small.scale k hk) hN hL).slotValueScript cp sv x' := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  rcases x with v | ⟨e, o⟩
  · rcases x' with w | ⟨e', o'⟩
    · have hfib : D.fib v = D.fib w := by
        have h' : (small.scale k hk).coreVertex (D.fib v) =
            (small.scale k hk).coreVertex (D.fib w) := h
        exact Sum.inl.inj h'
      exact hFib v w hfib
    · rw [ExpansionData.interior_fibre hCond' e' o' _ h]
      rfl
  · rw [ExpansionData.interior_fibre hCond' e o x' h.symm]
    rfl

/-- The descent of a script on `B` to the small subdivision: its value at a chosen preimage. -/
noncomputable def descend (hCond : D.Conditions small.core)
    (f : firing_script (D.bigSpec (small.scale k hk) hN hL).graph) :
    firing_script (small.scale k hk).graph := fun b ↦
  f (Classical.choose (ExpansionData.vertexMap_surjective
    (D := D) (small := small.scale k hk) (hN := hN) (hL := hL) hCond b))

/-- A script constant on the fibres of the contraction is the pull-back of its descent. -/
theorem eq_pullScript_descend (hCond : D.Conditions small.core)
    (f : firing_script (D.bigSpec (small.scale k hk) hN hL).graph)
    (hf : ∀ x x', ExpansionData.vertexMap D (small.scale k hk) hN hL x =
      ExpansionData.vertexMap D (small.scale k hk) hN hL x' → f x = f x') :
    f = (ExpansionData.certificate D (small.scale k hk) hN hL).pullScript
      (descend D small hN hL k hk hCond f) := by
  funext x
  exact hf _ _ (Classical.choose_spec (ExpansionData.vertexMap_surjective
    (D := D) (small := small.scale k hk) (hN := hN) (hL := hL) hCond
    (ExpansionData.vertexMap D (small.scale k hk) hN hL x))).symm

/-! ## 3.  The pushed Laplacian, slot by slot -/

/-- **The pushed Laplacian of a compatible slot-value script**, as a sum over the unit steps of
every slot: the step difference of `sv` times the difference of the indicator `hit` of `b` at
the two ends of the step. -/
theorem pushDiv_prin_slotValueScript (hCond : D.Conditions small.core)
    (hC : (D.bigSpec (small.scale k hk) hN hL).SlotValueCompatible cp sv)
    (b : (small.scale k hk).Vertex) :
    (ExpansionData.certificate D (small.scale k hk) hN hL).pushDiv
        (prin (D.bigSpec (small.scale k hk) hN hL).graph
          ((D.bigSpec (small.scale k hk) hN hL).slotValueScript cp sv)) b =
      ∑ e : Fin Q, ∑ o : Fin ((D.bigSpec (small.scale k hk) hN hL).length e),
        (sv e (o.val + 1) - sv e o.val) *
          (hit D small k hk e b o.val - hit D small k hk e b (o.val + 1)) := by
  classical
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  set B := D.bigSpec (small.scale k hk) hN hL
  have hSlope := B.isStepSlope_slotValueScript hC
  unfold GraphContractionCertificate.pushDiv
  rw [Finset.sum_congr rfl fun x _ ↦ by rw [B.prin_eq_sum_slopes hSlope x]]
  have hSwap : ∀ x : B.Vertex,
      (if (ExpansionData.certificate D (small.scale k hk) hN hL).vertexMap x = b then
        ∑ step : B.Step,
          ((if B.stepLeft step.1 step.2 = x then
              sv step.1 (step.2.val + 1) - sv step.1 step.2.val else 0) +
            (if B.stepRight step.1 step.2 = x then
              -(sv step.1 (step.2.val + 1) - sv step.1 step.2.val) else 0))
      else 0) =
        ∑ step : B.Step,
          ((if B.stepLeft step.1 step.2 = x then
              (if ExpansionData.vertexMap D (small.scale k hk) hN hL x = b then
                sv step.1 (step.2.val + 1) - sv step.1 step.2.val else 0)
            else 0) +
            (if B.stepRight step.1 step.2 = x then
              (if ExpansionData.vertexMap D (small.scale k hk) hN hL x = b then
                -(sv step.1 (step.2.val + 1) - sv step.1 step.2.val) else 0)
            else 0)) := by
    intro x
    by_cases hx : (ExpansionData.certificate D (small.scale k hk) hN hL).vertexMap x = b
    · rw [ite_eq_left hx]
      refine Finset.sum_congr rfl fun step _ ↦ ?_
      have hx' : ExpansionData.vertexMap D (small.scale k hk) hN hL x = b := hx
      simp only [hx', ite_true]
    · rw [ite_eq_right hx]
      have hx' : ¬ ExpansionData.vertexMap D (small.scale k hk) hN hL x = b := hx
      simp only [hx', ite_false, ite_self, add_zero, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl fun x _ ↦ hSwap x, Finset.sum_comm]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_add_distrib, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun o _ ↦ ?_
  rw [ExpansionData.vertexMap_stepLeft hCond' e o, ExpansionData.vertexMap_stepRight hCond' e o]
  unfold hit
  split_ifs <;> ring

/-! ## 4.  Linear equivalence -/

/-- **Linear equivalence from the slot sum.**  If the difference `A' - A` of two divisors on
`small.scale k` is, at every vertex, the slot sum of a compatible script constant on the fibres
of `D.fib`, then `A` and `A'` are linearly equivalent: `A' - A` is the Laplacian of the descended
script (`pushDiv_prin_pullScript`). -/
theorem linear_equiv_of_slots (hCond : D.Conditions small.core)
    (hFib : ∀ v w, D.fib v = D.fib w → cp v = cp w)
    (hC : (D.bigSpec (small.scale k hk) hN hL).SlotValueCompatible cp sv)
    (A A' : CFDiv (small.scale k hk).graph)
    (hSmall : ∀ b, A' b - A b =
      ∑ e : Fin Q, ∑ o : Fin ((D.bigSpec (small.scale k hk) hN hL).length e),
        (sv e (o.val + 1) - sv e o.val) *
          (hit D small k hk e b o.val - hit D small k hk e b (o.val + 1))) :
    linear_equiv (small.scale k hk).graph A A' := by
  have hCond' : D.Conditions (small.scale k hk).core := hCond
  unfold linear_equiv
  rw [principal_iff_eq_prin]
  refine ⟨descend D small hN hL k hk hCond
    ((D.bigSpec (small.scale k hk) hN hL).slotValueScript cp sv), ?_⟩
  rw [← (ExpansionData.certificate D (small.scale k hk) hN hL).pushDiv_prin_pullScript
      (ExpansionData.certificate_valid hCond'),
    ← eq_pullScript_descend D small hN hL k hk hCond _
      (fun _ _ h ↦ slotValueScript_eq_of_vertexMap_eq D small hN hL k hk cp sv hCond hFib h)]
  funext b
  rw [Pi.sub_apply, hSmall b, pushDiv_prin_slotValueScript D small hN hL k hk cp sv hCond hC b]

end DraismaVargas.Count.SlotScriptKernel
