import DraismaVargasCount.GeneralKRowCore

/-!
# The census of a star-shaped wall block, for an arbitrary candidate

Vargas, Part II (arXiv:2609.09109), the rigidity above `w_0` (`lemma-above-w0`) in the
section on changing combinatorial type.  Fix a globally assembled candidate `C` over a
valid datum `G`, and a
wall block (named by a sheet `x`) at which the candidate's resolution is a
*star* (`NonTrivalentValencyFourRows.IsStar`): one endpoint, on the side
`ret C x`, keeps the whole wall block, and the other endpoint is the new-edge
partition.  So above that block the candidate has one *retaining* vertex `R`,
one *fine* vertex per new-edge class, and one new occurrence joining `R` to
each fine vertex.

This file computes the surviving stars at `R` and at the fine vertices from
the survivors of `G` at the block, under three hypotheses on the block
(`StarHyp`): target-direction injectivity, surviving valency at most three,
and at most two wall edges on one side of the pairing.  The consequences are
the three facts the row dictionary needs:

* `descent`: two survivors that are consecutive in `G` at the block stay on
  one stable row of `C`;
* `absorbed`: a surviving new occurrence of the block lies on the stable row
  of a retained survivor of the block;
* the census lemmas `ret_*` / `fine_*` used by `GeneralKRowEquiv` to show that
  the reverse row map is constant on consecutive pairs.

This is the argument of Part I's `K = 0` modules
`NonTrivalentValencyFourRowEquiv`, `…Descent`, `…RowEquivFinal` §§2--3 and
`…RetainedInjective` §5, re-proved over an arbitrary candidate so that it
applies to the general-`K` candidate.

## What is NOT proved here

Nothing about the anchor block (the one block that is not a star).  The
hypotheses of `StarHyp` are discharged for `GeneralKExitSetup.candK` in
`GeneralKRowsK.starHyp`.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKRowStar

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.GeneralKRowCore

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {G : GluingDatum target degree}

/-- A surviving occurrence of `G` at the wall block of the sheet `x`. -/
def IsSurv (wall : target.V) (o : G.SourceEdge) (x : Fin degree) : Prop :=
  ¬ IsDangling G o ∧ o.1.1 ∈ GluingDatum.incidentEdges wall ∧
    (G.vertexPartition wall).Rel x o.1.2

theorem IsSurv.congr {o : G.SourceEdge} {x y : Fin degree}
    (h : IsSurv wall o x) (hxy : (G.vertexPartition wall).Rel x y) : IsSurv wall o y :=
  ⟨h.1, h.2.1, hxy.symm.trans h.2.2⟩

theorem mem_ndI_G_iff (o : G.SourceEdge) (x : Fin degree) :
    o ∈ nonDanglingIncident G (G.sourceEndpoint wall x) ↔ IsSurv wall o x := by
  rw [mem_nonDanglingIncident, incident_iff_target_mem_and_rel]
  show (¬IsDangling G o ∧ o.1.1 ∈ GluingDatum.incidentEdges wall ∧
      (G.vertexPartition wall).Rel ((G.vertexPartition wall).repr x) o.1.2) ↔ _
  unfold IsSurv
  have : (G.vertexPartition wall).Rel ((G.vertexPartition wall).repr x) o.1.2 ↔
      (G.vertexPartition wall).Rel x o.1.2 :=
    ⟨fun h ↦ (SheetPartition.rel_repr_right _ x).trans h,
      fun h ↦ (SheetPartition.rel_repr_right _ x).symm.trans h⟩
  rw [this]

variable (C : BalancedGlobal.Candidate target degree G wall)

/-- The retaining side of the (star) resolution of the wall block of `x`. -/
noncomputable def ret (x : Fin degree) : Bool := by
  classical
  exact if (C.resolution ((G.vertexPartition wall).repr x)).left = G.vertexPartition wall
    then false else true

theorem ret_congr {x y : Fin degree} (h : (G.vertexPartition wall).Rel x y) :
    ret C x = ret C y := by
  unfold ret
  rw [show (G.vertexPartition wall).repr x = (G.vertexPartition wall).repr y from h]

theorem ret_rel {x : Fin degree}
    (hS : NonTrivalentValencyFourRows.IsStar (G.vertexPartition wall)
      (C.resolution ((G.vertexPartition wall).repr x))) (y : Fin degree) :
    (endPart C (ret C x)).Rel x y ↔ (G.vertexPartition wall).Rel x y := by
  classical
  rw [endPart_rel_iff]
  unfold ret
  by_cases hL : (C.resolution ((G.vertexPartition wall).repr x)).left = G.vertexPartition wall
  · rw [if_pos hL]
    simp only [Bool.false_eq_true, if_false]
    rw [hL]
  · rw [if_neg hL]
    simp only [if_true]
    rcases hS with ⟨hl, _⟩ | ⟨hr, _⟩
    · exact absurd hl hL
    · rw [hr]

theorem fine_rel {x : Fin degree}
    (hS : NonTrivalentValencyFourRows.IsStar (G.vertexPartition wall)
      (C.resolution ((G.vertexPartition wall).repr x))) (y : Fin degree) :
    (endPart C (!ret C x)).Rel x y ↔ (pasted C).newEdge.Rel x y := by
  classical
  rw [endPart_rel_iff, newPart_rel_iff]
  unfold ret
  by_cases hL : (C.resolution ((G.vertexPartition wall).repr x)).left = G.vertexPartition wall
  · rw [if_pos hL]
    simp only [Bool.not_false, if_true]
    rcases hS with ⟨_, hn⟩ | ⟨hr, hn⟩
    · rw [hn]
    · rw [hn, hL, hr]
  · rw [if_neg hL]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    rcases hS with ⟨hl, _⟩ | ⟨_, hn⟩
    · exact absurd hl hL
    · rw [hn]

theorem bool_eq_or_eq_not (b T : Bool) : b = T ∨ b = !T := by
  cases b <;> cases T <;> simp

theorem mem_pair_left {α : Type*} [DecidableEq α] (p q : α) : p ∈ ({p, q} : Finset α) :=
  Finset.mem_insert_self p _

theorem mem_pair_right {α : Type*} [DecidableEq α] (p q : α) : q ∈ ({p, q} : Finset α) :=
  Finset.mem_insert_of_mem (Finset.mem_singleton_self q)

/-- A survivor of the block of `x` assigned to the side `b`. -/
def SideSurv (x : Fin degree) (b : Bool) (o : G.SourceEdge) : Prop :=
  IsSurv wall o x ∧ C.right o.1.1 = b

/-- A survivor of the block of `x` on the fine side, in the new-edge class of `x`. -/
def FineSurv (x : Fin degree) (o : G.SourceEdge) : Prop :=
  SideSurv C x (!ret C x) o ∧ (pasted C).newEdge.Rel x o.1.2

theorem SideSurv.congr {x y : Fin degree} {b : Bool} {o : G.SourceEdge}
    (h : SideSurv C x b o) (hxy : (G.vertexPartition wall).Rel x y) : SideSurv C y b o :=
  ⟨h.1.congr hxy, h.2⟩

/-- **The hypotheses on the non-anchor wall blocks**, as the conjunction of its
fields.  `a` names the anchor block, the one block where nothing is
assumed.  At a non-anchor block the candidate's resolution is a star, the
datum is target-direction injective with surviving valency at most three, and
the side assignment puts at most two wall edges on each side. -/
structure StarHyp (a : Fin degree) : Prop where
  valid : G.Valid
  genus : genus C.datum.sourceGraph = genus G.sourceGraph
  star : ∀ x, ¬ (G.vertexPartition wall).Rel a x →
    NonTrivalentValencyFourRows.IsStar (G.vertexPartition wall)
      (C.resolution ((G.vertexPartition wall).repr x))
  inj : ∀ x, ¬ (G.vertexPartition wall).Rel a x → ∀ o₁ o₂ : G.SourceEdge,
    IsSurv wall o₁ x → IsSurv wall o₂ x → o₁.1.1 = o₂.1.1 → o₁ = o₂
  valency : ∀ x, ¬ (G.vertexPartition wall).Rel a x →
    nonDanglingValency G (G.sourceEndpoint wall x) ≤ 3
  side : ∀ (b : Bool) (e₁ e₂ e₃ : target.edges),
    e₁ ∈ GluingDatum.incidentEdges wall → e₂ ∈ GluingDatum.incidentEdges wall →
    e₃ ∈ GluingDatum.incidentEdges wall →
    C.right e₁ = b → C.right e₂ = b → C.right e₃ = b → e₁ = e₂ ∨ e₁ = e₃ ∨ e₂ = e₃

variable {C} {a : Fin degree} (S : StarHyp C a)

/-- The retained copy of a surviving occurrence of `G`. -/
noncomputable abbrev retE (o : G.SourceEdge) (h : ¬ IsDangling G o) :
    NonDanglingEdge C.datum :=
  ResolutionAwayFromWall.retainedEdge C S.valid.1 ⟨o, h⟩

theorem retE_val (o : G.SourceEdge) (h : ¬ IsDangling G o) :
    (retE S o h).1 = C.oldSourceEdge o := rfl

theorem not_rel_of_rel {x y : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hxy : (G.vertexPartition wall).Rel x y) : ¬ (G.vertexPartition wall).Rel a y :=
  fun h ↦ hx (h.trans hxy.symm)

/-! ### Counting survivors of `G` at a non-anchor block -/

include S in
theorem not_four {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    {o₁ o₂ o₃ o₄ : G.SourceEdge} (h₁ : IsSurv wall o₁ x) (h₂ : IsSurv wall o₂ x)
    (h₃ : IsSurv wall o₃ x) (h₄ : IsSurv wall o₄ x) (h12 : o₁ ≠ o₂) (h13 : o₁ ≠ o₃)
    (h14 : o₁ ≠ o₄) (h23 : o₂ ≠ o₃) (h24 : o₂ ≠ o₄) (h34 : o₃ ≠ o₄) : False := by
  have h := four_le_nd ((mem_ndI_G_iff o₁ x).mpr h₁) ((mem_ndI_G_iff o₂ x).mpr h₂)
    ((mem_ndI_G_iff o₃ x).mpr h₃) ((mem_ndI_G_iff o₄ x).mpr h₄) h12 h13 h14 h23 h24 h34
  have := S.valency x hx
  omega

include S in
theorem not_three_side {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x) {b : Bool}
    {o₁ o₂ o₃ : G.SourceEdge} (h₁ : SideSurv C x b o₁) (h₂ : SideSurv C x b o₂)
    (h₃ : SideSurv C x b o₃) (h12 : o₁ ≠ o₂) (h13 : o₁ ≠ o₃) (h23 : o₂ ≠ o₃) : False := by
  rcases S.side b _ _ _ h₁.1.2.1 h₂.1.2.1 h₃.1.2.1 h₁.2 h₂.2 h₃.2 with h | h | h
  · exact h12 (S.inj x hx _ _ h₁.1 h₂.1 h)
  · exact h13 (S.inj x hx _ _ h₁.1 h₃.1 h)
  · exact h23 (S.inj x hx _ _ h₂.1 h₃.1 h)

include S in
/-- Two distinct survivors that exhaust the survivors of their block are
consecutive in `G`. -/
theorem stablePath_eq_of_only_two {x : Fin degree} {o₁ o₂ : G.SourceEdge}
    (h₁ : IsSurv wall o₁ x) (h₂ : IsSurv wall o₂ x) (hne : o₁ ≠ o₂)
    (hOnly : ∀ o, IsSurv wall o x → o = o₁ ∨ o = o₂) :
    NonDanglingEdge.stablePath (⟨o₁, h₁.1⟩ : NonDanglingEdge G) =
      NonDanglingEdge.stablePath (⟨o₂, h₂.1⟩ : NonDanglingEdge G) := by
  classical
  apply stablePath_eq_of_consecutive
  refine consecutive_of_subset_pair S.valid.1 (v := G.sourceEndpoint wall x) _ _
    (fun h ↦ hne (congrArg Subtype.val h)) ?_
    ((mem_nonDanglingIncident _ _ _).mp ((mem_ndI_G_iff o₁ x).mpr h₁)).2
    ((mem_nonDanglingIncident _ _ _).mp ((mem_ndI_G_iff o₂ x).mpr h₂)).2
  intro z hz
  rcases hOnly z ((mem_ndI_G_iff z x).mp hz) with rfl | rfl <;> simp

/-! ### The surviving stars of the retaining and fine vertices -/

include S in
theorem mem_ndI_ret {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (f : C.datum.SourceEdge) :
    f ∈ nonDanglingIncident C.datum (epv C (ret C x) x) ↔
      (∃ o, SideSurv C x (ret C x) o ∧ f = C.oldSourceEdge o) ∨
      (∃ t, (G.vertexPartition wall).Rel x t ∧ ¬ IsDangling C.datum (C.newSourceEdge t) ∧
        f = C.newSourceEdge t) := by
  rw [mem_ndI_epv C S.valid S.genus]
  have hR := ret_rel C (S.star x hx)
  constructor
  · rintro (⟨o, hS, hAt, hSide, hRel, rfl⟩ | ⟨t, hRel, hS, rfl⟩)
    · exact Or.inl ⟨o, ⟨⟨hS, hAt, (hR _).mp hRel⟩, hSide⟩, rfl⟩
    · exact Or.inr ⟨t, (hR _).mp hRel, hS, rfl⟩
  · rintro (⟨o, ⟨⟨hS, hAt, hRel⟩, hSide⟩, rfl⟩ | ⟨t, hRel, hS, rfl⟩)
    · exact Or.inl ⟨o, hS, hAt, hSide, (hR _).mpr hRel, rfl⟩
    · exact Or.inr ⟨t, (hR _).mpr hRel, hS, rfl⟩

include S in
theorem mem_ndI_fine {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (f : C.datum.SourceEdge) :
    f ∈ nonDanglingIncident C.datum (epv C (!ret C x) x) ↔
      (∃ o, FineSurv C x o ∧ f = C.oldSourceEdge o) ∨
      (¬ IsDangling C.datum (C.newSourceEdge x) ∧ f = C.newSourceEdge x) := by
  rw [mem_ndI_epv C S.valid S.genus]
  have hF := fine_rel C (S.star x hx)
  constructor
  · rintro (⟨o, hS, hAt, hSide, hRel, rfl⟩ | ⟨t, hRel, hS, rfl⟩)
    · have hN := (hF _).mp hRel
      exact Or.inl ⟨o, ⟨⟨⟨hS, hAt, (newPart_refines C).rel hN⟩, hSide⟩, hN⟩, rfl⟩
    · have hEq : C.newSourceEdge x = C.newSourceEdge t :=
        (newSourceEdge_eq_iff C x t).mpr ((hF _).mp hRel)
      rw [← hEq] at hS ⊢
      exact Or.inr ⟨hS, rfl⟩
  · rintro (⟨o, ⟨⟨⟨hS, hAt, _⟩, hSide⟩, hN⟩, rfl⟩ | ⟨hS, rfl⟩)
    · exact Or.inl ⟨o, hS, hAt, hSide, (hF _).mpr hN, rfl⟩
    · exact Or.inr ⟨x, (hF _).mpr rfl, hS, rfl⟩

/-! ### Incidences at the two vertex kinds -/

include S in
theorem old_incident_ret {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    {o : G.SourceEdge} (ho : SideSurv C x (ret C x) o) :
    C.oldSourceEdge o ∈ nonDanglingIncident C.datum (epv C (ret C x) x) :=
  (mem_ndI_ret S hx _).mpr (Or.inl ⟨o, ho, rfl⟩)

include S in
theorem new_incident_ret {x t : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hxt : (G.vertexPartition wall).Rel x t) :
    Incident C.datum (C.newSourceEdge t) (epv C (ret C x) x) :=
  (newSourceEdge_incident_iff C _ t x).mpr ((ret_rel C (S.star x hx) t).mpr hxt)

include S in
theorem old_incident_fine {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    {o : G.SourceEdge} (ho : FineSurv C x o) :
    C.oldSourceEdge o ∈ nonDanglingIncident C.datum (epv C (!ret C x) x) :=
  (mem_ndI_fine S hx _).mpr (Or.inl ⟨o, ho, rfl⟩)

theorem FineSurv.of_sideSurv {x : Fin degree} {o : G.SourceEdge}
    (h : SideSurv C x (!ret C x) o) : FineSurv C o.1.2 o := by
  refine ⟨⟨h.1.congr h.1.2.2, ?_⟩, rfl⟩
  rw [h.2, ret_congr C h.1.2.2]

theorem FineSurv.sideSurv {x : Fin degree} {o : G.SourceEdge} (h : FineSurv C x o) :
    SideSurv C x (!ret C x) o := h.1

/-- Two fine-side survivors of one block lie in one new-edge class exactly when
their new occurrences coincide. -/
theorem fineSurv_iff {x t : Fin degree} (hxt : (G.vertexPartition wall).Rel x t)
    {o : G.SourceEdge} :
    FineSurv C t o ↔ SideSurv C x (!ret C x) o ∧ C.newSourceEdge t = C.newSourceEdge o.1.2 := by
  rw [newSourceEdge_eq_iff]
  unfold FineSurv
  rw [ret_congr C hxt]
  exact ⟨fun h ↦ ⟨SideSurv.congr C h.1 hxt.symm, h.2⟩, fun h ↦ ⟨SideSurv.congr C h.1 hxt, h.2⟩⟩

/-! ### The two engines -/

include S in
/-- A new occurrence whose class carries no fine-side survivor is dangling. -/
theorem dangling_of_no_fine {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hNo : ∀ o, ¬ FineSurv C x o) : IsDangling C.datum (C.newSourceEdge x) := by
  apply isDangling_of_subset_singleton (C.datum_valid S.valid).1
    (v := epv C (!ret C x) x)
  · intro f hf
    rcases (mem_ndI_fine S hx f).mp hf with ⟨o, ho, rfl⟩ | ⟨_, rfl⟩
    · exact absurd ho (hNo o)
    · exact Finset.mem_singleton_self _
  · exact newSourceEdge_incident C _ x

include S in
theorem exists_fine_of_survives {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hN : ¬ IsDangling C.datum (C.newSourceEdge x)) : ∃ o, FineSurv C x o := by
  by_contra hNo
  push Not at hNo
  exact hN (dangling_of_no_fine S hx hNo)

include S in
/-- A surviving new occurrence of the block of `x` is the new occurrence of the
class of some fine-side survivor of that block. -/
theorem new_eq_of_survives {x t : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hxt : (G.vertexPartition wall).Rel x t)
    (hN : ¬ IsDangling C.datum (C.newSourceEdge t)) :
    ∃ o, SideSurv C x (!ret C x) o ∧ C.newSourceEdge t = C.newSourceEdge o.1.2 := by
  obtain ⟨o, ho⟩ := exists_fine_of_survives S (not_rel_of_rel hx hxt) hN
  exact ⟨o, ((fineSurv_iff hxt).mp ho)⟩

include S in
/-- A new occurrence whose class carries exactly one fine-side survivor
survives, and is consecutive to that survivor at the fine vertex. -/
theorem fine_unique {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    {o : G.SourceEdge} (ho : FineSurv C x o) (hU : ∀ o', FineSurv C x o' → o' = o) :
    ∃ hN : ¬ IsDangling C.datum (C.newSourceEdge x),
      Consecutive C.datum ⟨C.newSourceEdge x, hN⟩ (retE S o ho.1.1.1) := by
  classical
  have hSub : nonDanglingIncident C.datum (epv C (!ret C x) x) ⊆
      {C.newSourceEdge x, C.oldSourceEdge o} := by
    intro f hf
    rcases (mem_ndI_fine S hx f).mp hf with ⟨o', ho', rfl⟩ | ⟨_, rfl⟩
    · rw [hU o' ho']
      simp
    · simp
  have hMemO := old_incident_fine S hx ho
  have hRes := survives_of_subset_pair (C.datum_valid S.valid).1 (new_ne_old C x o) hSub
    (newSourceEdge_incident C _ x) ((mem_nonDanglingIncident _ _ _).mp hMemO).1
    ((mem_nonDanglingIncident _ _ _).mp hMemO).2
  refine ⟨hRes.1, consecutive_of_subset_pair (C.datum_valid S.valid).1 _ _
    (fun h ↦ new_ne_old C x o (congrArg Subtype.val h)) hSub
    (newSourceEdge_incident C _ x) ((mem_nonDanglingIncident _ _ _).mp hMemO).2⟩

include S in
/-- At the retaining vertex: a retaining survivor and one new occurrence of the
block that together exhaust its surviving star are consecutive, and the new
occurrence survives. -/
theorem ret_pair {x t : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hxt : (G.vertexPartition wall).Rel x t) {o : G.SourceEdge}
    (ho : SideSurv C x (ret C x) o)
    (hSub : nonDanglingIncident C.datum (epv C (ret C x) x) ⊆
      {C.newSourceEdge t, C.oldSourceEdge o}) :
    ∃ hN : ¬ IsDangling C.datum (C.newSourceEdge t),
      Consecutive C.datum ⟨C.newSourceEdge t, hN⟩ (retE S o ho.1.1) := by
  have hMemO := old_incident_ret S hx ho
  have hRes := survives_of_subset_pair (C.datum_valid S.valid).1 (new_ne_old C t o) hSub
    (new_incident_ret S hx hxt) ((mem_nonDanglingIncident _ _ _).mp hMemO).1
    ((mem_nonDanglingIncident _ _ _).mp hMemO).2
  exact ⟨hRes.1, consecutive_of_subset_pair (C.datum_valid S.valid).1 _ _
    (fun h ↦ new_ne_old C t o (congrArg Subtype.val h)) hSub
    (new_incident_ret S hx hxt) ((mem_nonDanglingIncident _ _ _).mp hMemO).2⟩

/-! ### Descent and absorption -/

theorem side_absurd {b c : Bool} (h₁ : c = b) (h₂ : c = !b) : False := by
  subst h₁
  cases c <;> exact absurd h₂ (by decide)

theorem sideSurv_ne {x : Fin degree} {b : Bool} {o₁ o₂ : G.SourceEdge}
    (h₁ : SideSurv C x b o₁) (h₂ : SideSurv C x (!b) o₂) : o₁ ≠ o₂ := by
  rintro rfl
  exact side_absurd h₁.2 h₂.2

include S in
/-- **Descent, mixed case**: one survivor on each side.  The new occurrence of
the fine survivor's class survives and joins the two. -/
theorem descent_mixed {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    {o₁ o₂ : G.SourceEdge} (h₁ : SideSurv C x (ret C x) o₁) (h₂ : SideSurv C x (!ret C x) o₂)
    (hOnly : ∀ o, IsSurv wall o x → o = o₁ ∨ o = o₂) :
    (retE S o₁ h₁.1.1).stablePath = (retE S o₂ h₂.1.1).stablePath := by
  classical
  have hxt : (G.vertexPartition wall).Rel x o₂.1.2 := h₂.1.2.2
  have ht' := not_rel_of_rel hx hxt
  have hF : FineSurv C o₂.1.2 o₂ := FineSurv.of_sideSurv h₂
  have hU : ∀ o', FineSurv C o₂.1.2 o' → o' = o₂ := by
    intro o' ho'
    have hs := ((fineSurv_iff hxt).mp ho').1
    rcases hOnly o' hs.1 with h | h
    · rw [h] at hs
      exact (sideSurv_ne h₁ hs rfl).elim
    · exact h
  obtain ⟨hN, hCons⟩ := fine_unique S ht' hF hU
  have hSub : nonDanglingIncident C.datum (epv C (ret C x) x) ⊆
      {C.newSourceEdge o₂.1.2, C.oldSourceEdge o₁} := by
    intro f hf
    rcases (mem_ndI_ret S hx f).mp hf with ⟨o, ho, rfl⟩ | ⟨t', hxt', hN', rfl⟩
    · rcases hOnly o ho.1 with h | h
      · rw [h]; exact mem_pair_right _ _
      · rw [h] at ho
        exact (sideSurv_ne ho h₂ rfl).elim
    · obtain ⟨o, ho, hEq⟩ := new_eq_of_survives S hx hxt' hN'
      rcases hOnly o ho.1 with h | h
      · rw [h] at ho
        exact (sideSurv_ne h₁ ho rfl).elim
      · rw [hEq, h]; exact mem_pair_left _ _
  obtain ⟨hN2, hCons2⟩ := ret_pair S hx hxt h₁ hSub
  exact (stablePath_eq_of_consecutive hCons2).symm.trans (stablePath_eq_of_consecutive hCons)

include S in
/-- **Descent**: two survivors that exhaust the survivors of a non-anchor block
(so that they are consecutive in `G`) stay on one stable row of the candidate. -/
theorem descent {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    {o₁ o₂ : G.SourceEdge} (h₁ : IsSurv wall o₁ x) (h₂ : IsSurv wall o₂ x) (hne : o₁ ≠ o₂)
    (hOnly : ∀ o, IsSurv wall o x → o = o₁ ∨ o = o₂) :
    (retE S o₁ h₁.1).stablePath = (retE S o₂ h₂.1).stablePath := by
  classical
  have hConn := (C.datum_valid S.valid).1
  rcases bool_eq_or_eq_not (C.right o₁.1.1) (ret C x) with s₁ | s₁ <;>
    rcases bool_eq_or_eq_not (C.right o₂.1.1) (ret C x) with s₂ | s₂
  · -- both on the retaining side
    apply stablePath_eq_of_consecutive
    refine consecutive_of_subset_pair hConn (v := epv C (ret C x) x) _ _
      (fun h ↦ hne (ResolutionCut.oldSourceEdge_injective C (congrArg Subtype.val h))) ?_
      ((mem_nonDanglingIncident _ _ _).mp (old_incident_ret S hx ⟨h₁, s₁⟩)).2
      ((mem_nonDanglingIncident _ _ _).mp (old_incident_ret S hx ⟨h₂, s₂⟩)).2
    intro f hf
    rcases (mem_ndI_ret S hx f).mp hf with ⟨o, ho, rfl⟩ | ⟨t', hxt', hN', rfl⟩
    · rcases hOnly o ho.1 with h | h <;> rw [h]
      · exact mem_pair_left _ _
      · exact mem_pair_right _ _
    · obtain ⟨o, ho, -⟩ := new_eq_of_survives S hx hxt' hN'
      rcases hOnly o ho.1 with h | h
      · rw [h] at ho
        exact (sideSurv_ne ⟨h₁, s₁⟩ ho rfl).elim
      · rw [h] at ho
        exact (sideSurv_ne ⟨h₂, s₂⟩ ho rfl).elim
  · exact descent_mixed S hx ⟨h₁, s₁⟩ ⟨h₂, s₂⟩ hOnly
  · exact (descent_mixed S hx ⟨h₂, s₂⟩ ⟨h₁, s₁⟩
      (fun o ho ↦ (hOnly o ho).symm)).symm
  · -- both on the fine side
    have hOnlyFine : ∀ o, SideSurv C x (!ret C x) o → o = o₁ ∨ o = o₂ :=
      fun o ho ↦ hOnly o ho.1
    have hNoRet : ∀ o, ¬ SideSurv C x (ret C x) o := by
      intro o ho
      rcases hOnly o ho.1 with h | h
      · rw [h] at ho
        exact sideSurv_ne ho ⟨h₁, s₁⟩ rfl
      · rw [h] at ho
        exact sideSurv_ne ho ⟨h₂, s₂⟩ rfl
    have hx₁ : (G.vertexPartition wall).Rel x o₁.1.2 := h₁.2.2
    have hx₂ : (G.vertexPartition wall).Rel x o₂.1.2 := h₂.2.2
    by_cases hc : C.newSourceEdge o₁.1.2 = C.newSourceEdge o₂.1.2
    · -- one new-edge class: its new occurrence dangles, the survivors meet at
      -- the fine vertex
      have hF₁ : FineSurv C o₁.1.2 o₁ := FineSurv.of_sideSurv ⟨h₁, s₁⟩
      have hF₂ : FineSurv C o₁.1.2 o₂ := (fineSurv_iff hx₁).mpr ⟨⟨h₂, s₂⟩, hc⟩
      have ht₁ := not_rel_of_rel hx hx₁
      have hDang : IsDangling C.datum (C.newSourceEdge o₁.1.2) := by
        apply isDangling_of_subset_singleton hConn (v := epv C (ret C x) x) _
          (new_incident_ret S hx hx₁)
        intro f hf
        rcases (mem_ndI_ret S hx f).mp hf with ⟨o, ho, rfl⟩ | ⟨t', hxt', hN', rfl⟩
        · exact (hNoRet o ho).elim
        · obtain ⟨o, ho, hEq⟩ := new_eq_of_survives S hx hxt' hN'
          rcases hOnlyFine o ho with h | h <;> rw [hEq, h]
          · exact Finset.mem_singleton_self _
          · rw [hc]; exact Finset.mem_singleton_self _
      have hC₁ := (mem_nonDanglingIncident _ _ _).mp (old_incident_fine S ht₁ hF₁)
      have hC₂ := (mem_nonDanglingIncident _ _ _).mp (old_incident_fine S ht₁ hF₂)
      apply stablePath_eq_of_consecutive
      refine consecutive_of_subset_pair hConn (v := epv C (!ret C o₁.1.2) o₁.1.2) _ _
        (fun h ↦ hne (ResolutionCut.oldSourceEdge_injective C (congrArg Subtype.val h))) ?_
        hC₁.2 hC₂.2
      intro f hf
      rcases (mem_ndI_fine S ht₁ f).mp hf with ⟨o, ho, rfl⟩ | ⟨hS, rfl⟩
      · rcases hOnly o (ho.1.1.congr hx₁.symm) with h | h <;> rw [h]
        · exact mem_pair_left _ _
        · exact mem_pair_right _ _
      · exact (hS hDang).elim
    · -- two classes: both new occurrences survive and meet at the retaining vertex
      have hU₁ : ∀ o', FineSurv C o₁.1.2 o' → o' = o₁ := by
        intro o' ho'
        obtain ⟨hs, hEq⟩ := (fineSurv_iff hx₁).mp ho'
        rcases hOnlyFine o' hs with h | h
        · exact h
        · rw [h] at hEq
          exact (hc hEq).elim
      have hU₂ : ∀ o', FineSurv C o₂.1.2 o' → o' = o₂ := by
        intro o' ho'
        obtain ⟨hs, hEq⟩ := (fineSurv_iff hx₂).mp ho'
        rcases hOnlyFine o' hs with h | h
        · rw [h] at hEq
          exact (hc hEq.symm).elim
        · exact h
      obtain ⟨hN₁, hCons₁⟩ := fine_unique S (not_rel_of_rel hx hx₁)
        (FineSurv.of_sideSurv ⟨h₁, s₁⟩) hU₁
      obtain ⟨hN₂, hCons₂⟩ := fine_unique S (not_rel_of_rel hx hx₂)
        (FineSurv.of_sideSurv ⟨h₂, s₂⟩) hU₂
      have hMid : Consecutive C.datum ⟨C.newSourceEdge o₁.1.2, hN₁⟩
          ⟨C.newSourceEdge o₂.1.2, hN₂⟩ := by
        refine consecutive_of_subset_pair hConn (v := epv C (ret C x) x) _ _
          (fun h ↦ hc (congrArg Subtype.val h)) ?_
          (new_incident_ret S hx hx₁) (new_incident_ret S hx hx₂)
        intro f hf
        rcases (mem_ndI_ret S hx f).mp hf with ⟨o, ho, rfl⟩ | ⟨t', hxt', hN', rfl⟩
        · exact (hNoRet o ho).elim
        · obtain ⟨o, ho, hEq⟩ := new_eq_of_survives S hx hxt' hN'
          rcases hOnlyFine o ho with h | h <;> rw [hEq, h]
          · exact mem_pair_left _ _
          · exact mem_pair_right _ _
      exact ((stablePath_eq_of_consecutive hCons₁).symm.trans
        (stablePath_eq_of_consecutive hMid)).trans (stablePath_eq_of_consecutive hCons₂)

include S in
/-- **Absorption**: a surviving new occurrence of a non-anchor block lies on the
stable row of a retained survivor of that block. -/
theorem absorbed {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hN : ¬ IsDangling C.datum (C.newSourceEdge x)) :
    ∃ (o : G.SourceEdge) (h : ¬ IsDangling G o),
      NonDanglingEdge.stablePath (⟨C.newSourceEdge x, hN⟩ : NonDanglingEdge C.datum) =
        (retE S o h).stablePath := by
  classical
  have hConn := (C.datum_valid S.valid).1
  obtain ⟨o, ho⟩ := exists_fine_of_survives S hx hN
  by_cases hU : ∀ o', FineSurv C x o' → o' = o
  · obtain ⟨_, hCons⟩ := fine_unique S hx ho hU
    exact ⟨o, ho.1.1.1, stablePath_eq_of_consecutive hCons⟩
  push Not at hU
  obtain ⟨o', ho', hne⟩ := hU
  have hFineOnly : ∀ o'', SideSurv C x (!ret C x) o'' → o'' = o ∨ o'' = o' := by
    intro o'' h''
    by_contra hc
    push Not at hc
    exact not_three_side S hx ho.1 ho'.1 h'' (Ne.symm hne) (Ne.symm hc.1) (Ne.symm hc.2)
  have hxo : C.newSourceEdge x = C.newSourceEdge o.1.2 := (newSourceEdge_eq_iff C _ _).mpr ho.2
  have hxo' : C.newSourceEdge x = C.newSourceEdge o'.1.2 :=
    (newSourceEdge_eq_iff C _ _).mpr ho'.2
  have hNewOnly : ∀ t', (G.vertexPartition wall).Rel x t' →
      ¬ IsDangling C.datum (C.newSourceEdge t') → C.newSourceEdge t' = C.newSourceEdge x := by
    intro t' hxt' hN'
    obtain ⟨o'', h'', hEq⟩ := new_eq_of_survives S hx hxt' hN'
    rcases hFineOnly o'' h'' with h | h <;> rw [hEq, h]
    · exact hxo.symm
    · exact hxo'.symm
  by_cases hR : ∃ o₃, SideSurv C x (ret C x) o₃
  · obtain ⟨o₃, h₃⟩ := hR
    have hSub : nonDanglingIncident C.datum (epv C (ret C x) x) ⊆
        {C.newSourceEdge x, C.oldSourceEdge o₃} := by
      intro f hf
      rcases (mem_ndI_ret S hx f).mp hf with ⟨o₄, h₄, rfl⟩ | ⟨t', hxt', hN', rfl⟩
      · by_cases h43 : o₄ = o₃
        · rw [h43]; exact mem_pair_right _ _
        · exact (not_four S hx ho.1.1 ho'.1.1 h₃.1 h₄.1 (Ne.symm hne)
            (sideSurv_ne h₃ ho.1).symm (sideSurv_ne h₄ ho.1).symm
            (sideSurv_ne h₃ ho'.1).symm (sideSurv_ne h₄ ho'.1).symm (Ne.symm h43)).elim
      · rw [hNewOnly t' hxt' hN']; exact mem_pair_left _ _
    obtain ⟨_, hCons⟩ := ret_pair S hx rfl h₃ hSub
    exact ⟨o₃, h₃.1.1, stablePath_eq_of_consecutive hCons⟩
  · exfalso
    push Not at hR
    apply hN
    apply isDangling_of_subset_singleton hConn (v := epv C (ret C x) x) _
      (new_incident_ret S hx rfl)
    intro f hf
    rcases (mem_ndI_ret S hx f).mp hf with ⟨o₄, h₄, rfl⟩ | ⟨t', hxt', hN', rfl⟩
    · exact (hR o₄ h₄).elim
    · rw [hNewOnly t' hxt' hN']; exact Finset.mem_singleton_self _

/-! ### The reverse row assignment of a new occurrence -/

theorem mem_pair_of_nd_two {tgt : CFGraph} {D : GluingDatum tgt degree} {v : D.SourceVertex}
    (hVal : nonDanglingValency D v = 2) {p q : D.SourceEdge} (hpq : p ≠ q)
    (hp : p ∈ nonDanglingIncident D v) (hq : q ∈ nonDanglingIncident D v)
    {r : D.SourceEdge} (hr : r ∈ nonDanglingIncident D v) : r = p ∨ r = q := by
  classical
  have hSub : ({p, q} : Finset D.SourceEdge) ⊆ nonDanglingIncident D v := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hp
    · rw [Finset.mem_singleton.mp hz]; exact hq
  have hEq := Finset.eq_of_subset_of_card_le hSub (by
    rw [card_nonDanglingIncident, hVal, Finset.card_insert_of_notMem (by simpa using hpq),
      Finset.card_singleton])
  rw [← hEq] at hr
  rcases Finset.mem_insert.mp hr with h | h
  · exact Or.inl h
  · exact Or.inr (Finset.mem_singleton.mp h)

variable (C) in
/-- The wall row a surviving new occurrence of the block of `x` is absorbed
into: the row of the unique fine-side survivor of its class when there is one,
and otherwise the row of the unique retaining-side survivor of the block. -/
noncomputable def newRow (x : Fin degree) : Option (StablePath G) :=
  NonTrivalentValencyFourRetainedInjective.pickWith
    (fun o : NonDanglingEdge G ↦ o.stablePath)
    (fun o ↦ FineSurv C x o.1) (fun o ↦ SideSurv C x (ret C x) o.1)

theorem newRow_fine {x : Fin degree} {o : G.SourceEdge} (ho : FineSurv C x o)
    (hU : ∀ o', FineSurv C x o' → o' = o) :
    newRow C x = some (NonDanglingEdge.stablePath ⟨o, ho.1.1.1⟩) := by
  unfold newRow
  exact NonTrivalentValencyFourRetainedInjective.pickWith_left
    (fun o : NonDanglingEdge G ↦ o.stablePath) _ _
    (a := (⟨o, ho.1.1.1⟩ : NonDanglingEdge G)) ho (fun b hb ↦ Subtype.ext (hU b.1 hb))

theorem newRow_ret {x : Fin degree} {o : G.SourceEdge} (ho : SideSurv C x (ret C x) o)
    (hU : ∀ o', SideSurv C x (ret C x) o' → o' = o) {o₁ o₂ : G.SourceEdge}
    (h₁ : FineSurv C x o₁) (h₂ : FineSurv C x o₂) (h12 : o₁ ≠ o₂) :
    newRow C x = some (NonDanglingEdge.stablePath ⟨o, ho.1.1⟩) := by
  unfold newRow
  refine NonTrivalentValencyFourRetainedInjective.pickWith_right
    (fun o : NonDanglingEdge G ↦ o.stablePath) _ _ ?_
    (a := (⟨o, ho.1.1⟩ : NonDanglingEdge G)) ho (fun b hb ↦ Subtype.ext (hU b.1 hb))
  rintro ⟨c, -, hc⟩
  have e₁ := hc ⟨o₁, h₁.1.1.1⟩ h₁
  have e₂ := hc ⟨o₂, h₂.1.1.1⟩ h₂
  exact h12 (congrArg Subtype.val (e₁.trans e₂.symm))

theorem newRow_congr {x y : Fin degree} (h : (pasted C).newEdge.Rel x y) :
    newRow C x = newRow C y := by
  have hP : (G.vertexPartition wall).Rel x y := (newPart_refines C).rel h
  have hF : (fun o : NonDanglingEdge G ↦ FineSurv C x o.1) =
      (fun o ↦ FineSurv C y o.1) := by
    funext o
    apply propext
    unfold FineSurv
    rw [ret_congr C hP]
    exact ⟨fun k ↦ ⟨SideSurv.congr C k.1 hP, h.symm.trans k.2⟩,
      fun k ↦ ⟨SideSurv.congr C k.1 hP.symm, h.trans k.2⟩⟩
  have hR : (fun o : NonDanglingEdge G ↦ SideSurv C x (ret C x) o.1) =
      (fun o ↦ SideSurv C y (ret C y) o.1) := by
    funext o
    apply propext
    rw [ret_congr C hP]
    exact ⟨fun k ↦ SideSurv.congr C k hP, fun k ↦ SideSurv.congr C k hP.symm⟩
  unfold newRow
  rw [hF, hR]

/-! ### The census at a divalent vertex above a non-anchor block -/

include S in
/-- At a divalent retaining vertex carrying two retaining survivors, those two
are the only survivors of the block. -/
theorem ret_old_old {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hVal : nonDanglingValency C.datum (epv C (ret C x) x) = 2)
    {o₁ o₂ : G.SourceEdge} (h₁ : SideSurv C x (ret C x) o₁) (h₂ : SideSurv C x (ret C x) o₂)
    (hne : o₁ ≠ o₂) : ∀ o, IsSurv wall o x → o = o₁ ∨ o = o₂ := by
  classical
  have hm₁ := old_incident_ret S hx h₁
  have hm₂ := old_incident_ret S hx h₂
  have hne' : C.oldSourceEdge o₁ ≠ C.oldSourceEdge o₂ :=
    fun h ↦ hne (ResolutionCut.oldSourceEdge_injective C h)
  intro o ho
  rcases bool_eq_or_eq_not (C.right o.1.1) (ret C x) with s | s
  · rcases mem_pair_of_nd_two hVal hne' hm₁ hm₂ (old_incident_ret S hx ⟨ho, s⟩) with h | h
    · exact Or.inl (ResolutionCut.oldSourceEdge_injective C h)
    · exact Or.inr (ResolutionCut.oldSourceEdge_injective C h)
  · exfalso
    have hxo : (G.vertexPartition wall).Rel x o.1.2 := ho.2.2
    have hF : FineSurv C o.1.2 o := FineSurv.of_sideSurv ⟨ho, s⟩
    by_cases hU : ∀ o', FineSurv C o.1.2 o' → o' = o
    · obtain ⟨hN, -⟩ := fine_unique S (not_rel_of_rel hx hxo) hF hU
      have hmN : C.newSourceEdge o.1.2 ∈ nonDanglingIncident C.datum (epv C (ret C x) x) :=
        (mem_nonDanglingIncident _ _ _).mpr ⟨hN, new_incident_ret S hx hxo⟩
      rcases mem_pair_of_nd_two hVal hne' hm₁ hm₂ hmN with h | h
      · exact new_ne_old C _ _ h
      · exact new_ne_old C _ _ h
    · push Not at hU
      obtain ⟨o', ho', hne''⟩ := hU
      have hs' := ((fineSurv_iff hxo).mp ho').1
      exact not_four S hx h₁.1 h₂.1 ho hs'.1 hne (sideSurv_ne h₁ ⟨ho, s⟩)
          (sideSurv_ne h₁ hs') (sideSurv_ne h₂ ⟨ho, s⟩) (sideSurv_ne h₂ hs') (Ne.symm hne'')

theorem sideSurv_congr_iff {x y : Fin degree} (h : (G.vertexPartition wall).Rel x y)
    (b : Bool) (o : G.SourceEdge) : SideSurv C x b o ↔ SideSurv C y b o :=
  ⟨fun k ↦ SideSurv.congr C k h, fun k ↦ SideSurv.congr C k h.symm⟩

theorem newSourceEdge_eq_of_fineSurv {x : Fin degree} {o : G.SourceEdge}
    (h : FineSurv C x o) : C.newSourceEdge x = C.newSourceEdge o.1.2 :=
  (newSourceEdge_eq_iff C _ _).mpr h.2

include S in
/-- A divalent retaining vertex carrying a retaining survivor and a surviving
new occurrence: that new occurrence is absorbed into the survivor's row. -/
theorem ret_old_new {x t : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hVal : nonDanglingValency C.datum (epv C (ret C x) x) = 2)
    {o₁ : G.SourceEdge} (h₁ : SideSurv C x (ret C x) o₁)
    (hxt : (G.vertexPartition wall).Rel x t) (hN : ¬ IsDangling C.datum (C.newSourceEdge t)) :
    newRow C t = some (NonDanglingEdge.stablePath ⟨o₁, h₁.1.1⟩) := by
  classical
  have hm₁ := old_incident_ret S hx h₁
  have hmN : C.newSourceEdge t ∈ nonDanglingIncident C.datum (epv C (ret C x) x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hN, new_incident_ret S hx hxt⟩
  have hne' : C.oldSourceEdge o₁ ≠ C.newSourceEdge t := (new_ne_old C t o₁).symm
  have pairR := fun {f} (hf : f ∈ nonDanglingIncident C.datum (epv C (ret C x) x)) ↦
    mem_pair_of_nd_two hVal hne' hm₁ hmN hf
  have retOnly : ∀ o, SideSurv C x (ret C x) o → o = o₁ := by
    intro o ho
    rcases pairR (old_incident_ret S hx ho) with h | h
    · exact ResolutionCut.oldSourceEdge_injective C h
    · exact (new_ne_old C t o h.symm).elim
  have ht := not_rel_of_rel hx hxt
  obtain ⟨o', ho'⟩ := exists_fine_of_survives S ht hN
  have hs' := ((fineSurv_iff hxt).mp ho').1
  by_cases hU : ∀ o'', FineSurv C t o'' → o'' = o'
  · rw [newRow_fine ho' hU]
    refine congrArg some (stablePath_eq_of_only_two S h₁.1 hs'.1
      (sideSurv_ne h₁ hs') (fun o ho ↦ ?_)).symm
    rcases bool_eq_or_eq_not (C.right o.1.1) (ret C x) with s | s
    · exact Or.inl (retOnly o ⟨ho, s⟩)
    · right
      by_cases hc : C.newSourceEdge o.1.2 = C.newSourceEdge t
      · exact hU o ((fineSurv_iff hxt).mpr ⟨⟨ho, s⟩, hc.symm⟩)
      · exfalso
        have hxo : (G.vertexPartition wall).Rel x o.1.2 := ho.2.2
        have hF : FineSurv C o.1.2 o := FineSurv.of_sideSurv ⟨ho, s⟩
        by_cases hU' : ∀ o'', FineSurv C o.1.2 o'' → o'' = o
        · obtain ⟨hN', -⟩ := fine_unique S (not_rel_of_rel hx hxo) hF hU'
          rcases pairR ((mem_nonDanglingIncident _ _ _).mpr ⟨hN', new_incident_ret S hx hxo⟩)
            with h | h
          · exact new_ne_old C _ _ h
          · exact hc h
        · push Not at hU'
          obtain ⟨o'', ho'', hne''⟩ := hU'
          have hs'' := ((fineSurv_iff hxo).mp ho'').1
          have hEqT := newSourceEdge_eq_of_fineSurv ho'
          have hEq'' := ((fineSurv_iff hxo).mp ho'').2
          refine not_three_side S hx hs' ⟨ho, s⟩ hs'' ?_ ?_ (Ne.symm hne'')
          · rintro rfl
            exact hc hEqT.symm
          · rintro rfl
            exact hc (hEq''.trans hEqT.symm)
  · push Not at hU
    obtain ⟨o'', ho'', hne''⟩ := hU
    have h₁t : SideSurv C t (ret C t) o₁ := by
      rw [← ret_congr C hxt]; exact SideSurv.congr C h₁ hxt
    have retOnly' : ∀ o, SideSurv C t (ret C t) o → o = o₁ := by
      intro o ho
      rw [← ret_congr C hxt] at ho
      exact retOnly o (SideSurv.congr C ho hxt.symm)
    exact newRow_ret h₁t retOnly' ho'' ho' hne''

include S in
/-- A divalent retaining vertex carrying two surviving new occurrences: they are
absorbed into two rows, which coincide. -/
theorem ret_new_new {x t₁ t₂ : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hVal : nonDanglingValency C.datum (epv C (ret C x) x) = 2)
    (hxt₁ : (G.vertexPartition wall).Rel x t₁) (hxt₂ : (G.vertexPartition wall).Rel x t₂)
    (hN₁ : ¬ IsDangling C.datum (C.newSourceEdge t₁))
    (hN₂ : ¬ IsDangling C.datum (C.newSourceEdge t₂))
    (hne : C.newSourceEdge t₁ ≠ C.newSourceEdge t₂) : newRow C t₁ = newRow C t₂ := by
  classical
  have hm₁ : C.newSourceEdge t₁ ∈ nonDanglingIncident C.datum (epv C (ret C x) x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hN₁, new_incident_ret S hx hxt₁⟩
  have hm₂ : C.newSourceEdge t₂ ∈ nonDanglingIncident C.datum (epv C (ret C x) x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hN₂, new_incident_ret S hx hxt₂⟩
  have noRet : ∀ o, ¬ SideSurv C x (ret C x) o := by
    intro o ho
    rcases mem_pair_of_nd_two hVal hne hm₁ hm₂ (old_incident_ret S hx ho) with h | h
    · exact new_ne_old C _ _ h.symm
    · exact new_ne_old C _ _ h.symm
  obtain ⟨o₁, ho₁⟩ := exists_fine_of_survives S (not_rel_of_rel hx hxt₁) hN₁
  obtain ⟨o₂, ho₂⟩ := exists_fine_of_survives S (not_rel_of_rel hx hxt₂) hN₂
  have hs₁ := ((fineSurv_iff hxt₁).mp ho₁)
  have hs₂ := ((fineSurv_iff hxt₂).mp ho₂)
  have h12 : o₁ ≠ o₂ := by
    rintro rfl
    exact hne (hs₁.2.trans hs₂.2.symm)
  have fineOnly : ∀ o, SideSurv C x (!ret C x) o → o = o₁ ∨ o = o₂ := by
    intro o ho
    by_contra hc
    push Not at hc
    exact not_three_side S hx hs₁.1 hs₂.1 ho h12 (Ne.symm hc.1) (Ne.symm hc.2)
  have hU₁ : ∀ o, FineSurv C t₁ o → o = o₁ := by
    intro o ho
    obtain ⟨hs, hEq⟩ := (fineSurv_iff hxt₁).mp ho
    rcases fineOnly o hs with h | h
    · exact h
    · rw [h] at hEq
      exact (hne (hEq.trans hs₂.2.symm)).elim
  have hU₂ : ∀ o, FineSurv C t₂ o → o = o₂ := by
    intro o ho
    obtain ⟨hs, hEq⟩ := (fineSurv_iff hxt₂).mp ho
    rcases fineOnly o hs with h | h
    · rw [h] at hEq
      exact (hne (hs₁.2.trans hEq.symm)).elim
    · exact h
  rw [newRow_fine ho₁ hU₁, newRow_fine ho₂ hU₂]
  refine congrArg some (stablePath_eq_of_only_two S hs₁.1.1 hs₂.1.1 h12 (fun o ho ↦ ?_))
  rcases bool_eq_or_eq_not (C.right o.1.1) (ret C x) with s | s
  · exact (noRet o ⟨ho, s⟩).elim
  · exact fineOnly o ⟨ho, s⟩

include S in
/-- A divalent fine vertex carrying two fine survivors: they are the only
survivors of the block. -/
theorem fine_old_old {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hVal : nonDanglingValency C.datum (epv C (!ret C x) x) = 2)
    {o₁ o₂ : G.SourceEdge} (h₁ : FineSurv C x o₁) (h₂ : FineSurv C x o₂) (hne : o₁ ≠ o₂) :
    ∀ o, IsSurv wall o x → o = o₁ ∨ o = o₂ := by
  classical
  have hm₁ := old_incident_fine S hx h₁
  have hm₂ := old_incident_fine S hx h₂
  have hne' : C.oldSourceEdge o₁ ≠ C.oldSourceEdge o₂ :=
    fun h ↦ hne (ResolutionCut.oldSourceEdge_injective C h)
  have hDang : IsDangling C.datum (C.newSourceEdge x) := by
    by_contra hN
    rcases mem_pair_of_nd_two hVal hne' hm₁ hm₂
      ((mem_nonDanglingIncident _ _ _).mpr ⟨hN, newSourceEdge_incident C _ x⟩) with h | h
    · exact new_ne_old C _ _ h
    · exact new_ne_old C _ _ h
  have fineOnly : ∀ o, SideSurv C x (!ret C x) o → o = o₁ ∨ o = o₂ := by
    intro o ho
    by_contra hc
    push Not at hc
    exact not_three_side S hx h₁.1 h₂.1 ho hne (Ne.symm hc.1) (Ne.symm hc.2)
  intro o ho
  rcases bool_eq_or_eq_not (C.right o.1.1) (ret C x) with s | s
  · exfalso
    have hSub : nonDanglingIncident C.datum (epv C (ret C x) x) ⊆
        {C.newSourceEdge x, C.oldSourceEdge o} := by
      intro f hf
      rcases (mem_ndI_ret S hx f).mp hf with ⟨o₄, h₄, rfl⟩ | ⟨t', hxt', hN', rfl⟩
      · by_cases h4 : o₄ = o
        · rw [h4]; exact mem_pair_right _ _
        · exact (not_four S hx h₁.1.1 h₂.1.1 ho h₄.1 hne (sideSurv_ne ⟨ho, s⟩ h₁.1).symm
            (sideSurv_ne h₄ h₁.1).symm (sideSurv_ne ⟨ho, s⟩ h₂.1).symm
            (sideSurv_ne h₄ h₂.1).symm (Ne.symm h4)).elim
      · obtain ⟨o'', h'', hEq⟩ := new_eq_of_survives S hx hxt' hN'
        rcases fineOnly o'' h'' with h | h <;> rw [hEq, h]
        · rw [← newSourceEdge_eq_of_fineSurv h₁]; exact mem_pair_left _ _
        · rw [← newSourceEdge_eq_of_fineSurv h₂]; exact mem_pair_left _ _
    exact (ret_pair S hx rfl ⟨ho, s⟩ hSub).1 hDang
  · exact fineOnly o ⟨ho, s⟩

include S in
/-- A divalent fine vertex carrying a fine survivor and the surviving new
occurrence of its class: the new occurrence is absorbed into that row. -/
theorem fine_old_new {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (hVal : nonDanglingValency C.datum (epv C (!ret C x) x) = 2)
    {o : G.SourceEdge} (h : FineSurv C x o) (hN : ¬ IsDangling C.datum (C.newSourceEdge x)) :
    newRow C x = some (NonDanglingEdge.stablePath ⟨o, h.1.1.1⟩) := by
  have hm := old_incident_fine S hx h
  have hmN : C.newSourceEdge x ∈ nonDanglingIncident C.datum (epv C (!ret C x) x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨hN, newSourceEdge_incident C _ x⟩
  refine newRow_fine h (fun o' ho' ↦ ?_)
  rcases mem_pair_of_nd_two hVal (new_ne_old C x o).symm hm hmN (old_incident_fine S hx ho')
    with k | k
  · exact ResolutionCut.oldSourceEdge_injective C k
  · exact (new_ne_old C _ _ k.symm).elim

end DraismaVargas.Count.GeneralKRowStar
