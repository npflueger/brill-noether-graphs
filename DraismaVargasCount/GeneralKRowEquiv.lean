module

public import DraismaVargasCount.GeneralKRowStar

@[expose] public section

/-!
# The row equivalence of a wall resolution with one non-star block

Vargas, Part II, the labelling conventions of the combinatorial setup for a change of
combinatorial type (`subsec-setup-determinants`), as used in the proof of
`lm:change-comb-type`: "aside from `h_1^(q)` the edges of `H^(q)` correspond
bijectively to those of `H_0`". This is part of the valency-four limits of general `K`
(case `{v4-nd4}`, `subsec-case-v4`), which feed the type changes at merged-vertex valency
four (step 3 of `Assembly`).

Let `C` be a globally assembled candidate over a valid datum `G`, genus
preserving, whose resolution is a star at every wall block except one, the
*anchor* block of the sheet `a` (`GeneralKRowStar.StarHyp`).  At the anchor we
assume (`AnchorHyp`):

* no source vertex of `C` above the anchor block is divalent;
* every surviving new occurrence above the anchor is the one of a sheet
  `bridge`, which survives;
* the anchor vertex of `G` is not divalent.

Then the stable rows of `C` are the stable rows of `G` together with the one
row of the bridge:

* `rowEquiv : StablePath C.datum ≃ Option (StablePath G)`, with
  `rowEquiv_retainedRow` (a retained row goes to its wall row) and
  `rowEquiv_bridgeRow` (the bridge row goes to `none`);
* `occurrences_retainedRow_old` / `matrix_retainedRow_old`: over an old target
  edge a retained row has exactly the retained copies of the wall row's
  occurrences, hence the same natural matrix entry;
* `matrix_bridgeRow_old` (zero) and `matrix_bridgeRow_new_pos` (positive): the
  bridge row lives on the new target edge only.

The proof is the inverse `Quot.lift` of the `K = 0` argument
`NonTrivalentValencyFourRetainedInjective`: `rowOfEdge` sends a retained
occurrence to its wall row, a new occurrence above the anchor to `none` and a
new occurrence of a star block to `GeneralKRowStar.newRow`; it is constant on
consecutive pairs (`rowOfEdge_eq_of_consecutive`), by the census of
`GeneralKRowStar` at star blocks and by `AnchorHyp` at the anchor.

## What is NOT proved here

The hypotheses `StarHyp` and `AnchorHyp` themselves.  For the general-`K`
candidate `GeneralKExitSetup.candK` they are discharged in `GeneralKRowsK`
(`starHyp`, `anchorHyp`).
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKRowEquiv

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.GeneralKRowCore
open DraismaVargas.Count.GeneralKRowStar

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {G : GluingDatum target degree}

variable (C : BalancedGlobal.Candidate target degree G wall)

/-- **The hypotheses at the anchor block** (interface: the conjunction of its
fields). -/
structure AnchorHyp (a bridge : Fin degree) : Prop where
  bridge_rel : (G.vertexPartition wall).Rel a bridge
  nd_ne_two : ∀ (b : Bool) (s : Fin degree), (G.vertexPartition wall).Rel a s →
    nonDanglingValency C.datum (epv C b s) ≠ 2
  new_eq : ∀ s, (G.vertexPartition wall).Rel a s →
    ¬ IsDangling C.datum (C.newSourceEdge s) → C.newSourceEdge s = C.newSourceEdge bridge
  bridge_survives : ¬ IsDangling C.datum (C.newSourceEdge bridge)
  nd_anchor : nonDanglingValency G (G.sourceEndpoint wall a) ≠ 2

variable {C} {a : Fin degree} (S : StarHyp C a)

/-! ## 1.  The reverse row assignment on surviving occurrences -/

/-- A retained occurrence goes to its wall row; a new occurrence above the
anchor to `none`; a new occurrence of a star block to `newRow`. -/
noncomputable def rowOfEdge (e : NonDanglingEdge C.datum) : Option (StablePath G) := by
  classical
  exact if h : ∃ o : NonDanglingEdge G, retE S o.1 o.2 = e then
      some (Classical.choose h).stablePath
    else if (G.vertexPartition wall).Rel a e.1.1.2 then none else newRow C e.1.1.2

theorem rowOfEdge_retE (o : G.SourceEdge) (h : ¬ IsDangling G o) :
    rowOfEdge S (retE S o h) = some (NonDanglingEdge.stablePath ⟨o, h⟩) := by
  classical
  have hOld : ∃ o' : NonDanglingEdge G, retE S o'.1 o'.2 = retE S o h := ⟨⟨o, h⟩, rfl⟩
  rw [rowOfEdge, dite_eq_left hOld]
  have hEq : Classical.choose hOld = ⟨o, h⟩ :=
    ResolutionAwayFromWall.retainedEdge_injective C S.valid.1 (Classical.choose_spec hOld)
  rw [hEq]

theorem not_retained_new {s : Fin degree} (hs : ¬ IsDangling C.datum (C.newSourceEdge s)) :
    ¬ ∃ o : NonDanglingEdge G, retE S o.1 o.2 = ⟨C.newSourceEdge s, hs⟩ := by
  rintro ⟨o, hEq⟩
  exact new_ne_old C s o.1 (congrArg Subtype.val hEq).symm

theorem rowOfEdge_new_anchor {s : Fin degree} (hs : ¬ IsDangling C.datum (C.newSourceEdge s))
    (hA : (G.vertexPartition wall).Rel a s) : rowOfEdge S ⟨C.newSourceEdge s, hs⟩ = none := by
  classical
  unfold rowOfEdge
  rw [dite_eq_right (not_retained_new S hs)]
  have hRel : (G.vertexPartition wall).Rel a (C.newSourceEdge s).1.2 := by
    rw [BalancedGlobal.Candidate.newSourceEdge_sheet]
    exact hA.trans ((newPart_refines C).rel (SheetPartition.rel_repr_right _ s))
  rw [ite_eq_left hRel]

theorem rowOfEdge_new {s : Fin degree} (hs : ¬ IsDangling C.datum (C.newSourceEdge s))
    (hA : ¬ (G.vertexPartition wall).Rel a s) :
    rowOfEdge S ⟨C.newSourceEdge s, hs⟩ = newRow C s := by
  classical
  unfold rowOfEdge
  rw [dite_eq_right (not_retained_new S hs)]
  have hNw : (pasted C).newEdge.Rel s (C.newSourceEdge s).1.2 := by
    rw [BalancedGlobal.Candidate.newSourceEdge_sheet]
    exact SheetPartition.rel_repr_right _ s
  have hRel : ¬ (G.vertexPartition wall).Rel a (C.newSourceEdge s).1.2 :=
    fun h ↦ hA (h.trans ((newPart_refines C).rel hNw).symm)
  rw [ite_eq_right hRel]
  exact (newRow_congr hNw).symm

/-- Every surviving occurrence is retained or new. -/
theorem nde_cases (e : NonDanglingEdge C.datum) :
    (∃ (o : G.SourceEdge) (h : ¬ IsDangling G o), e = retE S o h) ∨
      ∃ (s : Fin degree) (hs : ¬ IsDangling C.datum (C.newSourceEdge s)),
        e = ⟨C.newSourceEdge s, hs⟩ := by
  rcases ResolutionAwayFromWall.nonDanglingEdge_cases C S.valid S.genus e with
    ⟨o, rfl⟩ | ⟨s, hs, rfl⟩
  · exact Or.inl ⟨o.1, o.2, rfl⟩
  · exact Or.inr ⟨s, hs, rfl⟩

/-! ## 2.  Constancy on consecutive pairs -/

/-- Constancy at a divalent vertex above a star block. -/
theorem rowOfEdge_eq_star {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x) (b : Bool)
    (hVal : nonDanglingValency C.datum (epv C b x) = 2) {e f : NonDanglingEdge C.datum}
    (hne : e ≠ f) (he : Incident C.datum e.1 (epv C b x))
    (hf : Incident C.datum f.1 (epv C b x)) : rowOfEdge S e = rowOfEdge S f := by
  have he' : e.1 ∈ nonDanglingIncident C.datum (epv C b x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, he⟩
  have hf' : f.1 ∈ nonDanglingIncident C.datum (epv C b x) :=
    (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hf⟩
  rcases bool_eq_or_eq_not b (ret C x) with rfl | rfl
  · rcases (mem_ndI_ret S hx e.1).mp he' with ⟨o₁, h₁, he1⟩ | ⟨t₁, hxt₁, hN₁, he1⟩ <;>
      rcases (mem_ndI_ret S hx f.1).mp hf' with ⟨o₂, h₂, hf1⟩ | ⟨t₂, hxt₂, hN₂, hf1⟩
    · obtain rfl : e = retE S o₁ h₁.1.1 := Subtype.ext he1
      obtain rfl : f = retE S o₂ h₂.1.1 := Subtype.ext hf1
      have h12 : o₁ ≠ o₂ := fun h ↦ hne (by subst h; rfl)
      rw [rowOfEdge_retE, rowOfEdge_retE]
      exact congrArg some (stablePath_eq_of_only_two S h₁.1 h₂.1 h12
        (ret_old_old S hx hVal h₁ h₂ h12))
    · obtain rfl : e = retE S o₁ h₁.1.1 := Subtype.ext he1
      obtain rfl : f = ⟨C.newSourceEdge t₂, hN₂⟩ := Subtype.ext hf1
      rw [rowOfEdge_retE, rowOfEdge_new S hN₂ (not_rel_of_rel hx hxt₂),
        ret_old_new S hx hVal h₁ hxt₂ hN₂]
    · obtain rfl : e = ⟨C.newSourceEdge t₁, hN₁⟩ := Subtype.ext he1
      obtain rfl : f = retE S o₂ h₂.1.1 := Subtype.ext hf1
      rw [rowOfEdge_retE, rowOfEdge_new S hN₁ (not_rel_of_rel hx hxt₁),
        ret_old_new S hx hVal h₂ hxt₁ hN₁]
    · obtain rfl : e = ⟨C.newSourceEdge t₁, hN₁⟩ := Subtype.ext he1
      obtain rfl : f = ⟨C.newSourceEdge t₂, hN₂⟩ := Subtype.ext hf1
      rw [rowOfEdge_new S hN₁ (not_rel_of_rel hx hxt₁),
        rowOfEdge_new S hN₂ (not_rel_of_rel hx hxt₂)]
      exact ret_new_new S hx hVal hxt₁ hxt₂ hN₁ hN₂ (fun h ↦ hne (Subtype.ext h))
  · rcases (mem_ndI_fine S hx e.1).mp he' with ⟨o₁, h₁, he1⟩ | ⟨hN₁, he1⟩ <;>
      rcases (mem_ndI_fine S hx f.1).mp hf' with ⟨o₂, h₂, hf1⟩ | ⟨hN₂, hf1⟩
    · obtain rfl : e = retE S o₁ h₁.1.1.1 := Subtype.ext he1
      obtain rfl : f = retE S o₂ h₂.1.1.1 := Subtype.ext hf1
      have h12 : o₁ ≠ o₂ := fun h ↦ hne (by subst h; rfl)
      rw [rowOfEdge_retE, rowOfEdge_retE]
      exact congrArg some (stablePath_eq_of_only_two S h₁.1.1 h₂.1.1 h12
        (fine_old_old S hx hVal h₁ h₂ h12))
    · obtain rfl : e = retE S o₁ h₁.1.1.1 := Subtype.ext he1
      obtain rfl : f = ⟨C.newSourceEdge x, hN₂⟩ := Subtype.ext hf1
      rw [rowOfEdge_retE, rowOfEdge_new S hN₂ hx, fine_old_new S hx hVal h₁ hN₂]
    · obtain rfl : e = ⟨C.newSourceEdge x, hN₁⟩ := Subtype.ext he1
      obtain rfl : f = retE S o₂ h₂.1.1.1 := Subtype.ext hf1
      rw [rowOfEdge_retE, rowOfEdge_new S hN₁ hx, fine_old_new S hx hVal h₂ hN₁]
    · exact absurd (Subtype.ext (he1.trans hf1.symm)) hne

/-- Constancy away from the wall: both partners are retained, and consecutive
in `G`. -/
theorem rowOfEdge_eq_away (v : G.SourceVertex) (hAway : v.1.1 ≠ wall)
    {e f : NonDanglingEdge C.datum} (hne : e ≠ f)
    (he : Incident C.datum e.1 (ResolutionAwayFromWall.retainedVertex C v))
    (hf : Incident C.datum f.1 (ResolutionAwayFromWall.retainedVertex C v))
    (hVal : nonDanglingValency C.datum (ResolutionAwayFromWall.retainedVertex C v) = 2) :
    rowOfEdge S e = rowOfEdge S f := by
  rcases nde_cases S e with ⟨o₁, h₁, rfl⟩ | ⟨s, hs, rfl⟩
  · rcases nde_cases S f with ⟨o₂, h₂, rfl⟩ | ⟨s, hs, rfl⟩
    · rw [rowOfEdge_retE, rowOfEdge_retE]
      have h12 : (⟨o₁, h₁⟩ : NonDanglingEdge G) ≠ ⟨o₂, h₂⟩ := by
        intro h
        obtain rfl : o₁ = o₂ := congrArg Subtype.val h
        exact hne rfl
      refine congrArg some (stablePath_eq_of_consecutive ⟨h12, v, ?_, ?_, ?_⟩)
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff C v hAway o₁).mp he
      · exact (ResolutionAwayFromWall.incident_oldSourceEdge_iff C v hAway o₂).mp hf
      · exact (ResolutionAwayFromWall.nonDanglingValency_retainedVertex C S.valid S.genus v
          hAway).symm.trans hVal
    · exact absurd hf (ResolutionAwayFromWall.not_incident_newSourceEdge C v hAway s)
  · exact absurd he (ResolutionAwayFromWall.not_incident_newSourceEdge C v hAway s)

variable {bridge : Fin degree} (A : AnchorHyp C a bridge)

include A in
/-- **The reverse row assignment is constant on consecutive pairs.** -/
theorem rowOfEdge_eq_of_consecutive {e f : NonDanglingEdge C.datum}
    (h : Consecutive C.datum e f) : rowOfEdge S e = rowOfEdge S f := by
  obtain ⟨hne, v, he, hf, hVal⟩ := h
  rcases vertex_cases C v with ⟨old, hAway, rfl⟩ | ⟨b, hb⟩
  · exact rowOfEdge_eq_away S old hAway hne he hf hVal
  · rw [← hb] at he hf hVal
    by_cases hA : (G.vertexPartition wall).Rel a v.1.2
    · exact absurd hVal (A.nd_ne_two b _ hA)
    · exact rowOfEdge_eq_star S hA b hVal hne he hf

include A in
/-- **Descent**: consecutive occurrences of `G` stay on one stable row of `C`. -/
theorem retE_stablePath_eq {o₁ o₂ : NonDanglingEdge G} (h : Consecutive G o₁ o₂) :
    (retE S o₁.1 o₁.2).stablePath = (retE S o₂.1 o₂.2).stablePath := by
  obtain ⟨hne, v, h1, h2, hVal⟩ := h
  by_cases hAt : v.1.1 = wall
  · have hv : G.sourceEndpoint wall v.1.2 = v :=
      (GluingDatum.sourceEndpoint_eq_iff _ _ _ _).mpr ⟨hAt.symm, rfl⟩
    rw [← hv] at h1 h2 hVal
    by_cases hA : (G.vertexPartition wall).Rel a v.1.2
    · have hEq : G.sourceEndpoint wall a = G.sourceEndpoint wall v.1.2 := by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact hA
      exact absurd (hEq ▸ hVal) A.nd_anchor
    · have hm₁ : o₁.1 ∈ nonDanglingIncident G (G.sourceEndpoint wall v.1.2) :=
        (mem_nonDanglingIncident _ _ _).mpr ⟨o₁.2, h1⟩
      have hm₂ : o₂.1 ∈ nonDanglingIncident G (G.sourceEndpoint wall v.1.2) :=
        (mem_nonDanglingIncident _ _ _).mpr ⟨o₂.2, h2⟩
      have hne' : o₁.1 ≠ o₂.1 := fun h ↦ hne (Subtype.ext h)
      exact descent S hA ((mem_ndI_G_iff _ _).mp hm₁) ((mem_ndI_G_iff _ _).mp hm₂) hne'
        (fun o ho ↦ mem_pair_of_nd_two hVal hne' hm₁ hm₂ ((mem_ndI_G_iff _ _).mpr ho))
  · exact stablePath_eq_of_consecutive
      (ResolutionAwayFromWall.consecutive_retained_of_away C S.valid S.genus o₁ o₂ hne v hAt
        h1 h2 hVal)

/-! ## 3.  The row equivalence -/

/-- The retained-row map: every stable row of `G` descends to a stable row of `C`
along the literal retained occurrences. -/
noncomputable def retainedRow : StablePath G → StablePath C.datum :=
  Quot.lift (fun o : NonDanglingEdge G ↦ (retE S o.1 o.2).stablePath)
    (fun _ _ h ↦ retE_stablePath_eq S A h)

@[simp] theorem retainedRow_mk (o : NonDanglingEdge G) :
    retainedRow S A o.stablePath = (retE S o.1 o.2).stablePath := rfl

/-- The reverse map on stable rows. -/
noncomputable def rowDescend : StablePath C.datum → Option (StablePath G) :=
  Quot.lift (rowOfEdge S) (fun _ _ h ↦ rowOfEdge_eq_of_consecutive S A h)

/-- The one new stable row: the bridge occurrence. -/
noncomputable def bridgeRow : StablePath C.datum :=
  NonDanglingEdge.stablePath ⟨C.newSourceEdge bridge, A.bridge_survives⟩

theorem rowDescend_retainedRow (r : StablePath G) :
    rowDescend S A (retainedRow S A r) = some r := by
  induction r using Quot.inductionOn with
  | h o => exact rowOfEdge_retE S o.1 o.2

theorem rowDescend_bridgeRow : rowDescend S A (bridgeRow A) = none :=
  rowOfEdge_new_anchor S A.bridge_survives A.bridge_rel

/-- The inverse map: `none` is the bridge row, `some r` the retained row of `r`. -/
noncomputable def rowAscend (q : Option (StablePath G)) : StablePath C.datum :=
  q.elim (bridgeRow A) (retainedRow S A)

theorem rowDescend_rowAscend (q : Option (StablePath G)) :
    rowDescend S A (rowAscend S A q) = q := by
  cases q with
  | none => exact rowDescend_bridgeRow S A
  | some r => exact rowDescend_retainedRow S A r

/-- **Every stable row of `C` is retained or the bridge row.** -/
theorem rowAscend_surjective : Function.Surjective (rowAscend S A) := by
  intro p
  induction p using Quot.inductionOn with
  | h e =>
    rcases nde_cases S e with ⟨o, h, rfl⟩ | ⟨s, hs, rfl⟩
    · exact ⟨some (NonDanglingEdge.stablePath ⟨o, h⟩), rfl⟩
    · by_cases hA : (G.vertexPartition wall).Rel a s
      · refine ⟨none, ?_⟩
        show bridgeRow A = _
        unfold bridgeRow
        congr 1
        exact Subtype.ext (A.new_eq s hA hs).symm
      · obtain ⟨o, h, hEq⟩ := absorbed S hA hs
        exact ⟨some (NonDanglingEdge.stablePath ⟨o, h⟩), hEq.symm⟩

/-- **The row equivalence**: the stable rows of the candidate are the stable
rows of `G` together with the bridge row. -/
noncomputable def rowEquiv : StablePath C.datum ≃ Option (StablePath G) where
  toFun := rowDescend S A
  invFun := rowAscend S A
  left_inv := by
    intro p
    obtain ⟨q, rfl⟩ := rowAscend_surjective S A p
    rw [rowDescend_rowAscend]
  right_inv := rowDescend_rowAscend S A

@[simp] theorem rowEquiv_retainedRow (r : StablePath G) :
    rowEquiv S A (retainedRow S A r) = some r :=
  rowDescend_retainedRow S A r

@[simp] theorem rowEquiv_bridgeRow : rowEquiv S A (bridgeRow A) = none :=
  rowDescend_bridgeRow S A

@[simp] theorem rowEquiv_symm_some (r : StablePath G) :
    (rowEquiv S A).symm (some r) = retainedRow S A r := rfl

@[simp] theorem rowEquiv_symm_none : (rowEquiv S A).symm none = bridgeRow A := rfl

theorem rowEquiv_mk_retE (o : G.SourceEdge) (h : ¬ IsDangling G o) :
    rowEquiv S A (retE S o h).stablePath = some (NonDanglingEdge.stablePath ⟨o, h⟩) :=
  rowOfEdge_retE S o h

theorem retainedRow_injective : Function.Injective (retainedRow S A) := by
  intro r₁ r₂ h
  have h₁ := rowEquiv_retainedRow S A r₁
  rw [h, rowEquiv_retainedRow] at h₁
  exact (Option.some_injective _ h₁).symm

theorem retainedRow_ne_bridgeRow (r : StablePath G) : retainedRow S A r ≠ bridgeRow A := by
  intro h
  have h₁ := rowEquiv_retainedRow S A r
  rw [h, rowEquiv_bridgeRow] at h₁
  cases h₁

/-! ## 4.  Occurrences and the natural matrix -/

theorem old_of_target_some {e : C.datum.SourceEdge} {t : target.edges}
    (hT : e.1.1 = occurrenceEquiv target wall C.right (some t)) :
    ∃ o : G.SourceEdge, o.1.1 = t ∧ e = C.oldSourceEdge o := by
  rcases ResolutionPruning.sourceEdge_cases C e with ⟨o, rfl⟩ | ⟨s, rfl⟩
  · refine ⟨o, ?_, rfl⟩
    rw [BalancedGlobal.Candidate.oldSourceEdge_target] at hT
    exact Option.some_injective _ ((occurrenceEquiv target wall C.right).injective hT)
  · rw [BalancedGlobal.Candidate.newSourceEdge_target] at hT
    cases (occurrenceEquiv target wall C.right).injective hT

/-- Over an old target edge a retained row carries exactly the retained copies
of the wall row's occurrences. -/
theorem occurrences_retainedRow_old (r : StablePath G) (t : target.edges) :
    StableSourceMatrix.occurrences C.datum (retainedRow S A r)
        (occurrenceEquiv target wall C.right (some t)) =
      (StableSourceMatrix.occurrences G r t).image C.oldSourceEdge := by
  classical
  ext e
  rw [StableSourceMatrix.mem_occurrences, Finset.mem_image]
  constructor
  · rintro ⟨⟨hS, hRow⟩, hT⟩
    obtain ⟨o, rfl, rfl⟩ := old_of_target_some hT
    have hSo : ¬ IsDangling G o := fun h ↦ hS ((isDangling_old_iff C S.valid S.genus o).mpr h)
    have hRow' := congrArg (rowEquiv S A) hRow
    rw [rowEquiv_retainedRow] at hRow'
    have hMk : rowEquiv S A (NonDanglingEdge.stablePath ⟨C.oldSourceEdge o, hS⟩) =
        some (NonDanglingEdge.stablePath ⟨o, hSo⟩) := rowEquiv_mk_retE S A o hSo
    rw [hMk] at hRow'
    exact ⟨o, (StableSourceMatrix.mem_occurrences _ _ _).mpr
      ⟨⟨hSo, Option.some_injective _ hRow'⟩, rfl⟩, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    obtain ⟨⟨hSo, hRow⟩, hT⟩ := (StableSourceMatrix.mem_occurrences _ _ _).mp ho
    refine ⟨⟨fun h ↦ hSo ((isDangling_old_iff C S.valid S.genus o).mp h), ?_⟩, ?_⟩
    · rw [← hRow]
      rfl
    · rw [BalancedGlobal.Candidate.oldSourceEdge_target, hT]

/-- **The common minor, naturally**: a retained row has the wall row's entry in
every old column. -/
theorem matrix_retainedRow_old (r : StablePath G) (t : target.edges) :
    StableSourceMatrix.matrix C.datum (retainedRow S A r)
        (occurrenceEquiv target wall C.right (some t)) =
      StableSourceMatrix.matrix G r t := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_retainedRow_old S A, Finset.sum_image
    (fun _ _ _ _ h ↦ ResolutionCut.oldSourceEdge_injective C h)]
  exact Finset.sum_congr rfl fun o _ ↦ by
    rw [BalancedGlobal.Candidate.sourceEdgeIndex_oldSourceEdge]

include S in
theorem occurrences_bridgeRow_old (t : target.edges) :
    StableSourceMatrix.occurrences C.datum (bridgeRow A)
        (occurrenceEquiv target wall C.right (some t)) = ∅ := by
  classical
  refine Finset.eq_empty_iff_forall_notMem.mpr fun e he ↦ ?_
  obtain ⟨⟨hS, hRow⟩, hT⟩ := (StableSourceMatrix.mem_occurrences _ _ _).mp he
  obtain ⟨o, -, rfl⟩ := old_of_target_some hT
  have hSo : ¬ IsDangling G o := fun h ↦ hS ((isDangling_old_iff C S.valid S.genus o).mpr h)
  have hRow' := congrArg (rowEquiv S A) hRow
  rw [rowEquiv_bridgeRow] at hRow'
  have hMk : rowEquiv S A (NonDanglingEdge.stablePath ⟨C.oldSourceEdge o, hS⟩) =
      some (NonDanglingEdge.stablePath ⟨o, hSo⟩) := rowEquiv_mk_retE S A o hSo
  rw [hMk] at hRow'
  cases hRow'

include S in
/-- The bridge row vanishes on every old column. -/
theorem matrix_bridgeRow_old (t : target.edges) :
    StableSourceMatrix.matrix C.datum (bridgeRow A)
      (occurrenceEquiv target wall C.right (some t)) = 0 := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_old S A, Finset.sum_empty]

/-- The bridge row is positive on the new column. -/
theorem matrix_bridgeRow_new_pos :
    0 < StableSourceMatrix.matrix C.datum (bridgeRow A)
      (occurrenceEquiv target wall C.right none) := by
  classical
  unfold StableSourceMatrix.matrix
  refine Finset.sum_pos (fun e _ ↦ div_pos one_pos
    (by exact_mod_cast C.datum.sourceEdgeIndex_pos e)) ⟨C.newSourceEdge bridge, ?_⟩
  exact (StableSourceMatrix.mem_occurrences _ _ _).mpr ⟨⟨A.bridge_survives, rfl⟩, rfl⟩

include A in
/-- **The bridge is alone in its stable row**: both of its ends lie above the
anchor, where no vertex is divalent. -/
theorem eq_bridge_of_stablePath_eq (other : NonDanglingEdge C.datum)
    (h : other.stablePath = bridgeRow A) :
    other.1 = C.newSourceEdge bridge := by
  have hEnds := sourceEnds_newSourceEdge C bridge
  refine congrArg Subtype.val
    (NonTrivalentUniqueFourValent.eq_of_stablePath_eq_of_ends_ne_two
      ⟨C.newSourceEdge bridge, A.bridge_survives⟩ ?_ ?_ other h)
  · rw [congrArg Prod.fst hEnds]
    exact A.nd_ne_two false bridge A.bridge_rel
  · rw [congrArg Prod.snd hEnds]
    exact A.nd_ne_two true bridge A.bridge_rel

include A in
theorem occurrences_bridgeRow_new :
    StableSourceMatrix.occurrences C.datum (bridgeRow A)
        (occurrenceEquiv target wall C.right none) = {C.newSourceEdge bridge} := by
  classical
  ext e
  rw [StableSourceMatrix.mem_occurrences, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hS, hRow⟩, -⟩
    exact eq_bridge_of_stablePath_eq A ⟨e, hS⟩ hRow
  · rintro rfl
    exact ⟨⟨A.bridge_survives, rfl⟩, rfl⟩

include A in
/-- The corner entry of the bridge row is `1 / k₁`, the reciprocal of the
bridge's index. -/
theorem matrix_bridgeRow_new :
    StableSourceMatrix.matrix C.datum (bridgeRow A) (occurrenceEquiv target wall C.right none) =
      1 / (C.datum.sourceEdgeIndex (C.newSourceEdge bridge) : ℚ) := by
  classical
  unfold StableSourceMatrix.matrix
  rw [occurrences_bridgeRow_new A, Finset.sum_singleton]

end DraismaVargas.Count.GeneralKRowEquiv
