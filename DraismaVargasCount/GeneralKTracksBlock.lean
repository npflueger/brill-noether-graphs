import DraismaVargasCount.GeneralKLink
import DraismaVargasCount.GeneralKRowStar
import DraismaVargas.LocalCases.NonTrivalentValencyFourStarCount

/-!
# The branch vertices over a star-shaped wall block, for an arbitrary candidate

The datum-generic part of the general-`K` tracking (Vargas, Part II: the combinatorial
setup for a change of combinatorial type and the rigidity above `w_0`,
`subsec-setup-determinants` and `lemma-above-w0`, and the valency-four case `{v4-nd4}`,
`subsec-case-v4`).  The valency-four limits feed the type changes at merged-vertex
valency four (step 3 of `Assembly`).

This file works over an **arbitrary** globally assembled candidate
`C : BalancedGlobal.Candidate target degree G wall` over a valid datum `G` whose
source genus it preserves.  It classifies the branch vertices of `C` above one
wall block at which the resolution of `C` is a *star*
(`NonTrivalentValencyFourRows.IsStar`), and transports the surviving star of
that block to the unique branch vertex above it, occurrence by occurrence and
stable row by stable row.  The `K = 0` versions
(`NonTrivalentValencyFourTracks` §3, `NonTrivalentValencyFourStarCount` §1) are
stated for the specific `K = 0` candidate, so they do not apply to the general-`K`
candidate `GeneralKExitSetup.candK`; the arguments below are theirs, re-proved
over an arbitrary candidate.

## What is proved

The basic dictionary (`endV`, `epv`, `mem_ndI_epv`, `IsSurv`, `ret`, `pasted`, `StarHyp`,
...) is that of `GeneralKRowCore` and `GeneralKRowStar`; nothing defined there is
redefined here.

* §1  Two incidence facts at the new endpoint vertices (`oldSourceEdge_incident_self`,
  `retainedVertex_ne_epv`).
* §2  Two survivors at a divalent vertex lie on one stable row
  (`stablePath_eq_of_divalent`).
* §3  **The star-block census**, under explicit hypotheses on the block of a sheet `x`
  (star resolution, target-direction injectivity, surviving valency at most three, and
  at most two survivors per side): every vertex above the block has surviving valency
  at most three (`nd_over_le_three`, `census_small`); a vertex of surviving valency at
  least three above the block forces block valency three (`census_three_of_branch`);
  and when the block has valency three there is exactly one such vertex, trivalent,
  onto whose star the surviving star of the block is carried injectively, each
  survivor onto an occurrence of the stable row of its own retained copy
  (`census_branch`).  The proof splits into the *lonely* case (one fine survivor on
  the non-retaining side) and the *paired* case.
* §4  A labelled injective star map transports every label-filtered count
  (`card_filter_of_star_map`); row counts are label counts
  (`incidenceCount_eq_card_filter`).
* §5  (T1) off the wall (`card_filter_retainedVertex`) and at a non-anchor block
  (`census_transport`).
* §6  The same census with its hypotheses read off `GeneralKRowStar.StarHyp`
  (`side_of_starHyp`, `census_three_of_starHyp`, `census_transport_of_starHyp`).

## What is NOT proved here

Nothing about the anchor block, the gauge, or the tracking; see `GeneralKTracks` and
`GeneralKStarCount`.  The census is not proved for a block whose resolution is not a
star, nor for a block whose surviving valency exceeds three; both are hypotheses
(`StarHyp.star`, `StarHyp.valency`).  All hypotheses are explicit arguments or
`StarHyp`; no `Prop` is introduced here.
-/

set_option autoImplicit false

namespace DraismaVargas.Count.GeneralKTracksBlock

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.TargetExpansion
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StablePathCount
open DraismaVargas.Count.GeneralKRowCore
open DraismaVargas.Count.GeneralKRowStar

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {G : GluingDatum target degree}

/-! ## 1.  Two incidence facts at the new endpoint vertices -/

section Basic

variable (C : BalancedGlobal.Candidate target degree G wall)

theorem epv_target (b : Bool) (s : Fin degree) : (epv C b s).1.1 = endV C b := rfl

/-- An old occurrence at the wall meets the endpoint vertex of its own sheet on its
own side. -/
theorem oldSourceEdge_incident_self (edge : target.edges)
    (hAt : edge ∈ GluingDatum.incidentEdges wall) (b : Bool) (hSide : C.right edge = b)
    (sheet : Fin degree) :
    Incident C.datum (C.oldSourceEdge (G.sourceEdge edge sheet)) (epv C b sheet) := by
  cases b
  · exact LimitChainCore.oldSourceEdge_incident_old C edge hAt hSide sheet
  · exact M11SplitSurvival.oldSourceEdge_incident_fresh C edge hAt hSide sheet

theorem retainedVertex_ne_epv (old : G.SourceVertex) (hAway : old.1.1 ≠ wall) (b : Bool)
    (s : Fin degree) : ResolutionAwayFromWall.retainedVertex C old ≠ epv C b s := by
  intro h
  have h1 := congrArg (fun v : C.datum.SourceVertex ↦ v.1.1) h
  cases b
  · exact hAway (Sum.inl.inj h1)
  · cases h1

end Basic

/-! ## 2.  Counting at one vertex of a connected datum -/

section Counting

variable {tgt : CFGraph} {D : GluingDatum tgt degree}

/-- Two distinct survivors at a divalent vertex lie on one stable row. -/
theorem stablePath_eq_of_divalent {v : D.SourceVertex} (a b : NonDanglingEdge D)
    (hab : a ≠ b) (hIncA : Incident D a.1 v) (hIncB : Incident D b.1 v)
    (hTwo : nonDanglingValency D v = 2) : a.stablePath = b.stablePath :=
  stablePath_eq_of_consecutive ⟨hab, v, hIncA, hIncB, hTwo⟩

end Counting


/-! ## 3.  The star-block census -/

section Census

variable {C : BalancedGlobal.Candidate target degree G wall}

theorem isStar_congr {x y : Fin degree} (h : (G.vertexPartition wall).Rel x y)
    (hS : NonTrivalentValencyFourRows.IsStar (G.vertexPartition wall)
      (C.resolution ((G.vertexPartition wall).repr x))) :
    NonTrivalentValencyFourRows.IsStar (G.vertexPartition wall)
      (C.resolution ((G.vertexPartition wall).repr y)) := by
  rw [show (G.vertexPartition wall).repr y = (G.vertexPartition wall).repr x from h.symm]
  exact hS

theorem not_ne_self' (T : Bool) : (!T) ≠ T := by cases T <;> simp

variable (C) in
/-- A fine survivor of the block of `x`, in the new-edge class of `t`
(an abbreviation for the displayed conjunction). -/
abbrev FineIn (x t : Fin degree) (o : G.SourceEdge) : Prop :=
  IsSurv wall o x ∧ C.right o.1.1 = !ret C x ∧ (pasted C).newEdge.Rel t o.1.2

theorem newRel_wall {s t : Fin degree} (h : (pasted C).newEdge.Rel s t) :
    (G.vertexPartition wall).Rel s t :=
  (newPart_refines C).rel h

section Star

variable (hValid : G.Valid) (hGenus : genus C.datum.sourceGraph = genus G.sourceGraph)
include hValid hGenus

theorem old_mem_ndI {b : Bool} {x : Fin degree} {o : G.SourceEdge} (hS : ¬ IsDangling G o)
    (h1 : o.1.1 ∈ GluingDatum.incidentEdges wall) (h2 : C.right o.1.1 = b)
    (h3 : (endPart C b).Rel x o.1.2) :
    C.oldSourceEdge o ∈ nonDanglingIncident C.datum (epv C b x) :=
  (mem_ndI_epv C hValid hGenus b x _).mpr (Or.inl ⟨o, hS, h1, h2, h3, rfl⟩)

theorem new_mem_ndI {b : Bool} {x t : Fin degree} (h : (endPart C b).Rel x t)
    (hS : ¬ IsDangling C.datum (C.newSourceEdge t)) :
    C.newSourceEdge t ∈ nonDanglingIncident C.datum (epv C b x) :=
  (mem_ndI_epv C hValid hGenus b x _).mpr (Or.inr ⟨t, h, hS, rfl⟩)

variable {x : Fin degree}
  (hS : NonTrivalentValencyFourRows.IsStar (G.vertexPartition wall)
    (C.resolution ((G.vertexPartition wall).repr x)))
include hS

/-- **The fine endpoint's star**: its own new occurrence, and the fine survivors of
its class. -/
theorem ndI_fine_cases {t : Fin degree} (ht : (G.vertexPartition wall).Rel x t)
    {f : C.datum.SourceEdge} (hf : f ∈ nonDanglingIncident C.datum (epv C (!ret C x) t)) :
    f = C.newSourceEdge t ∨ ∃ o, FineIn C x t o ∧ f = C.oldSourceEdge o := by
  have hSt := isStar_congr ht hS
  have hRet : ret C t = ret C x := (ret_congr C ht).symm
  rcases (mem_ndI_epv C hValid hGenus _ t f).mp hf with
    ⟨o, hSurv, hAt, hSide, hRel, rfl⟩ | ⟨t', hRel, _, rfl⟩
  · right
    rw [← hRet] at hRel
    have hN := (fine_rel C hSt o.1.2).mp hRel
    exact ⟨o, ⟨⟨hSurv, hAt, ht.trans (newRel_wall hN)⟩, hSide, hN⟩, rfl⟩
  · left
    rw [← hRet] at hRel
    exact ((newSourceEdge_eq_iff C t t').mpr ((fine_rel C hSt t').mp hRel)).symm

/-- **The retaining endpoint's star**: retained survivors on the retaining side,
and surviving new occurrences of the block. -/
theorem ndI_ret_cases {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y)
    {f : C.datum.SourceEdge} (hf : f ∈ nonDanglingIncident C.datum (epv C (ret C x) y)) :
    (∃ o, IsSurv wall o x ∧ C.right o.1.1 = ret C x ∧ f = C.oldSourceEdge o) ∨
      ∃ t, (G.vertexPartition wall).Rel x t ∧ ¬ IsDangling C.datum (C.newSourceEdge t) ∧
        f = C.newSourceEdge t := by
  have hSy := isStar_congr hy hS
  have hRet : ret C y = ret C x := (ret_congr C hy).symm
  rcases (mem_ndI_epv C hValid hGenus _ y f).mp hf with
    ⟨o, hSurv, hAt, hSide, hRel, rfl⟩ | ⟨t, hRel, hSt, rfl⟩
  · left
    rw [← hRet] at hRel
    exact ⟨o, ⟨hSurv, hAt, hy.trans ((ret_rel C hSy o.1.2).mp hRel)⟩, hSide, rfl⟩
  · right
    rw [← hRet] at hRel
    exact ⟨t, hy.trans ((ret_rel C hSy t).mp hRel), hSt, rfl⟩

omit hValid hGenus in
theorem epv_ret_eq {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y) :
    epv C (ret C x) y = epv C (ret C x) x :=
  (epv_eq_iff C _ y x).mpr (((ret_rel C hS y).mpr hy).symm)

/-- **New pruning.**  A new occurrence of the block whose class carries no fine
survivor dangles: its fine endpoint would otherwise have surviving valency one. -/
theorem new_dangles_of_no_fine {t : Fin degree} (ht : (G.vertexPartition wall).Rel x t)
    (hNo : ¬ ∃ o, FineIn C x t o) : IsDangling C.datum (C.newSourceEdge t) := by
  refine isDangling_of_subset_singleton (C.datum_valid hValid).1 ?_
    (newSourceEdge_incident C (!ret C x) t)
  intro f hf
  rcases ndI_fine_cases hValid hGenus hS ht hf with rfl | ⟨o, ho, rfl⟩
  · exact Finset.mem_singleton_self _
  · exact absurd ⟨o, ho⟩ hNo

theorem exists_fineIn_of_survives {t : Fin degree} (ht : (G.vertexPartition wall).Rel x t)
    (hSurv : ¬ IsDangling C.datum (C.newSourceEdge t)) : ∃ o, FineIn C x t o := by
  by_contra hNo
  exact hSurv (new_dangles_of_no_fine hValid hGenus hS ht hNo)

/-- The retaining endpoint is named by the survivors of the block. -/
theorem ndI_ret_subset {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y) :
    nonDanglingIncident C.datum (epv C (ret C x) y) ⊆
      (nonDanglingIncident G (G.sourceEndpoint wall x)).image
        (fun o ↦ if C.right o.1.1 = ret C x then C.oldSourceEdge o
          else C.newSourceEdge o.1.2) := by
  intro f hf
  rcases ndI_ret_cases hValid hGenus hS hy hf with ⟨o, ho, hSide, rfl⟩ | ⟨t, ht, hSt, rfl⟩
  · exact Finset.mem_image.mpr ⟨o, (mem_ndI_G_iff o x).mpr ho, by rw [if_pos hSide]⟩
  · obtain ⟨o, ho, hSide, hN⟩ := exists_fineIn_of_survives hValid hGenus hS ht hSt
    refine Finset.mem_image.mpr ⟨o, (mem_ndI_G_iff o x).mpr ho, ?_⟩
    rw [if_neg (by rw [hSide]; exact not_ne_self' _)]
    exact ((newSourceEdge_eq_iff C _ _).mpr hN).symm

theorem nd_ret_le {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y) :
    nonDanglingValency C.datum (epv C (ret C x) y) ≤
      nonDanglingValency G (G.sourceEndpoint wall x) := by
  classical
  rw [← card_nonDanglingIncident, ← card_nonDanglingIncident]
  exact (Finset.card_le_card (ndI_ret_subset hValid hGenus hS hy)).trans Finset.card_image_le

/-- **New survival.**  A fine survivor alone in its new-edge class makes that
class's new occurrence survive, and its fine endpoint is divalent. -/
theorem new_survives_of_unique {o : G.SourceEdge} (ho : IsSurv wall o x)
    (hr : C.right o.1.1 = !ret C x) (hU : ∀ o', FineIn C x o.1.2 o' → o' = o) :
    ¬ IsDangling C.datum (C.newSourceEdge o.1.2) ∧
      nonDanglingValency C.datum (epv C (!ret C x) o.1.2) = 2 := by
  classical
  have ht : (G.vertexPartition wall).Rel x o.1.2 := ho.2.2
  have hOldS : ¬ IsDangling C.datum (C.oldSourceEdge o) :=
    fun h ↦ ho.1 ((isDangling_old_iff C hValid hGenus o).mp h)
  have hOldInc : Incident C.datum (C.oldSourceEdge o) (epv C (!ret C x) o.1.2) :=
    (oldSourceEdge_incident_iff C _ o o.1.2).mpr ⟨ho.2.1, hr, rfl⟩
  refine survives_of_subset_pair (C.datum_valid hValid).1 (new_ne_old C _ o) ?_
    (newSourceEdge_incident C _ _) hOldS hOldInc
  intro f hf
  rcases ndI_fine_cases hValid hGenus hS ht hf with rfl | ⟨o', ho', rfl⟩
  · simp
  · rw [hU o' ho']
    simp

/-- The new occurrence of a lonely fine survivor lies on that survivor's stable row. -/
theorem stablePath_new_of_unique {o : G.SourceEdge} (ho : IsSurv wall o x)
    (hr : C.right o.1.1 = !ret C x) (hU : ∀ o', FineIn C x o.1.2 o' → o' = o) :
    NonDanglingEdge.stablePath
        (⟨C.newSourceEdge o.1.2, (new_survives_of_unique hValid hGenus hS ho hr hU).1⟩ :
          NonDanglingEdge C.datum) =
      (ResolutionAwayFromWall.retainedEdge C hValid.1 ⟨o, ho.1⟩).stablePath := by
  refine stablePath_eq_of_divalent _ _ ?_ (newSourceEdge_incident C (!ret C x) o.1.2)
    ((oldSourceEdge_incident_iff C _ o o.1.2).mpr ⟨ho.2.1, hr, rfl⟩)
    (new_survives_of_unique hValid hGenus hS ho hr hU).2
  intro h
  exact new_ne_old C _ o (congrArg Subtype.val h)

open Classical in
/-- The fine endpoint's star lies in its new occurrence together with the fine
survivors of its class. -/
theorem ndI_fine_subset {t : Fin degree} (ht : (G.vertexPartition wall).Rel x t) :
    nonDanglingIncident C.datum (epv C (!ret C x) t) ⊆
      insert (C.newSourceEdge t)
        (((nonDanglingIncident G (G.sourceEndpoint wall x)).filter
          (fun o ↦ FineIn C x t o)).image C.oldSourceEdge) := by
  classical
  intro f hf
  rcases ndI_fine_cases hValid hGenus hS ht hf with rfl | ⟨o, ho, rfl⟩
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨o, Finset.mem_filter.mpr ⟨(mem_ndI_G_iff o x).mpr ho.1, ho⟩, rfl⟩)

/-! ### Two survivors on one side of the pairing at most -/

section Census3

variable (hVal : nonDanglingValency G (G.sourceEndpoint wall x) ≤ 3)
  (hSide : ∀ (b : Bool) (o₁ o₂ o₃ : G.SourceEdge), IsSurv wall o₁ x → IsSurv wall o₂ x →
    IsSurv wall o₃ x → C.right o₁.1.1 = b → C.right o₂.1.1 = b → C.right o₃.1.1 = b →
    o₁ = o₂ ∨ o₁ = o₃ ∨ o₂ = o₃)

omit hValid hGenus hS in
theorem card_le_of_side (hSide : ∀ (b : Bool) (o₁ o₂ o₃ : G.SourceEdge), IsSurv wall o₁ x →
    IsSurv wall o₂ x → IsSurv wall o₃ x → C.right o₁.1.1 = b → C.right o₂.1.1 = b →
    C.right o₃.1.1 = b → o₁ = o₂ ∨ o₁ = o₃ ∨ o₂ = o₃)
    (b : Bool) (F : Finset G.SourceEdge) (hF : ∀ o ∈ F, IsSurv wall o x ∧ C.right o.1.1 = b) :
    F.card ≤ 2 := by
  by_contra hBig
  obtain ⟨o₁, h₁, o₂, h₂, o₃, h₃, h12, h13, h23⟩ := (Finset.two_lt_card (s := F)).mp (by omega)
  rcases hSide b o₁ o₂ o₃ (hF _ h₁).1 (hF _ h₂).1 (hF _ h₃).1 (hF _ h₁).2 (hF _ h₂).2
    (hF _ h₃).2 with h | h | h
  · exact h12 h
  · exact h13 h
  · exact h23 h

omit hValid hGenus hS in
theorem card_survivors : (nonDanglingIncident G (G.sourceEndpoint wall x)).card =
    nonDanglingValency G (G.sourceEndpoint wall x) :=
  card_nonDanglingIncident G _

include hSide in
/-- **Every fine endpoint of the block is trivalent at most.** -/
theorem nd_fine_le_three {t : Fin degree} (ht : (G.vertexPartition wall).Rel x t) :
    nonDanglingValency C.datum (epv C (!ret C x) t) ≤ 3 := by
  classical
  rw [← card_nonDanglingIncident]
  refine (Finset.card_le_card (ndI_fine_subset hValid hGenus hS ht)).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  have h2 : ((nonDanglingIncident G (G.sourceEndpoint wall x)).filter
      (fun o ↦ FineIn C x t o)).card ≤ 2 :=
    card_le_of_side hSide (!ret C x) _ (fun o ho ↦
      ⟨(Finset.mem_filter.mp ho).2.1, (Finset.mem_filter.mp ho).2.2.1⟩)
  have := Finset.card_image_le (s := (nonDanglingIncident G (G.sourceEndpoint wall x)).filter
      (fun o ↦ FineIn C x t o)) (f := C.oldSourceEdge)
  omega

include hVal hSide in
/-- **Every vertex above the block is trivalent at most.** -/
theorem nd_over_le_three (b : Bool) {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y) :
    nonDanglingValency C.datum (epv C b y) ≤ 3 := by
  rcases bool_eq_or_eq_not b (ret C x) with rfl | rfl
  · exact (nd_ret_le hValid hGenus hS hy).trans hVal
  · exact nd_fine_le_three hValid hGenus hS hSide hy

/-- Lonely fine survivors: no two distinct fine survivors of the block share a
new-edge class (an abbreviation for the displayed statement). -/
abbrev Lonely (C : BalancedGlobal.Candidate target degree G wall) (x : Fin degree) : Prop :=
  ∀ o₁ o₂ : G.SourceEdge, IsSurv wall o₁ x → IsSurv wall o₂ x → C.right o₁.1.1 = !ret C x →
    C.right o₂.1.1 = !ret C x → (pasted C).newEdge.Rel o₁.1.2 o₂.1.2 → o₁ = o₂

omit hValid hGenus hS in
theorem lonely_unique (hL : Lonely C x) {o : G.SourceEdge} (ho : IsSurv wall o x)
    (hr : C.right o.1.1 = !ret C x) : ∀ o', FineIn C x o.1.2 o' → o' = o :=
  fun o' ho' ↦ (hL o o' ho ho'.1 hr ho'.2.1 ho'.2.2).symm

/-! #### The lonely case: the retaining endpoint carries the block's star -/

omit hValid hGenus hS in
open Classical in
theorem card_fine_le_one (hL : Lonely C x) (t : Fin degree) :
    ((nonDanglingIncident G (G.sourceEndpoint wall x)).filter
      (fun o ↦ FineIn C x t o)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro o₁ h₁ o₂ h₂
  obtain ⟨-, hf₁⟩ := Finset.mem_filter.mp h₁
  obtain ⟨-, hf₂⟩ := Finset.mem_filter.mp h₂
  exact hL o₁ o₂ hf₁.1 hf₂.1 hf₁.2.1 hf₂.2.1 (hf₁.2.2.symm.trans hf₂.2.2)

theorem nd_fine_le_two_of_lonely (hL : Lonely C x) {t : Fin degree}
    (ht : (G.vertexPartition wall).Rel x t) :
    nonDanglingValency C.datum (epv C (!ret C x) t) ≤ 2 := by
  classical
  rw [← card_nonDanglingIncident]
  refine (Finset.card_le_card (ndI_fine_subset hValid hGenus hS ht)).trans ?_
  refine (Finset.card_insert_le _ _).trans ?_
  have := (Finset.card_image_le (s := (nonDanglingIncident G (G.sourceEndpoint wall x)).filter
      (fun o ↦ FineIn C x t o)) (f := C.oldSourceEdge)).trans (card_fine_le_one hL t)
  omega

/-- A survivor of the block, read at the retaining endpoint: itself on the retaining
side, the new occurrence of its class otherwise. -/
noncomputable def retMap (C : BalancedGlobal.Candidate target degree G wall) (x : Fin degree)
    (o : G.SourceEdge) : C.datum.SourceEdge := by
  classical
  exact if C.right o.1.1 = ret C x then C.oldSourceEdge o else C.newSourceEdge o.1.2

theorem retMap_mem (hL : Lonely C x) {o : G.SourceEdge} (ho : IsSurv wall o x) :
    retMap C x o ∈ nonDanglingIncident C.datum (epv C (ret C x) x) := by
  classical
  unfold retMap
  split_ifs with hr
  · exact old_mem_ndI hValid hGenus ho.1 ho.2.1 hr ((ret_rel C hS o.1.2).mpr ho.2.2)
  · have hr' : C.right o.1.1 = !ret C x := by
      rcases bool_eq_or_eq_not (C.right o.1.1) (ret C x) with h | h
      · exact absurd h hr
      · exact h
    exact new_mem_ndI hValid hGenus ((ret_rel C hS o.1.2).mpr ho.2.2)
      (new_survives_of_unique hValid hGenus hS ho hr' (lonely_unique hL ho hr')).1

omit hValid hGenus hS in
theorem retMap_injOn (hL : Lonely C x) {o₁ o₂ : G.SourceEdge} (h₁ : IsSurv wall o₁ x)
    (h₂ : IsSurv wall o₂ x) (hEq : retMap C x o₁ = retMap C x o₂) : o₁ = o₂ := by
  classical
  unfold retMap at hEq
  by_cases hr₁ : C.right o₁.1.1 = ret C x <;> by_cases hr₂ : C.right o₂.1.1 = ret C x <;>
    simp only [hr₁, hr₂, if_true, if_false] at hEq
  · exact ResolutionCut.oldSourceEdge_injective C hEq
  · exact absurd hEq.symm (new_ne_old C _ _)
  · exact absurd hEq (new_ne_old C _ _)
  · have hr₁' : C.right o₁.1.1 = !ret C x := by
      rcases bool_eq_or_eq_not (C.right o₁.1.1) (ret C x) with h | h
      · exact absurd h hr₁
      · exact h
    have hr₂' : C.right o₂.1.1 = !ret C x := by
      rcases bool_eq_or_eq_not (C.right o₂.1.1) (ret C x) with h | h
      · exact absurd h hr₂
      · exact h
    exact hL o₁ o₂ h₁ h₂ hr₁' hr₂' ((newSourceEdge_eq_iff C _ _).mp hEq)

theorem ndI_ret_eq_of_lonely (hL : Lonely C x) :
    nonDanglingIncident C.datum (epv C (ret C x) x) =
      (nonDanglingIncident G (G.sourceEndpoint wall x)).image (retMap C x) := by
  classical
  refine Finset.Subset.antisymm ?_ ?_
  · intro f hf
    have := ndI_ret_subset hValid hGenus hS (rfl : (G.vertexPartition wall).Rel x x) hf
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp this
    exact Finset.mem_image.mpr ⟨o, ho, rfl⟩
  · intro f hf
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hf
    exact retMap_mem hValid hGenus hS hL ((mem_ndI_G_iff o x).mp ho)

theorem nd_ret_eq_of_lonely (hL : Lonely C x) :
    nonDanglingValency C.datum (epv C (ret C x) x) =
      nonDanglingValency G (G.sourceEndpoint wall x) := by
  classical
  rw [← card_nonDanglingIncident, ← card_nonDanglingIncident,
    ndI_ret_eq_of_lonely hValid hGenus hS hL]
  exact Finset.card_image_of_injOn (fun o₁ h₁ o₂ h₂ hEq ↦
    retMap_injOn hL ((mem_ndI_G_iff o₁ x).mp h₁) ((mem_ndI_G_iff o₂ x).mp h₂) hEq)

/-! #### The paired case: two fine survivors share a class -/

/-- Two distinct fine survivors in one new-edge class (an abbreviation for the
displayed statement). -/
abbrev Paired (C : BalancedGlobal.Candidate target degree G wall) (x : Fin degree)
    (o₁ o₂ : G.SourceEdge) : Prop :=
  o₁ ≠ o₂ ∧ IsSurv wall o₁ x ∧ IsSurv wall o₂ x ∧ C.right o₁.1.1 = !ret C x ∧
    C.right o₂.1.1 = !ret C x ∧ (pasted C).newEdge.Rel o₁.1.2 o₂.1.2

omit hValid hGenus hS in
theorem paired_of_not_lonely (hL : ¬ Lonely C x) : ∃ o₁ o₂, Paired C x o₁ o₂ := by
  by_contra hNo
  apply hL
  intro o₁ o₂ h₁ h₂ hr₁ hr₂ hN
  by_contra hNe
  exact hNo ⟨o₁, o₂, hNe, h₁, h₂, hr₁, hr₂, hN⟩

omit hValid hGenus hS hVal in
include hSide in
theorem fine_eq_of_paired {o₁ o₂ : G.SourceEdge} (hP : Paired C x o₁ o₂) {o : G.SourceEdge}
    (ho : IsSurv wall o x) (hr : C.right o.1.1 = !ret C x) : o = o₁ ∨ o = o₂ := by
  rcases hSide (!ret C x) o₁ o₂ o hP.2.1 hP.2.2.1 ho hP.2.2.2.1 hP.2.2.2.2.1 hr with
    h | h | h
  · exact absurd h hP.1
  · exact Or.inl h.symm
  · exact Or.inr h.symm

omit hValid hGenus hS in
include hSide in
/-- With a paired class and block valency three, the third survivor is on the
retaining side, and the block's survivors are exactly these three. -/
theorem exists_third_of_paired {o₁ o₂ : G.SourceEdge} (hP : Paired C x o₁ o₂)
    (h3 : nonDanglingValency G (G.sourceEndpoint wall x) = 3) :
    ∃ o₃, IsSurv wall o₃ x ∧ C.right o₃.1.1 = ret C x ∧ o₃ ≠ o₁ ∧ o₃ ≠ o₂ ∧
      ∀ o, IsSurv wall o x → o = o₁ ∨ o = o₂ ∨ o = o₃ := by
  classical
  have hCard : ({o₁, o₂} : Finset G.SourceEdge).card <
      (nonDanglingIncident G (G.sourceEndpoint wall x)).card := by
    rw [card_survivors, h3, Finset.card_pair hP.1]
    omega
  obtain ⟨o₃, h₃S, h₃N⟩ := Finset.exists_mem_notMem_of_card_lt_card hCard
  have h₃ : IsSurv wall o₃ x := (mem_ndI_G_iff o₃ x).mp h₃S
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at h₃N
  have hr₃ : C.right o₃.1.1 = ret C x := by
    rcases bool_eq_or_eq_not (C.right o₃.1.1) (ret C x) with h | h
    · exact h
    · rcases fine_eq_of_paired hSide hP h₃ h with h' | h'
      · exact absurd h' h₃N.1
      · exact absurd h' h₃N.2
  refine ⟨o₃, h₃, hr₃, h₃N.1, h₃N.2, ?_⟩
  intro o ho
  by_contra hNot
  simp only [not_or] at hNot
  have hSub : ({o₁, o₂, o₃, o} : Finset G.SourceEdge) ⊆
      nonDanglingIncident G (G.sourceEndpoint wall x) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (mem_ndI_G_iff _ x).mpr hP.2.1
    · exact (mem_ndI_G_iff _ x).mpr hP.2.2.1
    · exact h₃S
    · exact (mem_ndI_G_iff _ x).mpr ho
  have h4 : ({o₁, o₂, o₃, o} : Finset G.SourceEdge).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hP.1, Ne.symm h₃N.1, Ne.symm hNot.1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm h₃N.2, Ne.symm hNot.2.1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hNot.2.2]), Finset.card_singleton]
  have := Finset.card_le_card hSub
  rw [h4, card_survivors, h3] at this
  omega

omit hValid hGenus hS in
/-- With a paired class and block valency at most two, the block's survivors are
exactly the pair. -/
theorem eq_pair_of_paired {o₁ o₂ : G.SourceEdge} (hP : Paired C x o₁ o₂)
    (h2 : nonDanglingValency G (G.sourceEndpoint wall x) ≤ 2) :
    ∀ o, IsSurv wall o x → o = o₁ ∨ o = o₂ := by
  classical
  intro o ho
  by_contra hNot
  simp only [not_or] at hNot
  have hSub : ({o₁, o₂, o} : Finset G.SourceEdge) ⊆
      nonDanglingIncident G (G.sourceEndpoint wall x) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact (mem_ndI_G_iff _ x).mpr hP.2.1
    · exact (mem_ndI_G_iff _ x).mpr hP.2.2.1
    · exact (mem_ndI_G_iff _ x).mpr ho
  have h3 : ({o₁, o₂, o} : Finset G.SourceEdge).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hP.1, Ne.symm hNot.1]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hNot.2]), Finset.card_singleton]
  have := Finset.card_le_card hSub
  rw [h3, card_survivors] at this
  omega

omit hValid hGenus hVal hSide in
theorem fine_rel' {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y) (z : Fin degree) :
    (endPart C (!ret C x)).Rel y z ↔ (pasted C).newEdge.Rel y z := by
  rw [ret_congr C hy]
  exact fine_rel C (isStar_congr hy hS) z

omit hVal hSide in
theorem old_fine_mem {o : G.SourceEdge} (ho : IsSurv wall o x) (hr : C.right o.1.1 = !ret C x)
    {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y)
    (hN : (pasted C).newEdge.Rel y o.1.2) :
    C.oldSourceEdge o ∈ nonDanglingIncident C.datum (epv C (!ret C x) y) :=
  old_mem_ndI hValid hGenus ho.1 ho.2.1 hr ((fine_rel' hS hy o.1.2).mpr hN)

omit hVal hSide in
theorem fine_empty_ndI {t : Fin degree} (ht : (G.vertexPartition wall).Rel x t)
    (hNo : ∀ o, ¬ FineIn C x t o) :
    nonDanglingValency C.datum (epv C (!ret C x) t) ≤ 1 := by
  classical
  rw [← card_nonDanglingIncident]
  have hSub : nonDanglingIncident C.datum (epv C (!ret C x) t) ⊆ {C.newSourceEdge t} := by
    intro f hf
    rcases ndI_fine_cases hValid hGenus hS ht hf with rfl | ⟨o, ho, rfl⟩
    · exact Finset.mem_singleton_self _
    · exact absurd ho (hNo o)
  exact (Finset.card_le_card hSub).trans (by simp)

section Paired

variable {o₁ o₂ : G.SourceEdge} (hP : Paired C x o₁ o₂)
include hP hSide

omit hValid hGenus hS hVal in
theorem fineIn_cases {t : Fin degree} {o : G.SourceEdge} (ho : FineIn C x t o) :
    (o = o₁ ∨ o = o₂) ∧ (pasted C).newEdge.Rel t o₁.1.2 := by
  have hEq := fine_eq_of_paired hSide hP ho.1 ho.2.1
  refine ⟨hEq, ?_⟩
  rcases hEq with rfl | rfl
  · exact ho.2.2
  · exact ho.2.2.trans hP.2.2.2.2.2.symm

omit hVal in
theorem nd_fine_le_one_of_paired {t : Fin degree} (ht : (G.vertexPartition wall).Rel x t)
    (hN : ¬ (pasted C).newEdge.Rel t o₁.1.2) :
    nonDanglingValency C.datum (epv C (!ret C x) t) ≤ 1 :=
  fine_empty_ndI hValid hGenus hS ht (fun _o ho ↦ hN (fineIn_cases hSide hP ho).2)

omit hVal in
/-- With a paired class, the retaining endpoint's star is carried by the pair's new
occurrence and the retaining-side survivors. -/
theorem ndI_ret_subset_of_paired :
    nonDanglingIncident C.datum (epv C (ret C x) x) ⊆
      insert (C.newSourceEdge o₁.1.2)
        (((nonDanglingIncident G (G.sourceEndpoint wall x)).filter
          (fun o ↦ C.right o.1.1 = ret C x)).image C.oldSourceEdge) := by
  classical
  intro f hf
  have hMem := ndI_ret_subset hValid hGenus hS (rfl : (G.vertexPartition wall).Rel x x) hf
  obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hMem
  by_cases hr : C.right o.1.1 = ret C x
  · rw [if_pos hr]
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨o, Finset.mem_filter.mpr ⟨ho, hr⟩, rfl⟩)
  · rw [if_neg hr]
    have hr' : C.right o.1.1 = !ret C x := by
      rcases bool_eq_or_eq_not (C.right o.1.1) (ret C x) with h | h
      · exact absurd h hr
      · exact h
    rcases fine_eq_of_paired hSide hP ((mem_ndI_G_iff o x).mp ho) hr' with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · rw [(newSourceEdge_eq_iff C _ _).mpr hP.2.2.2.2.2.symm]
      exact Finset.mem_insert_self _ _

omit hVal in
/-- **Paired, block valency at most two**: the pair's new occurrence dangles. -/
theorem new_dangles_of_paired_small
    (h2 : nonDanglingValency G (G.sourceEndpoint wall x) ≤ 2) :
    IsDangling C.datum (C.newSourceEdge o₁.1.2) := by
  classical
  have hNoRet : ∀ o : G.SourceEdge, IsSurv wall o x → C.right o.1.1 ≠ ret C x := by
    intro o ho hr
    rcases eq_pair_of_paired hP h2 o ho with rfl | rfl
    · exact not_ne_self' _ (hP.2.2.2.1.symm.trans hr)
    · exact not_ne_self' _ (hP.2.2.2.2.1.symm.trans hr)
  refine isDangling_of_subset_singleton (C.datum_valid hValid).1 ?_
    ((newSourceEdge_incident_iff C _ _ _).mpr ((ret_rel C hS o₁.1.2).mpr hP.2.1.2.2))
  intro f hf
  have := ndI_ret_subset_of_paired hValid hGenus hS hSide hP hf
  rcases Finset.mem_insert.mp this with h | h
  · rw [h]
    exact Finset.mem_singleton_self _
  · obtain ⟨o, ho, -⟩ := Finset.mem_image.mp h
    obtain ⟨ho, hr⟩ := Finset.mem_filter.mp ho
    exact absurd hr (hNoRet o ((mem_ndI_G_iff o x).mp ho))

omit hVal in
theorem nd_fine_le_two_of_paired_small
    (h2 : nonDanglingValency G (G.sourceEndpoint wall x) ≤ 2) {t : Fin degree}
    (ht : (G.vertexPartition wall).Rel x t) :
    nonDanglingValency C.datum (epv C (!ret C x) t) ≤ 2 := by
  classical
  by_cases hN : (pasted C).newEdge.Rel t o₁.1.2
  · have hDang : IsDangling C.datum (C.newSourceEdge t) := by
      rw [(newSourceEdge_eq_iff C _ _).mpr hN]
      exact new_dangles_of_paired_small hValid hGenus hS hSide hP h2
    rw [← card_nonDanglingIncident]
    have hSub : nonDanglingIncident C.datum (epv C (!ret C x) t) ⊆
        {C.oldSourceEdge o₁, C.oldSourceEdge o₂} := by
      intro f hf
      rcases ndI_fine_cases hValid hGenus hS ht hf with rfl | ⟨o, ho, rfl⟩
      · exact absurd hDang ((mem_nonDanglingIncident _ _ _).mp hf).1
      · rcases (fineIn_cases hSide hP ho).1 with rfl | rfl <;> simp
    exact (Finset.card_le_card hSub).trans Finset.card_le_two
  · exact (nd_fine_le_one_of_paired hValid hGenus hS hSide hP ht hN).trans (by omega)

section Three

variable {o₃ : G.SourceEdge} (h₃ : IsSurv wall o₃ x) (hr₃ : C.right o₃.1.1 = ret C x)
  (hAll : ∀ o, IsSurv wall o x → o = o₁ ∨ o = o₂ ∨ o = o₃)
include h₃ hr₃ hAll

omit hVal in
/-- **Paired, block valency three**: the pair's new occurrence survives, the
retaining endpoint is divalent, and the new occurrence lies on the third
survivor's stable row. -/
theorem new_survives_of_paired :
    ¬ IsDangling C.datum (C.newSourceEdge o₁.1.2) ∧
      nonDanglingValency C.datum (epv C (ret C x) x) = 2 := by
  classical
  have hOldS : ¬ IsDangling C.datum (C.oldSourceEdge o₃) :=
    fun h ↦ h₃.1 ((isDangling_old_iff C hValid hGenus o₃).mp h)
  refine survives_of_subset_pair (C.datum_valid hValid).1 (new_ne_old C _ o₃) ?_
    ((newSourceEdge_incident_iff C _ _ _).mpr ((ret_rel C hS o₁.1.2).mpr hP.2.1.2.2)) hOldS
    ((oldSourceEdge_incident_iff C _ o₃ x).mpr ⟨h₃.2.1, hr₃, (ret_rel C hS o₃.1.2).mpr h₃.2.2⟩)
  intro f hf
  have := ndI_ret_subset_of_paired hValid hGenus hS hSide hP hf
  rcases Finset.mem_insert.mp this with h | h
  · rw [h]
    exact Finset.mem_insert_self _ _
  · obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨ho, hr⟩ := Finset.mem_filter.mp ho
    rcases hAll o ((mem_ndI_G_iff o x).mp ho) with rfl | rfl | rfl
    · exact absurd (hP.2.2.2.1.symm.trans hr) (not_ne_self' _)
    · exact absurd (hP.2.2.2.2.1.symm.trans hr) (not_ne_self' _)
    · simp

omit hVal in
theorem stablePath_new_of_paired :
    NonDanglingEdge.stablePath
        (⟨C.newSourceEdge o₁.1.2,
          (new_survives_of_paired hValid hGenus hS hSide hP h₃ hr₃ hAll).1⟩ :
          NonDanglingEdge C.datum) =
      (ResolutionAwayFromWall.retainedEdge C hValid.1 ⟨o₃, h₃.1⟩).stablePath := by
  refine stablePath_eq_of_divalent _ _ ?_
    ((newSourceEdge_incident_iff C _ _ _).mpr ((ret_rel C hS o₁.1.2).mpr hP.2.1.2.2))
    ((oldSourceEdge_incident_iff C _ o₃ x).mpr ⟨h₃.2.1, hr₃, (ret_rel C hS o₃.1.2).mpr h₃.2.2⟩)
    (new_survives_of_paired hValid hGenus hS hSide hP h₃ hr₃ hAll).2
  intro h
  exact new_ne_old C _ o₃ (congrArg Subtype.val h)

/-- **Paired, block valency three**: the common fine endpoint of the pair is
trivalent. -/
theorem nd_fine_eq_three_of_paired :
    nonDanglingValency C.datum (epv C (!ret C x) o₁.1.2) = 3 := by
  have hx1 : (G.vertexPartition wall).Rel x o₁.1.2 := hP.2.1.2.2
  refine le_antisymm (nd_fine_le_three hValid hGenus hS hSide hx1) ?_
  refine three_le_nd
    (new_mem_ndI hValid hGenus ((fine_rel' hS hx1 o₁.1.2).mpr rfl)
      (new_survives_of_paired hValid hGenus hS hSide hP h₃ hr₃ hAll).1)
    (old_fine_mem hValid hGenus hS hP.2.1 hP.2.2.2.1 hx1 rfl)
    (old_fine_mem hValid hGenus hS hP.2.2.1 hP.2.2.2.2.1 hx1 hP.2.2.2.2.2)
    (new_ne_old C _ _) (new_ne_old C _ _) ?_
  intro h
  exact hP.1 (ResolutionCut.oldSourceEdge_injective C h)

end Three

end Paired

omit hValid hGenus hS in
theorem eq_not_of_ne {b T : Bool} (h : b ≠ T) : b = !T := by
  rcases bool_eq_or_eq_not b T with h' | h'
  · exact absurd h' h
  · exact h'

omit hValid hGenus hS in
theorem surv_of_mem_incidentEdges {e : NonDanglingEdge G}
    (he : e ∈ incidentEdges G (G.sourceEndpoint wall x)) : IsSurv wall e.1 x :=
  (mem_ndI_G_iff e.1 x).mp ((mem_nonDanglingIncident _ _ _).mpr
    ⟨e.2, (mem_incidentEdges _ _ _).mp he⟩)

/-! ### The census -/

include hSide in
/-- **A block of surviving valency at most two carries no branch vertex.** -/
theorem census_small (h2 : nonDanglingValency G (G.sourceEndpoint wall x) ≤ 2) (b : Bool)
    {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y) :
    nonDanglingValency C.datum (epv C b y) ≤ 2 := by
  rcases bool_eq_or_eq_not b (ret C x) with rfl | rfl
  · exact (nd_ret_le hValid hGenus hS hy).trans h2
  · by_cases hL : Lonely C x
    · exact nd_fine_le_two_of_lonely hValid hGenus hS hL hy
    · obtain ⟨o₁, o₂, hP⟩ := paired_of_not_lonely hL
      exact nd_fine_le_two_of_paired_small hValid hGenus hS hSide hP h2 hy

include hVal hSide in
/-- **A branch vertex above the block forces block valency three.** -/
theorem census_three_of_branch (b : Bool) {y : Fin degree}
    (hy : (G.vertexPartition wall).Rel x y)
    (h : 3 ≤ nonDanglingValency C.datum (epv C b y)) :
    nonDanglingValency G (G.sourceEndpoint wall x) = 3 := by
  by_contra hne
  have := census_small hValid hGenus hS hSide (by omega) b hy
  omega

theorem stablePath_retMap_of_lonely (hL : Lonely C x) {e : NonDanglingEdge G}
    (he : IsSurv wall e.1 x) :
    NonDanglingEdge.stablePath (⟨retMap C x e.1,
        ((mem_nonDanglingIncident _ _ _).mp (retMap_mem hValid hGenus hS hL he)).1⟩ :
          NonDanglingEdge C.datum) =
      (ResolutionAwayFromWall.retainedEdge C hValid.1 e).stablePath := by
  classical
  by_cases hr : C.right e.1.1.1 = ret C x
  · congr 1
    apply Subtype.ext
    show retMap C x e.1 = C.oldSourceEdge e.1
    unfold retMap
    rw [if_pos hr]
  · have hr' := eq_not_of_ne hr
    have hEq : (⟨retMap C x e.1,
        ((mem_nonDanglingIncident _ _ _).mp (retMap_mem hValid hGenus hS hL he)).1⟩ :
          NonDanglingEdge C.datum) =
        ⟨C.newSourceEdge e.1.1.2,
          (new_survives_of_unique hValid hGenus hS he hr' (lonely_unique hL he hr')).1⟩ := by
      apply Subtype.ext
      show retMap C x e.1 = C.newSourceEdge e.1.1.2
      unfold retMap
      rw [if_neg hr]
    rw [hEq, stablePath_new_of_unique hValid hGenus hS he hr' (lonely_unique hL he hr')]
    rfl

include hSide in
/-- **The star-block census.**  A block of surviving valency three carries exactly
one branch vertex of the candidate; it is trivalent, and the surviving star of the
block is carried injectively onto its surviving star, each survivor onto an
occurrence of the stable row of its own retained copy. -/
theorem census_branch (h3 : nonDanglingValency G (G.sourceEndpoint wall x) = 3) :
    ∃ (b₀ : Bool) (y₀ : Fin degree), (G.vertexPartition wall).Rel x y₀ ∧
      nonDanglingValency C.datum (epv C b₀ y₀) = 3 ∧
      (∀ (b : Bool) (y : Fin degree), (G.vertexPartition wall).Rel x y →
        3 ≤ nonDanglingValency C.datum (epv C b y) → epv C b y = epv C b₀ y₀) ∧
      ∃ Φ : ∀ e ∈ incidentEdges G (G.sourceEndpoint wall x), NonDanglingEdge C.datum,
        (∀ e he, Φ e he ∈ incidentEdges C.datum (epv C b₀ y₀)) ∧
        (∀ e₁ e₂ h₁ h₂, Φ e₁ h₁ = Φ e₂ h₂ → e₁ = e₂) ∧
        (∀ e he, (Φ e he).stablePath =
          (ResolutionAwayFromWall.retainedEdge C hValid.1 e).stablePath) := by
  classical
  by_cases hL : Lonely C x
  · refine ⟨ret C x, x, rfl, (nd_ret_eq_of_lonely hValid hGenus hS hL).trans h3, ?_, ?_⟩
    · intro b y hy h
      rcases bool_eq_or_eq_not b (ret C x) with rfl | rfl
      · exact epv_ret_eq hS hy
      · have := nd_fine_le_two_of_lonely hValid hGenus hS hL hy
        omega
    · refine ⟨fun e he ↦ ⟨retMap C x e.1, ((mem_nonDanglingIncident _ _ _).mp
          (retMap_mem hValid hGenus hS hL (surv_of_mem_incidentEdges he))).1⟩, ?_, ?_, ?_⟩
      · intro e he
        exact (mem_incidentEdges _ _ _).mpr ((mem_nonDanglingIncident _ _ _).mp
          (retMap_mem hValid hGenus hS hL (surv_of_mem_incidentEdges he))).2
      · intro e₁ e₂ h₁ h₂ hEq
        exact Subtype.ext (retMap_injOn hL (surv_of_mem_incidentEdges h₁)
          (surv_of_mem_incidentEdges h₂) (congrArg Subtype.val hEq))
      · intro e he
        exact stablePath_retMap_of_lonely hValid hGenus hS hL (surv_of_mem_incidentEdges he)
  · obtain ⟨o₁, o₂, hP⟩ := paired_of_not_lonely hL
    obtain ⟨o₃, h₃, hr₃, h31, h32, hAll⟩ := exists_third_of_paired hSide hP h3
    have hx1 : (G.vertexPartition wall).Rel x o₁.1.2 := hP.2.1.2.2
    have hNewS := (new_survives_of_paired hValid hGenus hS hSide hP h₃ hr₃ hAll).1
    have hMem : ∀ o : G.SourceEdge, IsSurv wall o x →
        (if o = o₃ then C.newSourceEdge o₁.1.2 else C.oldSourceEdge o) ∈
          nonDanglingIncident C.datum (epv C (!ret C x) o₁.1.2) := by
      intro o ho
      by_cases h : o = o₃
      · rw [if_pos h]
        exact new_mem_ndI hValid hGenus ((fine_rel' hS hx1 o₁.1.2).mpr rfl) hNewS
      · rw [if_neg h]
        rcases hAll o ho with rfl | rfl | rfl
        · exact old_fine_mem hValid hGenus hS hP.2.1 hP.2.2.2.1 hx1 rfl
        · exact old_fine_mem hValid hGenus hS hP.2.2.1 hP.2.2.2.2.1 hx1 hP.2.2.2.2.2
        · exact absurd rfl h
    refine ⟨!ret C x, o₁.1.2, hx1,
      nd_fine_eq_three_of_paired hValid hGenus hS hSide hP h₃ hr₃ hAll, ?_, ?_⟩
    · intro b y hy h
      rcases bool_eq_or_eq_not b (ret C x) with rfl | rfl
      · rw [epv_ret_eq hS hy, (new_survives_of_paired hValid hGenus hS hSide hP h₃ hr₃
          hAll).2] at h
        omega
      · by_cases hN : (pasted C).newEdge.Rel y o₁.1.2
        · exact (epv_eq_iff C _ y o₁.1.2).mpr ((fine_rel' hS hy o₁.1.2).mpr hN)
        · have := nd_fine_le_one_of_paired hValid hGenus hS hSide hP hy hN
          omega
    · refine ⟨fun e he ↦ ⟨if e.1 = o₃ then C.newSourceEdge o₁.1.2 else C.oldSourceEdge e.1,
          ((mem_nonDanglingIncident _ _ _).mp
            (hMem e.1 (surv_of_mem_incidentEdges he))).1⟩, ?_, ?_, ?_⟩
      · intro e he
        exact (mem_incidentEdges _ _ _).mpr ((mem_nonDanglingIncident _ _ _).mp
          (hMem e.1 (surv_of_mem_incidentEdges he))).2
      · intro e₁ e₂ h₁ h₂ hEq
        have hv := congrArg Subtype.val hEq
        simp only at hv
        apply Subtype.ext
        by_cases k₁ : e₁.1 = o₃ <;> by_cases k₂ : e₂.1 = o₃ <;>
          simp only [k₁, k₂, if_true, if_false] at hv
        · exact k₁.trans k₂.symm
        · exact absurd hv (new_ne_old C _ _)
        · exact absurd hv.symm (new_ne_old C _ _)
        · exact ResolutionCut.oldSourceEdge_injective C hv
      · intro e he
        by_cases k : e.1 = o₃
        · have hE : e = ⟨o₃, h₃.1⟩ := Subtype.ext k
          subst hE
          rw [← stablePath_new_of_paired hValid hGenus hS hSide hP h₃ hr₃ hAll]
          congr 1
          apply Subtype.ext
          simp
        · congr 1
          apply Subtype.ext
          simp only [k, if_false]
          rfl

end Census3

end Star

end Census

/-! ## 4.  A labelled star map transports every label-filtered count -/

section StarMap

variable {target₁ target₂ : CFGraph} {degree₁ degree₂ : ℕ}
  {data₁ : GluingDatum target₁ degree₁} {data₂ : GluingDatum target₂ degree₂}
  {κ : Type*} [DecidableEq κ]

/-- **An injective label-preserving star map transports every label-filtered
count.**  It is automatically surjective once the target star is no larger. -/
theorem card_filter_of_star_map (v₁ : data₁.SourceVertex) (v₂ : data₂.SourceVertex)
    (lab₁ : NonDanglingEdge data₁ → κ) (lab₂ : NonDanglingEdge data₂ → κ)
    (Φ : ∀ e ∈ incidentEdges data₁ v₁, NonDanglingEdge data₂)
    (hMem : ∀ e he, Φ e he ∈ incidentEdges data₂ v₂)
    (hLab : ∀ e he, lab₂ (Φ e he) = lab₁ e)
    (hInj : ∀ e₁ e₂ he₁ he₂, Φ e₁ he₁ = Φ e₂ he₂ → e₁ = e₂)
    (hCard : nonDanglingValency data₂ v₂ ≤ nonDanglingValency data₁ v₁) (c : κ) :
    ((incidentEdges data₁ v₁).filter (fun e ↦ lab₁ e = c)).card =
      ((incidentEdges data₂ v₂).filter (fun e ↦ lab₂ e = c)).card := by
  classical
  have hSurj := Finset.surj_on_of_inj_on_of_card_le Φ hMem hInj
    (by rw [card_incidentEdges, card_incidentEdges]; exact hCard)
  refine Finset.card_bij (fun e he ↦ Φ e (Finset.mem_filter.mp he).1) ?_ ?_ ?_
  · intro e he
    refine Finset.mem_filter.mpr ⟨hMem _ _, ?_⟩
    rw [hLab, (Finset.mem_filter.mp he).2]
  · intro e₁ h₁ e₂ h₂ hEq
    exact hInj _ _ _ _ hEq
  · intro g hg
    obtain ⟨hMemG, hLabG⟩ := Finset.mem_filter.mp hg
    obtain ⟨e, he, rfl⟩ := hSurj g hMemG
    refine ⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, rfl⟩
    rw [← hLab e he]
    exact hLabG

/-- A row-filtered count is a label-filtered count, for an injective label of the rows. -/
theorem incidenceCount_eq_card_filter (v : data₁.SourceVertex) (lab : StablePath data₁ → κ)
    (hLab : Function.Injective lab) (r : StablePath data₁) :
    incidenceCount data₁ v r =
      ((incidentEdges data₁ v).filter (fun e ↦ lab e.stablePath = lab r)).card := by
  classical
  unfold incidenceCount
  congr 1
  ext e
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ by rw [h], fun h ↦ hLab h⟩

end StarMap

/-! ## 5.  Transport to the branch vertex above a block, and off the wall -/

section Transport

variable {C : BalancedGlobal.Candidate target degree G wall}
  (hValid : G.Valid) (hGenus : genus C.datum.sourceGraph = genus G.sourceGraph)
  {κ : Type*} [DecidableEq κ] (lab : StablePath C.datum → κ)

include hValid hGenus in
/-- **(T1) off the wall.**  The star of a vertex away from the wall is carried to
its retained vertex, each survivor onto its retained copy. -/
theorem card_filter_retainedVertex (w : G.SourceVertex) (hAway : w.1.1 ≠ wall) (c : κ) :
    ((incidentEdges C.datum (ResolutionAwayFromWall.retainedVertex C w)).filter
        (fun f ↦ lab f.stablePath = c)).card =
      ((incidentEdges G w).filter (fun e ↦
        lab (ResolutionAwayFromWall.retainedEdge C hValid.1 e).stablePath = c)).card := by
  classical
  refine (card_filter_of_star_map w (ResolutionAwayFromWall.retainedVertex C w)
    (fun e ↦ lab (ResolutionAwayFromWall.retainedEdge C hValid.1 e).stablePath)
    (fun f ↦ lab f.stablePath)
    (fun e _ ↦ ResolutionAwayFromWall.retainedEdge C hValid.1 e) ?_ (fun _ _ ↦ rfl) ?_ ?_ c).symm
  · intro e he
    exact (mem_incidentEdges _ _ _).mpr
      ((ResolutionAwayFromWall.incident_oldSourceEdge_iff C w hAway e.1).mpr
        ((mem_incidentEdges _ _ _).mp he))
  · intro e₁ e₂ _ _ hEq
    exact ResolutionAwayFromWall.retainedEdge_injective C hValid.1 hEq
  · rw [ResolutionAwayFromWall.nonDanglingValency_retainedVertex C hValid hGenus w hAway]

include hValid hGenus in
/-- **(T1) at a non-anchor block.**  A block of surviving valency three carries exactly
one branch vertex of the candidate, trivalent, whose label-filtered star counts are
those of the block, read through the retained copies. -/
theorem census_transport {x : Fin degree}
    (hS : NonTrivalentValencyFourRows.IsStar (G.vertexPartition wall)
      (C.resolution ((G.vertexPartition wall).repr x)))
    (hSide : ∀ (b : Bool) (o₁ o₂ o₃ : G.SourceEdge), IsSurv wall o₁ x → IsSurv wall o₂ x →
      IsSurv wall o₃ x → C.right o₁.1.1 = b → C.right o₂.1.1 = b → C.right o₃.1.1 = b →
      o₁ = o₂ ∨ o₁ = o₃ ∨ o₂ = o₃)
    (h3 : nonDanglingValency G (G.sourceEndpoint wall x) = 3) :
    ∃ (b₀ : Bool) (y₀ : Fin degree), (G.vertexPartition wall).Rel x y₀ ∧
      nonDanglingValency C.datum (epv C b₀ y₀) = 3 ∧
      (∀ (b : Bool) (y : Fin degree), (G.vertexPartition wall).Rel x y →
        3 ≤ nonDanglingValency C.datum (epv C b y) → epv C b y = epv C b₀ y₀) ∧
      ∀ c : κ, ((incidentEdges C.datum (epv C b₀ y₀)).filter
          (fun f ↦ lab f.stablePath = c)).card =
        ((incidentEdges G (G.sourceEndpoint wall x)).filter (fun e ↦
          lab (ResolutionAwayFromWall.retainedEdge C hValid.1 e).stablePath = c)).card := by
  obtain ⟨b₀, y₀, hy₀, hnd, hUniq, Φ, hMem, hInj, hPath⟩ :=
    census_branch hValid hGenus hS hSide h3
  refine ⟨b₀, y₀, hy₀, hnd, hUniq, fun c ↦ ?_⟩
  refine (card_filter_of_star_map _ _
    (fun e ↦ lab (ResolutionAwayFromWall.retainedEdge C hValid.1 e).stablePath)
    (fun f ↦ lab f.stablePath) Φ hMem (fun e he ↦ by rw [hPath e he]) hInj ?_ c).symm
  rw [hnd, h3]

end Transport

/-! ## 6.  The census from `StarHyp` -/

section OfStarHyp

variable {C : BalancedGlobal.Candidate target degree G wall} {a : Fin degree}
  (S : StarHyp C a)

include S in
/-- The survivor form of `StarHyp.side`: at most two survivors of a non-anchor block
on one side of the pairing. -/
theorem side_of_starHyp {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (b : Bool) (o₁ o₂ o₃ : G.SourceEdge) (h₁ : IsSurv wall o₁ x) (h₂ : IsSurv wall o₂ x)
    (h₃ : IsSurv wall o₃ x) (hs₁ : C.right o₁.1.1 = b) (hs₂ : C.right o₂.1.1 = b)
    (hs₃ : C.right o₃.1.1 = b) : o₁ = o₂ ∨ o₁ = o₃ ∨ o₂ = o₃ := by
  rcases S.side b _ _ _ h₁.2.1 h₂.2.1 h₃.2.1 hs₁ hs₂ hs₃ with h | h | h
  · exact Or.inl (S.inj x hx _ _ h₁ h₂ h)
  · exact Or.inr (Or.inl (S.inj x hx _ _ h₁ h₃ h))
  · exact Or.inr (Or.inr (S.inj x hx _ _ h₂ h₃ h))

include S in
/-- **A branch vertex above a non-anchor block forces block valency three.** -/
theorem census_three_of_starHyp {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (b : Bool) {y : Fin degree} (hy : (G.vertexPartition wall).Rel x y)
    (h : 3 ≤ nonDanglingValency C.datum (epv C b y)) :
    nonDanglingValency G (G.sourceEndpoint wall x) = 3 :=
  census_three_of_branch S.valid S.genus (S.star x hx) (S.valency x hx)
    (side_of_starHyp S hx) b hy h

include S in
/-- **(T1) at a non-anchor block, from `StarHyp`.** -/
theorem census_transport_of_starHyp {κ : Type*} [DecidableEq κ] (lab : StablePath C.datum → κ)
    {x : Fin degree} (hx : ¬ (G.vertexPartition wall).Rel a x)
    (h3 : nonDanglingValency G (G.sourceEndpoint wall x) = 3) :
    ∃ (b₀ : Bool) (y₀ : Fin degree), (G.vertexPartition wall).Rel x y₀ ∧
      nonDanglingValency C.datum (epv C b₀ y₀) = 3 ∧
      (∀ (b : Bool) (y : Fin degree), (G.vertexPartition wall).Rel x y →
        3 ≤ nonDanglingValency C.datum (epv C b y) → epv C b y = epv C b₀ y₀) ∧
      ∀ c : κ, ((incidentEdges C.datum (epv C b₀ y₀)).filter
          (fun f ↦ lab f.stablePath = c)).card =
        ((incidentEdges G (G.sourceEndpoint wall x)).filter (fun e ↦
          lab (ResolutionAwayFromWall.retainedEdge C S.valid.1 e).stablePath = c)).card :=
  census_transport S.valid S.genus lab (S.star x hx) (side_of_starHyp S hx) h3

end OfStarHyp

end DraismaVargas.Count.GeneralKTracksBlock
