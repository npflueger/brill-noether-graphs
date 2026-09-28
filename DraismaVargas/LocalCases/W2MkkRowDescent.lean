import DraismaVargas.LocalCases.W2MkkStableLift

/-!
# Descending Figure 34's occurrences to old stable rows

Source: Draisma–Vargas Part I, arXiv:1909.12924, case `{w2-r2-nd3-M-kk}` and Figure 34.

A retained occurrence goes back to itself.  A regrown occurrence above `A₀`
goes to the old occurrence `W2MkkStableGraph`'s census names — the retained
`t₂` occurrence through the same sheet for a detaching member, `e₃` for the
joined one — and a regrown occurrence over a background wall block goes to the
old `t₂` occurrence there.  This is the core's `SelectedData.rowOfEdge`, whose
local consecutive checks — not an assumed row correspondence — make it a map on
stable classes.

Composing with `W2MkkStableLift`'s lift gives an explicit geometric left
inverse, so the lift is injective; with its proved surjectivity this is the
geometric stable-row bijection `stablePathEquiv` of each member.

Nothing here is specific to which detaching member the datum carries: `M⁽¹⁾`
and `M⁽²⁾` are the same uniform `DetachData.candidate`, and member 2 is obtained
by instantiating these definitions at the branch-swapped datum.
-/

namespace DraismaVargas.LocalCases.W2MkkRowDescent

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2MkkSourceCandidates
open W2MkkStableGraph
open W2MkkStableLift

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## The detaching members `M⁽¹⁾`, `M⁽²⁾` -/

/-- A fixed old surviving occurrence representing one regrown occurrence of a
detaching member. -/
noncomputable def detachNewOldEdge (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).newSourceEdge sheet)) : NonDanglingEdge data :=
  (detachSelectedData input shape detach).newOldEdge sheet hSurvives

/-- Choose the unique retained preimage when there is one; otherwise the
occurrence is regrown and uses its fixed old representative. -/
noncomputable def detachRowOfEdge (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (edge : NonDanglingEdge (detach.candidate shape).datum) :
    StablePath data :=
  (detachSelectedData input shape detach).rowOfEdge edge

theorem detachRowOfEdge_retained (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (old : NonDanglingEdge data) :
    detachRowOfEdge input shape detach
        (retainedEdge (detach.candidate shape) input.valid.1 old) = old.stablePath :=
  (detachSelectedData input shape detach).rowOfEdge_retained old

theorem detachRowOfEdge_new (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (detach.candidate shape).datum
      ((detach.candidate shape).newSourceEdge sheet)) :
    detachRowOfEdge input shape detach ⟨(detach.candidate shape).newSourceEdge sheet, hSurvives⟩ =
      (detachNewOldEdge input shape detach sheet hSurvives).stablePath :=
  (detachSelectedData input shape detach).rowOfEdge_new sheet hSurvives

theorem detachRowOfEdge_eq_of_consecutive (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile)
    (first second : NonDanglingEdge (detach.candidate shape).datum)
    (hConsecutive : Consecutive (detach.candidate shape).datum first second) :
    detachRowOfEdge input shape detach first = detachRowOfEdge input shape detach second :=
  (detachSelectedData input shape detach).rowOfEdge_eq_of_consecutive first second hConsecutive

/-- The reverse geometric map on a detaching member's stable-row quotient. -/
noncomputable def detachStablePathDescend (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile) :
    StablePath (detach.candidate shape).datum → StablePath data :=
  (detachSelectedData input shape detach).stablePathDescend

@[simp] theorem detachStablePathDescend_mk (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile)
    (edge : NonDanglingEdge (detach.candidate shape).datum) :
    detachStablePathDescend input shape detach edge.stablePath =
      detachRowOfEdge input shape detach edge := rfl

theorem detachStablePathDescend_lift (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (path : StablePath data) :
    detachStablePathDescend input shape detach
        (detachStablePathLift input shape detach path) = path :=
  (detachSelectedData input shape detach).stablePathDescend_lift path

theorem detach_stablePathLift_injective (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    Function.Injective (detachStablePathLift input shape detach) :=
  (detachSelectedData input shape detach).stablePathLift_injective

/-- **A detaching member's geometric stable-row bijection.**  The forward map is
literally the retained-occurrence lift; no cardinality and no supplied row
correspondence enters. -/
noncomputable def detachStablePathEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) :
    StablePath data ≃ StablePath (detach.candidate shape).datum :=
  (detachSelectedData input shape detach).stablePathEquiv

@[simp] theorem detachStablePathEquiv_mk (input : W2SourceInput data star) (shape : Shape profile)
    (detach : DetachData profile) (edge : NonDanglingEdge data) :
    detachStablePathEquiv input shape detach edge.stablePath =
      (retainedEdge (detach.candidate shape) input.valid.1 edge).stablePath := rfl

@[simp] theorem detachStablePathEquiv_symm (input : W2SourceInput data star)
    (shape : Shape profile) (detach : DetachData profile)
    (path : StablePath (detach.candidate shape).datum) :
    (detachStablePathEquiv input shape detach).symm path =
      detachStablePathDescend input shape detach path :=
  (detachSelectedData input shape detach).stablePathEquiv_symm_apply path

/-! ## The joined member `M⁽³⁾` -/

/-- A fixed old surviving occurrence representing one regrown occurrence of
`M⁽³⁾`. -/
noncomputable def joinedNewOldEdge (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).newSourceEdge sheet)) : NonDanglingEdge data :=
  (joinedSelectedData input shape distinguished).newOldEdge sheet hSurvives

noncomputable def joinedRowOfEdge (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree)
    (edge : NonDanglingEdge (joinedCandidate profile distinguished).datum) :
    StablePath data :=
  (joinedSelectedData input shape distinguished).rowOfEdge edge

theorem joinedRowOfEdge_retained (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (old : NonDanglingEdge data) :
    joinedRowOfEdge input shape distinguished
        (retainedEdge (joinedCandidate profile distinguished) input.valid.1 old) =
      old.stablePath :=
  (joinedSelectedData input shape distinguished).rowOfEdge_retained old

theorem joinedRowOfEdge_new (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished sheet : Fin degree)
    (hSurvives : ¬ IsDangling (joinedCandidate profile distinguished).datum
      ((joinedCandidate profile distinguished).newSourceEdge sheet)) :
    joinedRowOfEdge input shape distinguished
        ⟨(joinedCandidate profile distinguished).newSourceEdge sheet, hSurvives⟩ =
      (joinedNewOldEdge input shape distinguished sheet hSurvives).stablePath :=
  (joinedSelectedData input shape distinguished).rowOfEdge_new sheet hSurvives

theorem joinedRowOfEdge_eq_of_consecutive (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree)
    (first second : NonDanglingEdge (joinedCandidate profile distinguished).datum)
    (hConsecutive : Consecutive (joinedCandidate profile distinguished).datum first second) :
    joinedRowOfEdge input shape distinguished first =
      joinedRowOfEdge input shape distinguished second :=
  (joinedSelectedData input shape distinguished).rowOfEdge_eq_of_consecutive first second
    hConsecutive

/-- The reverse geometric map on `M⁽³⁾`'s stable-row quotient. -/
noncomputable def joinedStablePathDescend (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree) :
    StablePath (joinedCandidate profile distinguished).datum → StablePath data :=
  (joinedSelectedData input shape distinguished).stablePathDescend

@[simp] theorem joinedStablePathDescend_mk (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree)
    (edge : NonDanglingEdge (joinedCandidate profile distinguished).datum) :
    joinedStablePathDescend input shape distinguished edge.stablePath =
      joinedRowOfEdge input shape distinguished edge := rfl

theorem joinedStablePathDescend_lift (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (path : StablePath data) :
    joinedStablePathDescend input shape distinguished
        (joinedStablePathLift input profile distinguished path) = path :=
  (joinedSelectedData input shape distinguished).stablePathDescend_lift path

theorem joined_stablePathLift_injective (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) :
    Function.Injective (joinedStablePathLift input profile distinguished) :=
  (joinedSelectedData input shape distinguished).stablePathLift_injective

/-- **`M⁽³⁾`'s geometric stable-row bijection.** -/
noncomputable def joinedStablePathEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) :
    StablePath data ≃ StablePath (joinedCandidate profile distinguished).datum :=
  (joinedSelectedData input shape distinguished).stablePathEquiv

@[simp] theorem joinedStablePathEquiv_mk (input : W2SourceInput data star) (shape : Shape profile)
    (distinguished : Fin degree) (edge : NonDanglingEdge data) :
    joinedStablePathEquiv input shape distinguished edge.stablePath =
      (retainedEdge (joinedCandidate profile distinguished) input.valid.1 edge).stablePath := rfl

@[simp] theorem joinedStablePathEquiv_symm (input : W2SourceInput data star)
    (shape : Shape profile) (distinguished : Fin degree)
    (path : StablePath (joinedCandidate profile distinguished).datum) :
    (joinedStablePathEquiv input shape distinguished).symm path =
      joinedStablePathDescend input shape distinguished path :=
  (joinedSelectedData input shape distinguished).stablePathEquiv_symm_apply path

end DraismaVargas.LocalCases.W2MkkRowDescent
