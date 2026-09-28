import DraismaVargas.LocalCases.W2M1kStableLift

/-!
# Descending Figure 33's occurrences to old stable rows

Source: Draisma--Vargas Part I, Case {w2-r2-nd3-M-1k}, Figure 33.

A retained occurrence goes back to itself.  A regrown occurrence above `A₀`
goes to the old occurrence `W2M1kStableGraph`'s census names -- `e₁` over its
own sheet and `e₂` on the residual class for `M⁽²⁾` (`W2M1kStableLift.dividedRep`),
`e₃` for `M⁽³⁾` -- and a regrown occurrence over a background wall block goes to
the old `star.edge 0` occurrence there.  This is the core's
`LimitChainCore.SelectedData.rowOfEdge`, whose local consecutive checks -- not
an assumed row correspondence -- make it a map on stable classes.

Composing with `W2M1kStableLift`'s lift gives an explicit geometric left
inverse, so the lift is injective; with its proved surjectivity this is the
geometric stable-row bijection `stablePathEquiv` of each member.

Member 2 of Figure 33 is not transported here: it is obtained by instantiating
these definitions at `W2M1kSwapped.swappedData`, exactly as
`W2M1kStableLift`'s docstring records.

`M⁽¹⁾` is absent, and for the reason `W2M1kStableLift.leaf_not_wallCandidate`
records: the leaf member has no `LimitChainCore.WallCandidate`, hence no
`SelectedData`, hence no core row descent.
-/

namespace DraismaVargas.LocalCases.W2M1kRowDescent

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2M1kSourceCandidates W2M1kLeaves
open W2M1kStableGraph
open W2M1kStableLift

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## The divided member `M⁽²⁾` -/

/-- A fixed old surviving occurrence representing one regrown occurrence of
`M⁽²⁾`. -/
noncomputable def dividedNewOldEdge (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).newSourceEdge sheet)) : NonDanglingEdge data :=
  (dividedSelectedData input shape divided).newOldEdge sheet hSurvives

/-- Choose the unique retained preimage when there is one; otherwise the
occurrence is regrown and uses its fixed old representative. -/
noncomputable def dividedRowOfEdge (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile)
    (edge : NonDanglingEdge (DividedData.candidate shape divided).datum) : StablePath data :=
  (dividedSelectedData input shape divided).rowOfEdge edge

theorem dividedRowOfEdge_retained (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (old : NonDanglingEdge data) :
    dividedRowOfEdge input shape divided
        (retainedEdge (DividedData.candidate shape divided) input.valid.1 old) =
      old.stablePath :=
  (dividedSelectedData input shape divided).rowOfEdge_retained old

theorem dividedRowOfEdge_new (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (DividedData.candidate shape divided).datum
      ((DividedData.candidate shape divided).newSourceEdge sheet)) :
    dividedRowOfEdge input shape divided
        ⟨(DividedData.candidate shape divided).newSourceEdge sheet, hSurvives⟩ =
      (dividedNewOldEdge input shape divided sheet hSurvives).stablePath :=
  (dividedSelectedData input shape divided).rowOfEdge_new sheet hSurvives

theorem dividedRowOfEdge_eq_of_consecutive (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (first second : NonDanglingEdge (DividedData.candidate shape divided).datum)
    (hConsecutive : Consecutive (DividedData.candidate shape divided).datum first second) :
    dividedRowOfEdge input shape divided first = dividedRowOfEdge input shape divided second :=
  (dividedSelectedData input shape divided).rowOfEdge_eq_of_consecutive first second hConsecutive

/-- The reverse geometric map on `M⁽²⁾`'s stable-row quotient. -/
noncomputable def dividedStablePathDescend (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    StablePath (DividedData.candidate shape divided).datum → StablePath data :=
  (dividedSelectedData input shape divided).stablePathDescend

@[simp] theorem dividedStablePathDescend_mk (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (edge : NonDanglingEdge (DividedData.candidate shape divided).datum) :
    dividedStablePathDescend input shape divided edge.stablePath =
      dividedRowOfEdge input shape divided edge := rfl

theorem dividedStablePathDescend_lift (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) :
    dividedStablePathDescend input shape divided
        (dividedStablePathLift input shape divided path) = path :=
  (dividedSelectedData input shape divided).stablePathDescend_lift path

theorem divided_stablePathLift_injective (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    Function.Injective (dividedStablePathLift input shape divided) :=
  (dividedSelectedData input shape divided).stablePathLift_injective

/-- **`M⁽²⁾`'s geometric stable-row bijection.**  The forward map is literally
the retained-occurrence lift; no cardinality and no supplied row correspondence
enters. -/
noncomputable def dividedStablePathEquiv (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) :
    StablePath data ≃ StablePath (DividedData.candidate shape divided).datum :=
  (dividedSelectedData input shape divided).stablePathEquiv

@[simp] theorem dividedStablePathEquiv_mk (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile) (edge : NonDanglingEdge data) :
    dividedStablePathEquiv input shape divided edge.stablePath =
      (retainedEdge (DividedData.candidate shape divided) input.valid.1 edge).stablePath := rfl

@[simp] theorem dividedStablePathEquiv_symm (input : W2SourceInput data star)
    (shape : Shape profile) (divided : DividedData profile)
    (path : StablePath (DividedData.candidate shape divided).datum) :
    (dividedStablePathEquiv input shape divided).symm path =
      dividedStablePathDescend input shape divided path :=
  (dividedSelectedData input shape divided).stablePathEquiv_symm_apply path

/-! ## The joined member `M⁽³⁾` -/

/-- A fixed old surviving occurrence representing one regrown occurrence of
`M⁽³⁾`. -/
noncomputable def joinedNewOldEdge (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).newSourceEdge sheet)) : NonDanglingEdge data :=
  (joinedSelectedData input shape geometry).newOldEdge sheet hSurvives

noncomputable def joinedRowOfEdge (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall)
    (edge : NonDanglingEdge (joinedCandidate star geometry).datum) : StablePath data :=
  (joinedSelectedData input shape geometry).rowOfEdge edge

theorem joinedRowOfEdge_retained (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (old : NonDanglingEdge data) :
    joinedRowOfEdge input shape geometry
        (retainedEdge (joinedCandidate star geometry) input.valid.1 old) = old.stablePath :=
  (joinedSelectedData input shape geometry).rowOfEdge_retained old

theorem joinedRowOfEdge_new (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).newSourceEdge sheet)) :
    joinedRowOfEdge input shape geometry
        ⟨(joinedCandidate star geometry).newSourceEdge sheet, hSurvives⟩ =
      (joinedNewOldEdge input shape geometry sheet hSurvives).stablePath :=
  (joinedSelectedData input shape geometry).rowOfEdge_new sheet hSurvives

theorem joinedRowOfEdge_eq_of_consecutive (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall)
    (first second : NonDanglingEdge (joinedCandidate star geometry).datum)
    (hConsecutive : Consecutive (joinedCandidate star geometry).datum first second) :
    joinedRowOfEdge input shape geometry first = joinedRowOfEdge input shape geometry second :=
  (joinedSelectedData input shape geometry).rowOfEdge_eq_of_consecutive first second hConsecutive

/-- The reverse geometric map on `M⁽³⁾`'s stable-row quotient. -/
noncomputable def joinedStablePathDescend (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall) :
    StablePath (joinedCandidate star geometry).datum → StablePath data :=
  (joinedSelectedData input shape geometry).stablePathDescend

@[simp] theorem joinedStablePathDescend_mk (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall)
    (edge : NonDanglingEdge (joinedCandidate star geometry).datum) :
    joinedStablePathDescend input shape geometry edge.stablePath =
      joinedRowOfEdge input shape geometry edge := rfl

theorem joinedStablePathDescend_lift (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) :
    joinedStablePathDescend input shape geometry
        (joinedStablePathLift input profile geometry path) = path :=
  (joinedSelectedData input shape geometry).stablePathDescend_lift path

theorem joined_stablePathLift_injective (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) :
    Function.Injective (joinedStablePathLift input profile geometry) :=
  (joinedSelectedData input shape geometry).stablePathLift_injective

/-- **`M⁽³⁾`'s geometric stable-row bijection.** -/
noncomputable def joinedStablePathEquiv (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) :
    StablePath data ≃ StablePath (joinedCandidate star geometry).datum :=
  (joinedSelectedData input shape geometry).stablePathEquiv

@[simp] theorem joinedStablePathEquiv_mk (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall)
    (edge : NonDanglingEdge data) :
    joinedStablePathEquiv input shape geometry edge.stablePath =
      (retainedEdge (joinedCandidate star geometry) input.valid.1 edge).stablePath := rfl

@[simp] theorem joinedStablePathEquiv_symm (input : W2SourceInput data star)
    (shape : Shape profile) (geometry : GlobalM1k.Geometry data wall)
    (path : StablePath (joinedCandidate star geometry).datum) :
    (joinedStablePathEquiv input shape geometry).symm path =
      joinedStablePathDescend input shape geometry path :=
  (joinedSelectedData input shape geometry).stablePathEquiv_symm_apply path

end DraismaVargas.LocalCases.W2M1kRowDescent
