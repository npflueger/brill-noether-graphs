import DraismaVargas.LocalCases.W2PStableLift

/-!
# Descending Figure 35's occurrences to old stable rows

A retained occurrence goes back to itself.  A regrown occurrence above `A₀`
goes to the old occurrence the census names; a regrown occurrence over a
background wall block goes to the old `t₂` occurrence there.  This is the
core's `SelectedData.rowOfEdge`, whose local consecutive checks — not an
assumed row correspondence — make it a map on stable classes.

Composing with `W2PStableLift.stablePathLift` gives an explicit geometric left
inverse, so the lift is injective; with its proved surjectivity this is the
geometric stable-row bijection `stablePathEquiv` of each member.
-/

namespace DraismaVargas.LocalCases.W2PRowDescent

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2PSourceCandidates
open W2PSurvival W2PStableLift

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- A fixed old surviving occurrence representing one regrown occurrence. -/
noncomputable def newOldEdge (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling member.candidate.datum
      (member.candidate.newSourceEdge sheet)) : NonDanglingEdge data :=
  (selectedData input census).newOldEdge sheet hSurvives

/-- Choose the unique retained preimage when there is one; otherwise the
occurrence is regrown and uses its fixed old representative. -/
noncomputable def rowOfEdge (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (edge : NonDanglingEdge member.candidate.datum) :
    StablePath data :=
  (selectedData input census).rowOfEdge edge

theorem rowOfEdge_retained (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (old : NonDanglingEdge data) :
    rowOfEdge input census (retainedEdge member.candidate input.valid.1 old) = old.stablePath :=
  (selectedData input census).rowOfEdge_retained old

theorem rowOfEdge_new (input : W2SourceInput data star) {member : MemberShape profile}
    (census : Census input member) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling member.candidate.datum (member.candidate.newSourceEdge sheet)) :
    rowOfEdge input census ⟨member.candidate.newSourceEdge sheet, hSurvives⟩ =
      (newOldEdge input census sheet hSurvives).stablePath :=
  (selectedData input census).rowOfEdge_new sheet hSurvives

theorem rowOfEdge_eq_of_consecutive (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member)
    (first second : NonDanglingEdge member.candidate.datum)
    (hConsecutive : Consecutive member.candidate.datum first second) :
    rowOfEdge input census first = rowOfEdge input census second :=
  (selectedData input census).rowOfEdge_eq_of_consecutive first second hConsecutive

/-! ## The geometric stable-row bijection -/

/-- The reverse geometric map on one member's stable-row quotient. -/
noncomputable def stablePathDescend (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member) :
    StablePath member.candidate.datum → StablePath data :=
  (selectedData input census).stablePathDescend

@[simp] theorem stablePathDescend_mk (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member)
    (edge : NonDanglingEdge member.candidate.datum) :
    stablePathDescend input census edge.stablePath = rowOfEdge input census edge := rfl

theorem stablePathDescend_lift (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member) (path : StablePath data) :
    stablePathDescend input census (stablePathLift input member path) = path :=
  (selectedData input census).stablePathDescend_lift path

theorem stablePathLift_injective (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member) :
    Function.Injective (stablePathLift input member) :=
  (selectedData input census).stablePathLift_injective

/-- **The member's geometric stable-row bijection.**  The forward map is
literally the retained-occurrence lift; no cardinality and no supplied row
correspondence enters. -/
noncomputable def stablePathEquiv (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member) :
    StablePath data ≃ StablePath member.candidate.datum :=
  (selectedData input census).stablePathEquiv

@[simp] theorem stablePathEquiv_mk (input : W2SourceInput data star)
    {member : MemberShape profile} (census : Census input member) (edge : NonDanglingEdge data) :
    stablePathEquiv input census edge.stablePath =
      (retainedEdge member.candidate input.valid.1 edge).stablePath := rfl

end DraismaVargas.LocalCases.W2PRowDescent
