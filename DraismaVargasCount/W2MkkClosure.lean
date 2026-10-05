module

public import DraismaVargas.LocalCases.W2MkkArbitraryExit
public import DraismaVargas.LocalCases.W2MkkSelectedCensus
public import DraismaVargas.LocalCases.SheetRelabelIncidence

@[expose] public section

/-!
# The remote dictionary of case `{w2-r2-nd3-M-kk}`

Source: Draisma--Vargas Part I (arXiv:1909.12924), case `{w2-r2-nd3-M-kk}`, Figure 34 and
Equation (8).

`W2MkkArbitraryExit` states the exit for an arbitrary incoming `w2Mkk` cover on two named
hypotheses: the **remote stable-incidence dictionary** (`RemoteDictionary`, with its genus
receipt) and the **selected-class census** (`DetachCensus ∨ JoinedCensus`, the Base II.1/Base
II.2 dichotomy of Part I's Case `{w2-r2}`).  This module proves the first for every incoming
datum; the second is `W2MkkSelectedCensus`.  `W2MkkIncomingDenominator` consumes the remote
dictionary (`remoteEquivalence`, `remote_sourceGenus`).

## Why the remote dictionary is not case data

Figure 34's remote member lives over `W2MkkTransport.swapRelabeling …|>.apply`,
a branch-swapped copy of the incoming wall datum.  That copy is reached by an
actual `GluingDatum.SheetRelabeling`, and a sheet relabelling carries
*everything* the remote position needs:

* the branch-and-row dictionary, by `StableGraphIncidence.sheetRelabel` -- its
  `vertex` field is the relabelling's own source-vertex equivalence restricted
  to survivors, its `row` field is `SheetRelabelStable.stablePathEquiv`, and its
  `incidence` field is `StableGraphIncidence.incidenceCount_sheetRelabel`; and
* the source genus, by `GluingDatum.SheetRelabeling.sourceGraphLaplacianEquiv`,
  an adjacency-preserving equivalence of the two literal quotient-source graphs.

Both are stated for an arbitrary relabelling in `SheetRelabelIncidence`; here
they are instantiated at the M-kk branch swap.  The one input is the wall
datum's own connectedness, which `SecondEquation.W2SourceInput.valid` already
carries, so the dictionary costs no new hypothesis at all:
`W2MkkTransport.swapGauge` was built from the same `hConnected` and the same
relabelling.

## The selected-class census

`W2MkkSelectedCensus.selectedCensus_dichotomy` proves the Base II.1/Base II.2 dichotomy
`DetachCensus ∨ JoinedCensus` from the classifier's own payload, and
`W2MkkSelectedCensus.divalent_endpoints` precludes Base I on the incoming side,
so the two target-valency hypotheses go with it.  Composed with the exit of
`W2MkkArbitraryExit`, the two named hypotheses are therefore discharged, and what remains is
exactly the `w2Mkk` bundle: the profile, the M-kk `Shape`, the `background` field, the
full-dimensional presentation, the contraction forest and the wall input.  That composition
is not stated as a separate theorem here; `RegrowthBalances` uses both facts for the M-kk
balance at a regrowth.

## Main results

* `W2MkkClosure.remoteEquivalence`, `remote_sourceGenus`, `remoteDictionary`,
  `remoteDictionary_of_input` -- the remote dictionary, in the forms the exit, the
  `RemoteDictionary` predicate and `W2MkkIncomingDenominator` ask for.
-/

namespace DraismaVargas.LocalCases.W2MkkClosure

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open FullDimensionalSource
open W2MkkSourceCandidates

/-! ## §1  The remote dictionary and its genus receipt

The whole dictionary is `SheetRelabelIncidence` at `W2MkkTransport.swapRelabeling`.
Nothing below mentions Figure 34's members, the orientation, or the census. -/

section Remote

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  (profile : W2R2SourceProfile.SourceProfile data star block)

/-- **The branch swap as a stable-incidence equivalence.**  `W2MkkTransport.swapGauge`
already carries the stable rows and the whole natural matrix across the swap
through `LimitChainCore.Gauge`; this is the *branch* half, and it comes from the
same relabelling and the same connectedness. -/
noncomputable def remoteEquivalence (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    StableGraphIncidence.Equivalence data
      (W2MkkTransport.swapRelabeling profile other hOther).apply :=
  SheetRelabelIncidence.equivalence
    (W2MkkTransport.swapRelabeling profile other hOther) hConnected

/-- **The source genus is preserved by the branch swap.**  This needs no
connectedness: relabelling permutes occurrences and preserves every
quotient-source edge multiplicity. -/
theorem remote_sourceGenus (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    genus (W2MkkTransport.swapRelabeling profile other hOther).apply.sourceGraph =
      genus data.sourceGraph :=
  SheetRelabelIncidence.sourceGenus_eq (W2MkkTransport.swapRelabeling profile other hOther)

/-- **`W2MkkArbitraryExit.RemoteDictionary` is inhabited at every profile,
every orientation and every swapped sheet.**  This is the remote-dictionary hypothesis of the
exit in `W2MkkArbitraryExit`. -/
theorem remoteDictionary (hConnected : data.Connected) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    W2MkkArbitraryExit.RemoteDictionary (profile := profile) other hOther :=
  ⟨remoteEquivalence profile hConnected other hOther⟩

/-- The same, from a `W2SourceInput`, which is how the connectedness arrives in
every consumer: `W2SourceInput.valid` is the wall datum's own validity. -/
theorem remoteDictionary_of_input (input : W2SourceInput data star) (other : Fin degree)
    (hOther : (data.vertexPartition wall).Rel (pinSheet profile) other) :
    W2MkkArbitraryExit.RemoteDictionary (profile := profile) other hOther :=
  remoteDictionary profile input.valid.1 other hOther

end Remote


end DraismaVargas.LocalCases.W2MkkClosure
