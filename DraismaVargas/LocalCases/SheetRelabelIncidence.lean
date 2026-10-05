module

public import DraismaVargas.LocalCases.StableGraphIncidence

@[expose] public section

/-!
# A sheet relabelling as a stable-incidence equivalence, with its genus receipt

Source: Draisma--Vargas Part I, §5.2 (inherited properties): the induced edge
labelling of a limit and the labellings compatible at a contracted edge.

`StableGraphIncidence.sheetRelabel` builds the three fields of
`StableGraphIncidence.Equivalence` out of a `GluingDatum.SheetRelabeling`'s own
source-vertex, source-edge and stable-path maps.  What the limit-matrix chain
actually consumes at a *remote* Figure position is not that structure but the
pair

* `Nonempty (StableGraphIncidence.Equivalence data relabeling.apply)`, the
  branch-and-row dictionary; and
* `genus relabeling.apply.sourceGraph = genus data.sourceGraph`, the source
  genus receipt,

because a presentation at a remote position is presented against the *incoming*
datum's stable graph and needs the outgoing datum's source genus to be the
incoming one.  Both halves hold for an **arbitrary** compatible global sheet
relabelling, with no case data whatsoever: the first from
`StableGraphIncidence.sheetRelabel` and the source's own connectedness, the
second from `GluingDatum.SheetRelabeling.sourceGraphLaplacianEquiv`, which is
an adjacency-preserving vertex equivalence of the two literal quotient-source
graphs.

So the file is short on purpose.  It exists because the two halves are needed
case by case at the point of use (`W3FourStableIncidence.positionOneDictionary`
and `positionTwoDictionary` are exactly this pair), and because
`W2MkkArbitraryExit.RemoteDictionary` is literally the first half at the M-kk
branch swap.  Nothing below mentions a wall, a star, a profile or a member.

## Main results

* `SheetRelabelIncidence.equivalence` -- the dictionary itself, a `def`, so
  that callers who want the maps and not merely their existence get them;
* `SheetRelabelIncidence.nonempty_equivalence` -- its `Nonempty` form, which is
  the shape the remote-position clauses ask for;
* `SheetRelabelIncidence.sourceGenus_eq` -- the genus receipt;
* `SheetRelabelIncidence.dictionary_and_sourceGenus` -- the two together, which
  is what a remote position consumes.
-/

namespace DraismaVargas.LocalCases.SheetRelabelIncidence

open DraismaVargas.Infrastructure

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- **A compatible global sheet relabelling is a stable-incidence
equivalence.**  This is `StableGraphIncidence.sheetRelabel`, named here so that
the remote-position clauses of the limit-matrix chain have one general lemma to
point at instead of rebuilding the three fields per case. -/
noncomputable def equivalence (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) :
    StableGraphIncidence.Equivalence data relabeling.apply :=
  StableGraphIncidence.sheetRelabel relabeling hConnected

/-- The dictionary in the `Nonempty` form that a full-dimensional presentation
clause at a remote position asks for. -/
theorem nonempty_equivalence (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) :
    Nonempty (StableGraphIncidence.Equivalence data relabeling.apply) :=
  ⟨equivalence relabeling hConnected⟩

/-- **The genus receipt.**  Relabelling is an adjacency-preserving equivalence
of the literal quotient-source graphs, so it preserves cyclomatic genus.  No
connectedness is needed for this half. -/
theorem sourceGenus_eq (relabeling : data.SheetRelabeling) :
    genus relabeling.apply.sourceGraph = genus data.sourceGraph :=
  relabeling.sourceGraphLaplacianEquiv.genus_eq

/-- **The pair a remote position consumes.** -/
theorem dictionary_and_sourceGenus (relabeling : data.SheetRelabeling)
    (hConnected : data.Connected) :
    Nonempty (StableGraphIncidence.Equivalence data relabeling.apply) ∧
      genus relabeling.apply.sourceGraph = genus data.sourceGraph :=
  ⟨nonempty_equivalence relabeling hConnected, sourceGenus_eq relabeling⟩

/-- The same pair from the full validity predicate, which is how the datum's
connectedness usually arrives. -/
theorem dictionary_and_sourceGenus_of_valid (relabeling : data.SheetRelabeling)
    (hValid : data.Valid) :
    Nonempty (StableGraphIncidence.Equivalence data relabeling.apply) ∧
      genus relabeling.apply.sourceGraph = genus data.sourceGraph :=
  dictionary_and_sourceGenus relabeling hValid.1

end DraismaVargas.LocalCases.SheetRelabelIncidence
