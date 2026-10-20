module

public import DiagonalSecant.TypedImage
public import DiagonalSecant.CTTransport
public import DraismaVargasCount.PencilTransportProducer

@[expose] public section

/-!
# The pencil transport of a typed frame

The marked twin of (T) of `PencilTransportProducer` (`pencilTransport`): the pushed fibres of a
closed typed frame over any two target vertices are linearly equivalent on `small.scale k`.

## What is reused, and what is twinned

Reused verbatim (datum-free or datum-level):

* `PencilTransportProducer.ramp` and its telescoping `sum_window` (§1);
* `TreeMetricPotential.chipSlope`/`chipPotential` (the integral tree slope of incidence
  `anchor − root` and its potential, integrated against the realized target lengths);
* `GluingDatum.sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence` (the sheet-partition
  refinement equation), `PendantDivisorTransport.push`, `SubdivisionGraph.Spec` scripts and
  `pushDiv_prin_pullScript` of `Utilities.Subdivision.CoreExpansion`.

Twinned in the helper module `CTTransport` (they index by rows): §2 `sourcePotential`,
`edgeSlope`, `sourcePotential_rise`, `fibre_sub_eq`; §3 `sum_fibre_sub`, `sum_edges_eq_sum_rows` (the surviving occurrences grouped
by **marked** rows, `mem_orderedRow_iff`); §4 the row data `rowStart`, `rowLen`, `rowSlope`,
`rowValue`; §5 the realization of the row vertices (`realize_rowVertex`, from
`TypedImage.realize_address` and `realize_branch` at the two ends — the mark end included, since
a mark is a marked branch vertex); §6 the script `script` on `D.bigSpec (small.scale k)`, its
compatibility `compat` at both ends of every slot, constancy on contracted slots
(`corePotential_contracted`) and hence on every fibre of the contraction
(`script_eq_of_vertexMap_eq`, through the last clause of `ExpansionData.Conditions`), and
`script_eq_pullScript`; §7 `pushDiv_prin_script`, `slot_sum`, `linear_equiv_pushed`. This
module states the result as `pencilTransport`.

## The boundary term that is not there

In the tripod (`Tripod/RealisationProof.lean` §4, "the leg edges at the marks") the
marks were trivalent with a long leg, and the fibre had to be *slid* along the legs with a
correction term. Here a mark is a row **end** with no leg: the fibre over a target vertex is
pushed as it is, and the script is constant on the mark's big core vertex as on any other
label. So the typed transport is the public (T) with marked rows, and nothing more.
-/

namespace DiagonalSecant.TypedTransport

open DraismaVargas.Infrastructure DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.LocalCases DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count DraismaVargas.Count.MarkedCount DraismaVargas.Count.MarkedCountGeneral
open DraismaVargas.Count.DegenerateBigDivisor (degenerateLength)
open DiagonalSecant.TypedRows DiagonalSecant.TypedPlacement DiagonalSecant.TypedImage
open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Subdivision.CoreExpansion

variable {n p N Q m degree : ℕ} {mark : Fin m → Fin N} {types : Fin m → ℕ}
  (D : ExpansionData n p N Q) (small : Spec n p) (hN : 0 < N)
  (hL : ∀ e : Fin Q, D.bigCore.tail e ≠ D.bigCore.head e) (k : ℕ) (hk : 0 < k)
  (κ : TypedFrame D.bigCore mark types degree)
  (hClosed : Closed (degenerateLength D small) κ)
  (hScale : scale (degenerateLength D small) κ = k)

/-- **(T), typed.** The pushed fibres over any two target vertices are linearly equivalent on
`small.scale k`, from `D.Conditions small.core`: `pushed anchor − pushed root` is the Laplacian of
the small script descended from the big-side script whose value at the offset `o` of a big slot
is the row potential (the pull-back of `chipPotential root anchor`) at the oriented position
(`CTTransport.linear_equiv_pushed`). -/
theorem pencilTransport (hCond : D.Conditions small.core) (root anchor : κ.target.V) :
    linear_equiv (small.scale k hk).graph
      (pushed D small hN hL k hk κ hClosed hScale root)
      (pushed D small hN hL k hk κ hClosed hScale anchor) :=
  CTTransport.linear_equiv_pushed D small hN hL k hk κ hClosed hScale root anchor hCond

end DiagonalSecant.TypedTransport
