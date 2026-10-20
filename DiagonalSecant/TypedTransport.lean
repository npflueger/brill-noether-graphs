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
`script_eq_pullScript`; §7 `pushDiv_prin_script`, `slot_sum`, `linear_equiv_pushed`; §8
`pencilTransport`.

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

/-! ## 1.  Rise-compatible target potentials -/

/-- A target potential `P` with integral slopes `s`, rising along every target edge by its
slope times the **realized integral length** of that edge (`PencilTransportProducer.RiseCompatible`,
on the typed realization). -/
def RiseCompatible (s : κ.target.edges → ℤ) (P : κ.target.V → ℤ) : Prop :=
  ∀ edge : κ.target.edges,
    P (edge : κ.target.V × κ.target.V).2 - P (edge : κ.target.V × κ.target.V).1 =
      s edge * ((realization (degenerateLength D small) κ hClosed).targetLength edge : ℤ)

/-- The integral tree slope with incidence `anchor − root` (`TreeMetricPotential.chipSlope`). -/
noncomputable def chipSlope (root anchor : κ.target.V) : κ.target.edges → ℤ :=
  TreeMetricPotential.chipSlope κ.data κ.fullDim.targetConnected κ.fullDim.targetGenus root anchor

/-- The tree potential integrating `chipSlope` against the realized target lengths (zeros
allowed). -/
noncomputable def chipPotential (root anchor : κ.target.V) : κ.target.V → ℤ :=
  TreeMetricPotential.chipPotential κ.data κ.fullDim.targetConnected κ.fullDim.targetGenus
    (realization (degenerateLength D small) κ hClosed).targetLength root anchor

/-- The chip potential is rise-compatible (`TreeMetricPotential.chipPotential_rise`). -/
theorem chip_riseCompatible (root anchor : κ.target.V) :
    RiseCompatible D small κ hClosed (chipSlope D κ root anchor)
      (chipPotential D small κ hClosed root anchor) := fun t ↦
  TreeMetricPotential.chipPotential_rise κ.data κ.fullDim.targetConnected κ.fullDim.targetGenus
    (realization (degenerateLength D small) κ hClosed).targetLength root anchor t

/-! ## 2.  The transport -/

/-- **The pushed fibres over any two target vertices are linearly equivalent**
(`PencilTransportProducer.linear_equiv_pushDivisor`): `pushed anchor − pushed root` is the
Laplacian of the small script descended from the big-side script whose value at the offset `o`
of a big slot is the row potential (the pull-back of `chipPotential root anchor`) at the oriented
position. -/
theorem linear_equiv_pushed (hCond : D.Conditions small.core) (root anchor : κ.target.V) :
    linear_equiv (small.scale k hk).graph
      (pushed D small hN hL k hk κ hClosed hScale root)
      (pushed D small hN hL k hk κ hClosed hScale anchor) :=
  -- The public §2–§7 with marked rows, proved in `CTTransport` (small side
  -- `pushed_sub_eq_rows`, big side `pushDiv_prin_script`, matched slot by slot by `slot_sum`).
  CTTransport.linear_equiv_pushed D small hN hL k hk κ hClosed hScale root anchor hCond

/-- **(T), typed.** The pushed fibres over any two target vertices are linearly equivalent on
`small.scale k`, from `D.Conditions small.core` alone. -/
theorem pencilTransport (hCond : D.Conditions small.core) (root anchor : κ.target.V) :
    linear_equiv (small.scale k hk).graph
      (pushed D small hN hL k hk κ hClosed hScale root)
      (pushed D small hN hL k hk κ hClosed hScale anchor) :=
  linear_equiv_pushed D small hN hL k hk κ hClosed hScale hCond root anchor

end DiagonalSecant.TypedTransport
