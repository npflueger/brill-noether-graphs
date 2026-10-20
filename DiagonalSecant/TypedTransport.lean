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

* the datum-level facts of `RowWalkKernel`: the dilation equation, the fibre difference as a
  pulled-back incidence (`sum_fibre_sub`), the row decomposition over any partition of the
  surviving edges (`sum_edges_eq_sum_rows`, here the **marked** rows), and the telescoping
  along a row;
* the row arithmetic of `RowAlgebra`: the row potential `RowAlgebra.value`, its values at the
  two ends, and the window computation `RowAlgebra.slot_sum`;
* the slot-value scripts of `SlotScriptKernel`: compatibility from the row ends
  (`compat_of_ends`), constancy on the fibres of `D.fib` (`eq_of_fib_eq`), and the linear
  equivalence by the descended script (`linear_equiv_of_slots`);
* `TreeMetricPotential.chipSlope`/`chipPotential` (the integral tree slope of incidence
  `anchor − root` and its potential, integrated against the realized target lengths);
* `GluingDatum.sourceEdgeIncidence_eq_localDegree_mul_targetEdgeIncidence` (the sheet-partition
  refinement equation), `PendantDivisorTransport.push`, `SubdivisionGraph.Spec` scripts and
  `pushDiv_prin_pullScript` of `Utilities.Subdivision.CoreExpansion`.

Twinned in the helper module `CTTransport` (they index by rows): §1 `RiseCompatible`,
`sourcePotential`, `edgeSlope`; the row data `rowStart`, `rowLen`, `rowSlope` and the walk
`rowVertex_isWalk`; §5 the realization of the row vertices (`realize_rowVertex`, from
`TypedImage.realize_address` and `realize_branch` at the two ends — the mark end included, since
a mark is a marked branch vertex); §6 the slot values `slotValue` on
`D.bigSpec (small.scale k)`, their compatibility `compat` at both ends of every slot, and
constancy of the core potential on contracted slots (`corePotential_contracted`); §7
`pushed_sub_eq_rows`, `linear_equiv_pushed`. This module states the result as
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
