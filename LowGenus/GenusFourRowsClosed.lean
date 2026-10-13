module

public import LowGenus.GenusFourCubicCoverage
public import LowGenus.GenusFourRow095Closed
public import LowGenus.GenusFourRow096Closed
public import LowGenus.GenusFourRow097Closed
public import LowGenus.GenusFourRow098Closed
public import LowGenus.GenusFourRow099Closed
public import LowGenus.GenusFourRow100Closed

@[expose] public section

/-!
# The six closed cubic genus-four rows

This is the small concrete ledger consumed by the public genus-four
pseudocore reduction.  All six rows have readable closed-face proofs.  The
kernel-checked generated certificates for rows 096, 099 and 100
(`LowGenus.Generated.GenusFourClosedRows`) prove the same three statements
independently; they are kept as checks and are not imported here.
-/

set_option autoImplicit false

namespace AtanasovRanganathan.GenusFourRowsClosed

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ContractionForestCensusGeneral
open AtanasovRanganathan.Configurations
open AtanasovRanganathan.GenusFourCubicAtlas
open AtanasovRanganathan.GenusFourCubicCoverage

/-- All six public cubic genus-four rows carry degree-three pencils throughout
their genus-preserving closed orthants. -/
theorem rowClosedCoverage : RowClosedCoverage := by
  intro row hRow length hForest hNotLoopy
  simp only [atlas, List.mem_cons, List.not_mem_nil, or_false] at hRow
  rcases hRow with rfl | rfl | rfl | rfl | rfl | rfl
  · exact GenusFourRow095Closed.row095_closed length hForest hNotLoopy
  · exact GenusFourRow096Closed.row096_closed length hForest hNotLoopy
  · rw [faceSpec_eq_censusSpec]
    exact LowGenus.GenusFourRow097Closed.bnExists_closed
      length hForest hNotLoopy
  · exact GenusFourRow098Closed.bnExists_closed length hForest hNotLoopy
  · exact GenusFourRow099Closed.row099_closed length hForest hNotLoopy
  · exact GenusFourRow100Closed.row100_closed length hForest hNotLoopy

/-- The public classifier and the six-row ledger cover every connected
loopless cubic genus-four core. -/
theorem cubicClosedCoverage :
    GenusFourPseudocoreCoverage.CubicClosedCoverage :=
  cubicClosedCoverage_of_rows rowClosedCoverage

/-- Every connected finite graph of genus four carries a degree-three
rank-one divisor, using only public modules. -/
theorem genusFourRankOneExistence : GenusFourRankOneExistence :=
  GenusFourPseudocoreCoverage.genusFourRankOneExistence_of_cubicClosedCoverage
    cubicClosedCoverage

end AtanasovRanganathan.GenusFourRowsClosed
