import LowGenus.AtanasovRanganathanProgram
import LowGenus.AtanasovRanganathanExistence
import LowGenus.ClosedConstructionTail
import LowGenus.ConfigurationBananaDoubleChip
import LowGenus.ConfigurationBananaTail
import LowGenus.ConfigurationChippedTriangle
import LowGenus.ConfigurationCommon
import LowGenus.ConfigurationEleven
import LowGenus.ConfigurationFive
import LowGenus.ConfigurationMarkedCommon
import LowGenus.ConfigurationMarkedRow
import LowGenus.ConfigurationMarkedThree
import LowGenus.ConfigurationMarkedTripod
import LowGenus.ConfigurationReservoirChain
import LowGenus.ConfigurationReservoirPair
import LowGenus.ConfigurationSeven
import LowGenus.ConfigurationThree
import LowGenus.ConfigurationThreeChain
import LowGenus.ConfigurationTwo
import LowGenus.GenusFourRow096Pencil
import LowGenus.GenusFourRow097Closed
import LowGenus.GenusFourRow097Contractions
import LowGenus.GenusFourRow098Closed
import LowGenus.GenusFiveClosedOrbit
import LowGenus.GenusFiveConfigurations
import LowGenus.GenusFiveConstructions
import LowGenus.GenusFiveCoreAtlas
import LowGenus.GenusFiveCubicAtlas
import LowGenus.GenusFiveCanonicalClassifier
import LowGenus.GenusFiveCubicCoverage
import LowGenus.GenusFiveBridgeRows
import LowGenus.GenusFivePseudocoreCoverage
import LowGenus.GenusFourCanonicalClassifier
import LowGenus.GenusFourCubicCoverage
import LowGenus.GenusFourPseudocoreCoverage
import LowGenus.GenusFourRowsClosed
import LowGenus.GenusFiveRow01
import LowGenus.GenusFiveRow02
import LowGenus.GenusFiveRow03
import LowGenus.GenusFiveRow04
import LowGenus.GenusFiveRow05
import LowGenus.GenusFiveRow05Symmetry
import LowGenus.GenusFiveRow06
import LowGenus.GenusFiveRow07
import LowGenus.GenusFiveRow08
import LowGenus.GenusFiveRow08ChamberOne
import LowGenus.GenusFiveRow08ChamberThree
import LowGenus.GenusFiveRow08ChamberTwo
import LowGenus.GenusFiveRow08Symmetry
import LowGenus.GenusFiveRow09
import LowGenus.GenusFiveRow10
import LowGenus.GenusFiveRow10ChamberOne
import LowGenus.GenusFiveRow10ChamberTwo
import LowGenus.GenusFiveRow10Symmetry
import LowGenus.GenusFiveRow11
import LowGenus.GenusFiveRow12
import LowGenus.GenusFiveRow12Tripod
import LowGenus.GenusFiveRow12Guarding
import LowGenus.GenusFiveRow13
import LowGenus.GenusFiveRow14
import LowGenus.GenusFiveRow15
import LowGenus.GenusFiveRow16
import LowGenus.GuardingOrbit
import LowGenus.GuardingSet
import LowGenus.Highlights
import LowGenus.Infrastructure.CoreRelabelingClosed
import LowGenus.Infrastructure.TrivalentExpansionClosed
import LowGenus.LowGenusExistence

/-! # The Atanasov--Ranganathan low-genus formalization

Root module for the `LowGenus` library: the formalization of the
Atanasov--Ranganathan existence theorem in genera at most five. It builds on
the generic chip-firing, subdivision, and transmission theory of the
`Utilities` library.

Fifteen generated cover modules -- `GenusFiveRow03FixedCover`,
`GenusFiveRow14FixedCover`, the five-module row-04 chain and the eight-module
row-06 chain -- are not imported here. They are retained as independent
generated checks alongside the readable proofs used by the main library.

`GenusFiveClosedCover` supplies the affine-cover semantics for those generated
certificates and is outside the dependency closure of
`brillNoetherExistenceThroughFive`.

Add an import line above whenever a module is added under `LowGenus/`, or
`lake build LowGenus` will silently skip it. -/
