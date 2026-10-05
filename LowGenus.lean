module

public import LowGenus.AtanasovRanganathanProgram
public import LowGenus.AtanasovRanganathanExistence
public import LowGenus.ClosedConstructionTail
public import LowGenus.ConfigurationBananaDoubleChip
public import LowGenus.ConfigurationBananaTail
public import LowGenus.ConfigurationChippedTriangle
public import LowGenus.ConfigurationCommon
public import LowGenus.ConfigurationEleven
public import LowGenus.ConfigurationFive
public import LowGenus.ConfigurationMarkedCommon
public import LowGenus.ConfigurationMarkedRow
public import LowGenus.ConfigurationMarkedThree
public import LowGenus.ConfigurationMarkedTripod
public import LowGenus.ConfigurationSeven
public import LowGenus.ConfigurationThree
public import LowGenus.ConfigurationThreeChain
public import LowGenus.ConfigurationTwo
public import LowGenus.GenusFourRow096Pencil
public import LowGenus.GenusFourRow097Closed
public import LowGenus.GenusFourRow097Contractions
public import LowGenus.GenusFourRow098Closed
public import LowGenus.GenusFiveClosedOrbit
public import LowGenus.GenusFiveConfigurations
public import LowGenus.GenusFiveConstructions
public import LowGenus.GenusFiveTwoPoleData
public import LowGenus.GenusFiveTwoPole
public import LowGenus.GenusFiveTwoPoleClosed
public import LowGenus.GenusFiveCoreAtlas
public import LowGenus.GenusFiveCubicAtlas
public import LowGenus.GenusFiveCanonicalClassifier
public import LowGenus.GenusFiveCubicCoverage
public import LowGenus.GenusFiveBridgeRows
public import LowGenus.GenusFivePseudocoreCoverage
public import LowGenus.GenusFourCanonicalClassifier
public import LowGenus.GenusFourCubicCoverage
public import LowGenus.GenusFourPseudocoreCoverage
public import LowGenus.GenusFourRowsClosed
public import LowGenus.GenusFiveRow05
public import LowGenus.GenusFiveRow05Symmetry
public import LowGenus.GenusFiveRow06
public import LowGenus.GenusFiveRow08
public import LowGenus.GenusFiveRow08ChamberOne
public import LowGenus.GenusFiveRow08ChamberThree
public import LowGenus.GenusFiveRow08ChamberTwo
public import LowGenus.GenusFiveRow08Symmetry
public import LowGenus.GenusFiveRow09
public import LowGenus.GenusFiveRow10
public import LowGenus.GenusFiveRow10ChamberOne
public import LowGenus.GenusFiveRow10ChamberTwo
public import LowGenus.GenusFiveRow10Symmetry
public import LowGenus.GenusFiveRow11
public import LowGenus.GenusFiveRow12
public import LowGenus.GenusFiveRow12Tripod
public import LowGenus.GenusFiveRow12Guarding
public import LowGenus.GenusFiveRow14
public import LowGenus.GenusFiveRow15
public import LowGenus.GenusFiveRow16
public import LowGenus.GuardingSet
public import LowGenus.Highlights
public import LowGenus.Infrastructure.CoreRelabelingClosed
public import LowGenus.Infrastructure.TrivalentExpansionClosed
public import LowGenus.LowGenusExistence

@[expose] public section

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
