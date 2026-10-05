module

-- The banana model: definitions, geometry, elementary structure
public import Bananas.Basics.BananaBasics
public import Bananas.Basics.BananaGeometry
public import Bananas.Basics.BananaSameStrandLemma
public import Bananas.Basics.Definitions
public import Bananas.Basics.DegreeOneRepresentatives
public import Bananas.Basics.GraphIsoCuts
public import Bananas.Basics.MarkedIso
public import Bananas.Basics.ReducedCutCriterion
public import Bananas.Basics.SegmentScript
public import Bananas.Basics.TwoEdgeCuts

-- The Jacobian presentation and torsion slopes (Prop 2.14)
public import Bananas.Jacobian.BananaJacobianDiagonal
public import Bananas.Jacobian.BananaJacobianLatticeReduction
public import Bananas.Jacobian.BananaJacobianLeftJustification
public import Bananas.Jacobian.BananaJacobianPresentation
public import Bananas.Jacobian.BananaJacobianProposition214
public import Bananas.Jacobian.BananaJacobianQuotientCertificate
public import Bananas.Jacobian.BananaJacobianReducedBridge
public import Bananas.Jacobian.BananaJacobianReducedInjectivity
public import Bananas.Jacobian.BananaJacobianReducedUniqueness
public import Bananas.Jacobian.BananaJacobianReductionTermination
public import Bananas.Jacobian.BananaJacobianSurjectivity
public import Bananas.Jacobian.BananaTorsionSlopes

-- Transmission, torsion orders, rank witnesses
public import Bananas.Transmission.ChainBalanceArithmetic
public import Bananas.Transmission.ChainTwoLoopsSameLeft
public import Bananas.Transmission.ChainTwoLoopsSameRight
public import Bananas.Transmission.CycleTorsionOrder
public import Bananas.Transmission.EqualTorsionKGeneral
public import Bananas.Transmission.ExactTorsionAPI
public import Bananas.Transmission.FarMarkAPI
public import Bananas.Transmission.FarMarkNegativeAPI
public import Bananas.Transmission.GenericFarWitness
public import Bananas.Transmission.GenericRankWitness
public import Bananas.Transmission.KGeneralBNGeneral
public import Bananas.Transmission.KGeneralGonality
public import Bananas.Transmission.KGeneralSwap
public import Bananas.Transmission.LengthTwoTorsion
public import Bananas.Transmission.MidpointTorsion
public import Bananas.Transmission.MixedTorsionChainBalance
public import Bananas.Transmission.MixedTorsionChains
public import Bananas.Transmission.NonrecurrenceDisjoint
public import Bananas.Transmission.NonrecurrenceWitness
public import Bananas.Transmission.RankDeltaDuality
public import Bananas.Transmission.RankDetermining
public import Bananas.Transmission.RankZeroSupport
public import Bananas.Transmission.RankZeroVertexBridge
public import Bananas.Transmission.RankZeroWitness
public import Bananas.Transmission.TorsionIso
public import Bananas.Transmission.TorsionOrderExact
public import Bananas.Transmission.TorsionOrderTwoGeneral
public import Bananas.Transmission.TransmissionAPI
public import Bananas.Transmission.TransmissionBasics
public import Bananas.Transmission.TransmissionBridge
public import Bananas.Transmission.TwoVertexGenusOneTorsion

-- Same-strand marks: endpoint/interior analysis (Sections 3-4)
public import Bananas.SameStrand.BananaEndpointDelta
public import Bananas.SameStrand.BananaEndpointRankCriterion
public import Bananas.SameStrand.EndpointBlock
public import Bananas.SameStrand.EndpointCardinality
public import Bananas.SameStrand.EndpointInversions
public import Bananas.SameStrand.NSMClassification
public import Bananas.SameStrand.NSMCrossWitness
public import Bananas.SameStrand.NSMFullClassification
public import Bananas.SameStrand.NSMSecondCrossWitness
public import Bananas.SameStrand.SameStrand
public import Bananas.SameStrand.SameStrandEndpointNegative
public import Bananas.SameStrand.SameStrandInteriorNegative
public import Bananas.SameStrand.Semibreak

-- Cross and one-off marks: inversion growth (Section 4)
public import Bananas.CrossOneOff.AffineInversionFinite
public import Bananas.CrossOneOff.AffineReduction
public import Bananas.CrossOneOff.BananaCrossOneOffDeltaFamilies
public import Bananas.CrossOneOff.BananaOneOffDeltaFamilies
public import Bananas.CrossOneOff.CrossOneOffArithmetic
public import Bananas.CrossOneOff.CrossOneOffBlock
public import Bananas.CrossOneOff.CrossOneOffCorrectedInversion
public import Bananas.CrossOneOff.CrossOneOffCorrectedKGeneral
public import Bananas.CrossOneOff.CrossOneOffDelta
public import Bananas.CrossOneOff.CrossOneOffExtendedBlock
public import Bananas.CrossOneOff.CrossOneOffFiniteCountSol
public import Bananas.CrossOneOff.CrossOneOffFiniteRows
public import Bananas.CrossOneOff.CrossOneOffFiring
public import Bananas.CrossOneOff.CrossOneOffForcedCountArithmetic
public import Bananas.CrossOneOff.CrossOneOffForcedCountLengthTwo
public import Bananas.CrossOneOff.CrossOneOffInversions
public import Bananas.CrossOneOff.CrossOneOffKGeneral
public import Bananas.CrossOneOff.CrossOneOffPeriodSeparation
public import Bananas.CrossOneOff.CrossOneOffResidueDelta
public import Bananas.CrossOneOff.CrossOneOffShortStrandPeriod
public import Bananas.CrossOneOff.CrossOneOffTransmission
public import Bananas.CrossOneOff.CrossStrandNegative
public import Bananas.CrossOneOff.CrossStrandSupport
public import Bananas.CrossOneOff.CrossingInversionCount
public import Bananas.CrossOneOff.LengthTwoCross
public import Bananas.CrossOneOff.LengthTwoCrossBasePoint
public import Bananas.CrossOneOff.LengthTwoCrossMonotonicity
public import Bananas.CrossOneOff.OneOffInversionLowerBound
public import Bananas.CrossOneOff.OneOffKGeneral
public import Bananas.CrossOneOff.OneOffMultipleRows
public import Bananas.CrossOneOff.OneOffPeriodBound
public import Bananas.CrossOneOff.OneOffPositiveRows
public import Bananas.CrossOneOff.OneOffRefinedInversion
public import Bananas.CrossOneOff.OneOffTransmission
public import Bananas.CrossOneOff.QuadraticInversionGrowth
public import Bananas.CrossOneOff.SignChangingInversions

-- Theta graphs: the genus-two exact theory
public import Bananas.Theta.EvenlyMarkedThetaKGeneral
public import Bananas.Theta.ThetaArithmetic
public import Bananas.Theta.ThetaBoundarySubmodularity
public import Bananas.Theta.ThetaChipEval
public import Bananas.Theta.ThetaCoordinateRigidity
public import Bananas.Theta.ThetaCounterexampleNormalForm
public import Bananas.Theta.ThetaExactTorsion
public import Bananas.Theta.ThetaExactTorsionRelabel
public import Bananas.Theta.ThetaExceptionalArithmetic
public import Bananas.Theta.ThetaGenusTwoCornerSum
public import Bananas.Theta.ThetaGenusTwoTwistIdentities
public import Bananas.Theta.ThetaInvTauCorrection
public import Bananas.Theta.ThetaInversionCount
public import Bananas.Theta.ThetaInversionFiniteSum
public import Bananas.Theta.ThetaJacobian
public import Bananas.Theta.ThetaJacobianPresentation
public import Bananas.Theta.ThetaKGeneralClassification
public import Bananas.Theta.ThetaKGeneralCoordinates
public import Bananas.Theta.ThetaLattice
public import Bananas.Theta.ThetaMoment
public import Bananas.Theta.ThetaNegativeDivisorClasses
public import Bananas.Theta.ThetaNegativeDivisorClassesBoundary
public import Bananas.Theta.ThetaNegativeDivisorClassesTerminal
public import Bananas.Theta.ThetaNonrecurrence
public import Bananas.Theta.ThetaPrefix
public import Bananas.Theta.ThetaPrincipal
public import Bananas.Theta.ThetaReflectionRank
public import Bananas.Theta.ThetaResidue
public import Bananas.Theta.ThetaTorsionAPI
public import Bananas.Theta.ThetaTransmissionAudit
public import Bananas.Theta.ThetaTransmissionCases

-- Wedge sums and their k-general classification
public import Bananas.Wedge.KGeneralWedgeGenerality
public import Bananas.Wedge.OnceMarkedWedgeGenerality
public import Bananas.Wedge.OppositeWedgeKGeneralClassification
public import Bananas.Wedge.OppositeWedgeRigidity
public import Bananas.Wedge.SameFactorWedgeKGeneral
public import Bananas.Wedge.SameFactorWedgePeriod
public import Bananas.Wedge.SameFactorWedgeRight
public import Bananas.Wedge.SameFactorWedgeSubmodularity
public import Bananas.Wedge.TwoVertexWedgeSubmodularity
public import Bananas.Wedge.VertexWedgeAssociativity
public import Bananas.Wedge.WedgeKGeneralClassification
public import Bananas.Wedge.WedgeKGeneralConverse
public import Bananas.Wedge.WedgeKGeneralSymmetric
public import Bananas.Wedge.WedgePeriodRecurrence
public import Bananas.Wedge.WedgeSubmodularity
public import Bananas.Wedge.WedgeTorsionRestriction
public import Bananas.Wedge.ZeroGenusWedge

-- Bridgeless low-genus classification and corrected theorems
public import Bananas.Classification.BridgelessDegreeOneClasses
public import Bananas.Classification.BridgelessGenusOneTopology
public import Bananas.Classification.BridgelessGenusTwoClassification
public import Bananas.Classification.BridgelessGenusTwoCornerAlgebra
public import Bananas.Classification.BridgelessGenusTwoDegreeShape
public import Bananas.Classification.BridgelessGenusTwoKGeneralReduction
public import Bananas.Classification.BridgelessGenusTwoNonrecurrence
public import Bananas.Classification.BridgelessGenusTwoPseudocore
public import Bananas.Classification.BridgelessGenusTwoTopology
public import Bananas.Classification.CorrectedBananaSimple
public import Bananas.Classification.CorrectedBananaTheorem117
public import Bananas.Classification.CorrectedBananaTorsion
public import Bananas.Classification.CorrectedMidpointKGeneral
public import Bananas.Classification.GenusOneKGeneral
public import Bananas.Classification.GenusOneRankDelta
public import Bananas.Classification.GenusTwoDegreeTwo
public import Bananas.Classification.GenusTwoReduction
public import Bananas.Classification.PointedGenusOneKGeneral
public import Bananas.Classification.SciWeierstrass
public import Bananas.Classification.WeierstrassPartition

-- Section 5 and Section 6 paper spines
public import Bananas.Sections.SectionFiveDefinitions
public import Bananas.Sections.SectionFiveInversionBound
public import Bananas.Sections.SectionFiveStatements
public import Bananas.Sections.SectionFiveSymmetries
public import Bananas.Sections.SectionFiveTransports
public import Bananas.Sections.SectionSixBananaCorollary
public import Bananas.Sections.SectionSixChainConclusion
public import Bananas.Sections.SectionSixDefinitions
public import Bananas.Sections.SectionSixFoundation

-- Worked examples and audits
public import Bananas.Examples.ExampleBngChain
public import Bananas.Examples.MechanicalAPIAudit

-- Downstream applications to named results in the tropical Brill--Noether
-- literature.  These consume the Section 6 chain theorems as black boxes; they
-- are not part of the twice-marked banana paper, which is why they are indexed here
-- and not in `TwiceMarkedBananas.lean`.
public import Bananas.ChainOfLoops.CDPR
public import Bananas.ChainOfLoops.BridgeChainTransport
public import Bananas.ChainOfLoops.CommonPeriodGonality
public import Bananas.ChainOfLoops.Highlights

@[expose] public section
