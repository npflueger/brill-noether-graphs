import DraismaVargas.LocalCases.RetainedExhausts

/-!
# The Statement's conclusion from the link and the vertex datum

The binders are those of
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one` and of
`RetainedRelabeling.nonempty_evenSubdivisionPencil_of_link'`.

## What is proved

One statement, twice: on the reduction side the route costs exactly **the
vertex datum**.  Given

* `link` -- `OuterWalk.TypeChangeLink` at every reached cover and prescribed
  move, verbatim from
  `RetainedRelabeling.nonempty_evenSubdivisionPencil_of_link'`; and
* `vertex` -- at every terminal face of the expansion model
  (`RequestedExpandedEndpoints.exists_expansionModel`), an injective map from
  the refined core vertices of the retained segment data to the core vertices
  of `RetainedCut.cutSpec`, satisfying the two endpoint equations
  `RetainedCoreModel.EndpointEquations` against the slot bijection
  `RetainedCoreModel.slotModel`,

the Statement's conclusion follows for every connected request of even genus at
least six.  §2 restates it with the two receipts pulled out in front of the
Statement's own four binders, so that it can be checked binder for binder
against the Statement.  Both `link` and `vertex` are supplied unconditionally
elsewhere (`NonTrivalentValencyTwoBaseOneLink.link_all`;
`RetainedVertexModel.vertexModel` with `RetainedClassInjectivity`), and
`RetainedClassInjectivity.nonempty_evenSubdivisionPencil` proves the Statement
by that route rather than through this file.

Everything else the reduction needs is inside: the canonical cut and its chain
(`RetainedCut`), the slot bijection and the length equation
(`RetainedCoreModel`), `hTwo` (`RetainedCut.carried_length_le_two`), and the
general-forest genus count (`RetainedExhausts.retainedExhausts_of_expansion`,
which turns an injection into a bijection through
`RetainedCut.card_refinedVertex_eq_cutSpec_n`).

## The hypotheses that remain explicit

1. **`link`** -- the type-changing exits, discharged unconditionally by
   `NonTrivalentValencyTwoBaseOneLink.link_all`.
2. **`vertex`** -- this file is a reduction, not a construction.  The map it
   asks for is described in `RetainedExhausts`; its injectivity is the
   general-forest form of `ClassInjectivity` §4.
   `RetainedVertexModel.vertexModel` (with its endpoint equations
   unconditional) and `RetainedClassInjectivity` (the injectivity) supply it,
   together giving `RetainedClassInjectivity.nonempty_evenSubdivisionPencil`
   with no hypothesis at all.
3. The theorems in this file are therefore stated **conditionally**, exactly
   as `RetainedRelabeling.nonempty_evenSubdivisionPencil_of_link'` is.

## Used by

The proof of `DraismaVargas.Statement` does not go through this file; its
`vertex`/`link` binders remain available for a caller that already has those
two receipts in some other shape.
-/

namespace DraismaVargas.LocalCases.RetainedStatement

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.OuterWalk
open DraismaVargas.LocalCases.RefinementCore
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.RetainedCut
open DraismaVargas.LocalCases.RetainedCoreModel
open DraismaVargas.LocalCases.RetainedExhausts
open DraismaVargas.LocalCases.RetainedRelabeling
open DraismaVargas.LocalCases.StableGraphIncidence
open DraismaVargas.LocalCases.StableSourceDarts
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TerminalExhausts
open DraismaVargas.LocalCases.TraversalPresentation

/-! ## 1.  The Statement's conclusion, on the link and the vertex datum -/

/-- **The Statement's conclusion for an arbitrary connected request, on the
link and the vertex datum.**

The binders `spec`, `hconn`, `hGenus`, `hEven` and the conclusion are
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one`'s
verbatim, and `link` is
`RetainedRelabeling.nonempty_evenSubdivisionPencil_of_link'`'s verbatim.  What
changes is the reduction-side receipt: where that theorem asks for the whole of
`RetainedRelabeling.CutRelabeling`, this one asks only for the **vertex datum**
-- an injective map on the refined core vertices satisfying the two endpoint
equations of `RetainedCoreModel.EndpointEquations`, at every terminal face of
the expansion model.  Everything else on the reduction side is discharged. -/
theorem nonempty_evenSubdivisionPencil_of_link_of_injective {n p : ℕ} (spec : Spec n p)
    (hconn : graph_connected spec.graph) (hGenus : 6 ≤ p + 1 - n)
    (hEven : Even (p + 1 - n))
    (link : ∀ m : ℕ, p + 1 - n = 2 * m + 2 →
      ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (vertex : ∀ {n₀ p₀ : ℕ} (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e)
      (hCond : D.Conditions spec₀.core)
      (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
      (tgt : CFGraph.{0}) (gdata : GluingDatum tgt degree) (wall : tgt.V)
      (cand : Candidate tgt degree gdata wall)
      (strong : StrongPresentation cand.datum coordinate)
      (coordinates : coordinate → ℚ)
      (iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
        (expansionForest D))
      (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface),
      Faithful dict → Spanning dict → cand.datum.Connected →
      SourceGenusMatches (D.bigSpec spec₀ hN hL) cand.datum →
      ∀ (face : ClearedFace cand strong.toPresentation coordinates)
        (topology : ClearedFace.SourceContractionTopology face)
        (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty),
        ∃ (rev : SlotIndex iface face → Bool)
          (vertexModel : RefinementCore.RefinedVertex (Retained.segmentData iface face
              (RetainedIndexProducer.retainedIndex hCond hN hL)) →
            Fin (RetainedCut.cutSpec iface face
              (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept).n),
          Function.Injective vertexModel ∧
            RetainedCoreModel.EndpointEquations iface face
              (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
              (RetainedCut.carried_length_le_two hCond hN hL) vertexModel) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  RetainedRelabeling.nonempty_evenSubdivisionPencil_of_link' spec hconn hGenus hEven link
    (fun spec₀ D hN hL hCond ↦
      cutRelabeling_of_expansion_of_injective hCond
        (fun degree coordinate _ _ tgt gdata wall cand strong coordinates iface dict ↦
          vertex spec₀ D hN hL hCond degree coordinate tgt gdata wall cand strong
            coordinates iface dict))

/-! ## 2.  The receipts in front of the Statement's binders -/

/-- **The two receipts pulled out in front of the Statement's own four
binders**, exactly as `StatementFromLink.nonempty_evenSubdivisionPencil_of_receipts`
and `RetainedRelabeling.nonempty_evenSubdivisionPencil_of_receipts'` do.  What
follows `link` and `vertex` is
`DraismaVargas.nonempty_evenSubdivisionPencil_ceil_half_genus_add_one`'s
statement, binder for binder and conclusion for conclusion, so this typechecks
as a binder-for-binder check against the Statement. -/
theorem nonempty_evenSubdivisionPencil_of_receipts''
    (link : ∀ m : ℕ,
      ∀ K : CubicDartGraph (Dart (CaterpillarSeed.seed m).candidate.datum)
        (BranchVertex (CaterpillarSeed.seed m).candidate.datum),
      CubicDartGraph.Reaches (seedGraph m) K →
      ∀ (mv : K.MoveData)
        (arrival : OuterWalk.FacetArrival (m + 2) K (seedLabel m) (seedLabel m mv.base))
        (wd : OuterWalk.WallData arrival), OuterWalk.TypeChangeLink mv wd)
    (vertex : ∀ {n₀ p₀ : ℕ} (spec₀ : Spec n₀ p₀)
      (D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀)))
      (hN : 0 < 2 * (p₀ - n₀))
      (hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e)
      (hCond : D.Conditions spec₀.core)
      (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
      (tgt : CFGraph.{0}) (gdata : GluingDatum tgt degree) (wall : tgt.V)
      (cand : Candidate tgt degree gdata wall)
      (strong : StrongPresentation cand.datum coordinate)
      (coordinates : coordinate → ℚ)
      (iface : InputInterface (D.bigSpec spec₀ hN hL) strong.toPresentation coordinates
        (expansionForest D))
      (dict : CoreDictionary (D.bigSpec spec₀ hN hL) strong iface),
      Faithful dict → Spanning dict → cand.datum.Connected →
      SourceGenusMatches (D.bigSpec spec₀ hN hL) cand.datum →
      ∀ (face : ClearedFace cand strong.toPresentation coordinates)
        (topology : ClearedFace.SourceContractionTopology face)
        (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty),
        ∃ (rev : SlotIndex iface face → Bool)
          (vertexModel : RefinementCore.RefinedVertex (Retained.segmentData iface face
              (RetainedIndexProducer.retainedIndex hCond hN hL)) →
            Fin (RetainedCut.cutSpec iface face
              (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept).n),
          Function.Injective vertexModel ∧
            RetainedCoreModel.EndpointEquations iface face
              (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
              (RetainedCut.carried_length_le_two hCond hN hL) vertexModel)
    {n p : ℕ} (spec : Spec n p) (hconn : graph_connected spec.graph)
    (hGenus : 6 ≤ p + 1 - n) (hEven : Even (p + 1 - n)) :
    Nonempty (DraismaVargas.SubdivisionPencil spec ((p + 2 - n) / 2 + 1)) :=
  nonempty_evenSubdivisionPencil_of_link_of_injective spec hconn hGenus hEven
    (fun m _ ↦ link m) vertex

end

end DraismaVargas.LocalCases.RetainedStatement
