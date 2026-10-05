module

public import DraismaVargas.LocalCases.RetainedCoreModel

@[expose] public section

/-!
# The general-forest Euler count, and the relabeling receipt it closes

At a general expansion forest the count the terminal core model needs is
`keptClasses.card + p' = n' + keptSlots.card`
(`RetainedCut.RetainedExhausts`), not `keptClasses.card = refinedSpec.n`.  The
Euler transport it rests on is Part I's, formalized in
`DraismaVargas.LocalCases.PrunedContractedSpec` and
`DraismaVargas.LocalCases.TerminalExhausts`.

## What is proved

**`RetainedCut.RetainedExhausts` is a theorem, not a hypothesis.**  It is an
identity between four numbers of the **face** and the two numbers of the
specification; it does not mention `InputRefinementData.refinedSpec`, so it
does not pin the core count `n`, and §1 shows that it *is* the genus receipt
`SourceGenusMatches`.  Three facts prove it at any forest:

* `ClearedFace.SourceContractionTopology.genus_prunedSpec` -- the pruned
  contracted spec has genus `keptSlots - keptClasses + 1`;
* `genus_prunedSpec_eq_genus_sourceGraph` on
  `classCard_add_keptSlots_card` -- pruning does not change the genus, given a
  kept class and a connected quotient source;
* `TerminalExhausts.sourceGenusMatches_iff` -- the receipt is
  `p - n + 1 = genus sourceGraph`.

§2 specialises to the cubic model of the expansion
(`RequestedExpandedEndpoints.exists_expansionModel`).
`sourceGenusMatches_of_bigSpec`: the cubic model of a requested specification
of genus `g = p₀ - n₀` has `2 * g` core vertices and `3 * g` slots, so it
carries the receipt exactly when the request does; `hN : 0 < 2 * (p₀ - n₀)`
makes the truncated subtraction honest.  Hence
`retainedExhausts_of_expansion`: at that model the count follows from
`hKept`, `candidate.datum.Connected` and
`SourceGenusMatches (D.bigSpec spec₀ hN hL) candidate.datum` -- all three
already inside `RetainedRelabeling.CutRelabeling`'s binder.

§3 collects the reduction.  `cutRelabeling_of_expansion_of_injective`: at the
cubic model, the relabeling receipt `RetainedRelabeling.CutRelabeling` follows
from **an injective map on the refined core vertices satisfying the two
endpoint equations**, at every terminal face.  The slot bijection, the
orientation flag, the length equation, `hTwo` and the genus count are all
discharged.

## The hypotheses that remain explicit here

1. **The vertex map itself**, with its endpoint equations
   (`RetainedCoreModel.EndpointEquations`) and its injectivity.  These are
   supplied elsewhere: `RetainedVertexModel.vertexModel` gives the map with
   `endpointEquations` unconditional, and `RetainedClassInjectivity` gives the
   injectivity.  The map is
   `RetainedTraversal`'s row walk on the breakpoints, `RetainedFibre`'s
   `requestedClass` on the non-marker requested core vertices and the new split
   vertex of `RetainedCut.cutSpec` on a straddling marker
   (`RetainedStraddle.piecePos_one_eq_retPos_zero`); its injectivity is the
   general-forest form of `ClassInjectivity` §4.
2. **`hCond`, `hN`, `hL`** and everything `CutRelabeling` keeps inside its
   binder (core dictionary, `Faithful`, `Spanning`, `Connected`,
   `SourceGenusMatches`, the topology and the kept class).
3. §1 is stated for an arbitrary specification and an arbitrary face; it says
   nothing about which specifications admit a face at all.
   `TerminalExhausts.exists_sourceGenusMatches` is the non-vacuity of its
   hypothesis.

## Used by

`RetainedRelabeling.CutRelabeling`, and through
`RetainedRelabeling.nonempty_evenSubdivisionPencil_of_link'` the proof of
`DraismaVargas.Statement`.
-/

namespace DraismaVargas.LocalCases.RetainedExhausts

noncomputable section

open Utilities
open Utilities.Certificate
open Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.IteratedSplitRefinement
open Utilities.Subdivision.CoreExpansion
open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.RequestedExpandedEndpoints
open DraismaVargas.LocalCases.RetainedCut
open DraismaVargas.LocalCases.RetainedCoreModel
open DraismaVargas.LocalCases.RetainedRelabeling
open DraismaVargas.LocalCases.StrongRefinement
open DraismaVargas.LocalCases.TerminalExhausts
open DraismaVargas.LocalCases.TraversalPresentation

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {strong : StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}

section Face

variable {n₀ p₀ : ℕ} {D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀))}
  {spec₀ : SubdivisionGraph.Spec n₀ p₀} {hN : 0 < 2 * (p₀ - n₀)}
  {hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e}

/-! ## 1.  The Euler count, at a general forest -/

/-- **`RetainedCut.RetainedExhausts` is the genus receipt, and nothing else.**
The pruned contracted spec has genus `keptSlots - keptClasses + 1`
(`genus_prunedSpec`), pruning does not change the genus
(`genus_prunedSpec_eq_genus_sourceGraph`, on the count
`classCard_add_keptSlots_card` that `hKept` and connectedness supply), and
`SourceGenusMatches` says the quotient source has the genus `p - n + 1` of the
specification.  No interface, no dictionary and no forest enter:
`RetainedExhausts` is an identity between four numbers and does not mention
`InputRefinementData.refinedSpec`, so the count goes through verbatim at any
forest. -/
theorem retainedExhausts_of_sourceGenusMatches {n p : ℕ}
    (spec : SubdivisionGraph.Spec n p)
    (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hConnected : candidate.datum.Connected)
    (hGenus : SourceGenusMatches spec candidate.datum) :
    RetainedCut.RetainedExhausts topology n p := by
  have h1 := ClearedFace.SourceContractionTopology.genus_prunedSpec topology hKept
  have h2 := ClearedFace.SourceContractionTopology.genus_prunedSpec_eq_genus_sourceGraph
    topology hKept
    (ClearedFace.SourceContractionTopology.classCard_add_keptSlots_card
      topology hKept hConnected)
  have h3 := (sourceGenusMatches_iff spec candidate.datum).mp hGenus
  unfold RetainedCut.RetainedExhausts
  omega

/-! ## 2.  At the cubic model of the expansion -/

/-- **The cubic model carries the requested genus receipt.**  The expansion
gives the requested genus `g = p₀ - n₀` a core of `2 * g` vertices and `3 * g`
slots, so `3 * g - 2 * g = g`; `hN` makes the truncated subtraction honest by
forcing `n₀ < p₀`. -/
theorem sourceGenusMatches_of_bigSpec
    (hGenus : SourceGenusMatches (D.bigSpec spec₀ hN hL) candidate.datum) :
    SourceGenusMatches spec₀ candidate.datum := by
  rw [sourceGenusMatches_iff] at hGenus ⊢
  omega

/-- **`RetainedCut.RetainedExhausts` at the cubic model, discharged.**  It is a
theorem, not a receipt: everything it needs -- the kept class, connectedness
and `SourceGenusMatches` of the *cubic model* -- is already inside
`RetainedRelabeling.CutRelabeling`'s binder. -/
theorem retainedExhausts_of_expansion
    (topology : ClearedFace.SourceContractionTopology face)
    (hKept : (ClearedFace.SourceContractionTopology.keptClasses topology).Nonempty)
    (hConnected : candidate.datum.Connected)
    (hGenus : SourceGenusMatches (D.bigSpec spec₀ hN hL) candidate.datum) :
    RetainedCut.RetainedExhausts topology n₀ p₀ :=
  retainedExhausts_of_sourceGenusMatches spec₀ topology hKept hConnected
    (sourceGenusMatches_of_bigSpec hGenus)

end Face

/-! ## 3.  The relabeling receipt, reduced to an injective vertex map -/

section Headline

variable {n₀ p₀ : ℕ} {D : ExpansionData n₀ p₀ (2 * (p₀ - n₀)) (3 * (p₀ - n₀))}
  {spec₀ : SubdivisionGraph.Spec n₀ p₀} {hN : 0 < 2 * (p₀ - n₀)}
  {hL : ∀ e : Fin (3 * (p₀ - n₀)), D.bigCore.tail e ≠ D.bigCore.head e}

/-- **The relabeling receipt at the cubic model, reduced to an injective vertex
map.**

`RetainedCut.cutRelabeling_of_cutCoreModel` reduced
`RetainedRelabeling.CutRelabeling` to a `RefinementCore.CoreModel` on the
canonical cut; `RetainedCoreModel` supplied that model's slot bijection, its
orientation flag and its length equation; §2 discharges the genus count
`RetainedCut.RetainedExhausts`, which by
`RetainedCut.card_refinedVertex_eq_cutSpec_n` turns an injection into a
bijection; and `RetainedCut.carried_length_le_two` discharges `hTwo`.  What is
left of the receipt is exactly this binder: **an injective map on the refined
core vertices satisfying the two endpoint equations**, at every terminal face.

The binder is `RetainedRelabeling.CutRelabeling`'s own, verbatim, and the
conclusion is the `cut` hypothesis of
`RetainedRelabeling.nonempty_evenSubdivisionPencil_of_link'` at one datum. -/
theorem cutRelabeling_of_expansion_of_injective (hCond : D.Conditions spec₀.core)
    (H : ∀ (degree : ℕ) (coordinate : Type) [Fintype coordinate] [DecidableEq coordinate]
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
    RetainedRelabeling.CutRelabeling (D.bigSpec spec₀ hN hL) (expansionForest D) spec₀
      (RetainedIndexProducer.retainedIndex hCond hN hL) := by
  refine RetainedCut.cutRelabeling_of_cutCoreModel ?_
  intro degree coordinate _ _ tgt gdata wall cand strong coordinates iface dict
    hFaithful hSpanning hConnected hSource face topology hKept
  obtain ⟨rev, vertexModel, hInj, hEq⟩ := H degree coordinate tgt gdata wall cand
    strong coordinates iface dict hFaithful hSpanning hConnected hSource face topology hKept
  exact ⟨rev, ⟨RetainedCoreModel.coreModel_of_injective_of_exhausts iface face
    (RetainedIndexProducer.retainedIndex hCond hN hL) topology rev hKept
    (RetainedCut.carried_length_le_two hCond hN hL)
    (retainedExhausts_of_expansion topology hKept hConnected hSource)
    vertexModel hInj hEq⟩⟩

end Headline

/-! ## 4.  The count, concretely

No structure is introduced: `RetainedCut.RetainedExhausts` is an equation
between four natural numbers, and §1 and §2 are theorems about it.  The
arithmetic of §2 is evaluated here at genus `g = p₀ - n₀ = 4`, with `p₀ = 7`,
`n₀ = 3`: the cubic model then has `2 * 4 = 8` core vertices and `3 * 4 = 12`
slots. -/

example : (3 : ℕ) * (7 - 3) = 12 := rfl

example : (2 : ℕ) * (7 - 3) = 8 := rfl

/-- and the two genus computations agree: `12 - 8 + 1 = 7 - 3 + 1`. -/
example : ((12 : ℕ) : ℤ) - ((8 : ℕ) : ℤ) + 1 = ((7 : ℕ) : ℤ) - ((3 : ℕ) : ℤ) + 1 := by
  norm_num

end

end DraismaVargas.LocalCases.RetainedExhausts
