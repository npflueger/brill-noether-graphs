module

public import DraismaVargas.LocalCases.W3Nd2IncomingSheetClasses
public import DraismaVargas.LocalCases.StablePathContraction
public import DraismaVargas.LocalCases.W4IncomingCensus

@[expose] public section

/-!
# Every r0 background block at the selected incoming nd2 wall of Case {w3}

Source: Draisma--Vargas Part I, Case {w3-r0}, read on the actual incoming datum
exactly as Case {w3-r1-nd2} (Figure 31) is read by
`W3Nd2IncomingSheetClasses`.  The template for this step is
`M11IncomingBackground`, and two cautions from it apply here: background wall
blocks need not be singletons, and equality of relations alone does not
identify the stored representative functions of a sheet partition.

## What is proved

Every wall block other than the distinguished one (`background ≠
input.distinguishedBlock`) has vanishing local ramification at the merged
wall, by `ThirdEquation.W3SourceInput.localRamification_eq_zero_of_ne` (the
trivalent wall carries its single unit of change on exactly one block, with
*no* split branch, so this needs no extra case analysis the way
`W2RankObstructions.other_localRamification_eq_zero` does at a divalent wall).
Forest additivity descends this to vanishing local ramification at *both*
original endpoints, at every sheet in the block
(`background_localRamification_endpoints_eq_zero`).

At the **divalent** original endpoint this pins down, for every source vertex
in the block, the exact dichotomy of `{w3-r0}`: either the vertex is fully
dangling (a literal singleton sheet class), or it has non-dangling valency
two, in which case its class equals the class of *every* surviving adjacent
occurrence -- in particular the contracted occurrence's class, whenever it
survives there (`background_divalent_dichotomy`, specialised to the actual
incoming contraction as `background_dichotomy_of_left_divalent` /
`background_dichotomy_of_right_divalent` according to
`W3Nd2IncomingTargetPlacement.endpoint_valencies`). This is proved **without**
assuming the block is a singleton: the second alternative is exactly the
non-singleton case, and it genuinely occurs (a pass-through vertex whose two
surviving occurrences -- one of them possibly the contracted one -- both
carry its whole class).

## What is not attempted, and why

`M11IncomingBackground` additionally classifies the *other* endpoint (there,
always divalent too) and the contracted-edge partition as `JoinedOnBlock` /
`DiscreteOnBlock` of the *whole* merged wall block, by an induction along the
alternating chain `ContractionFibre.join_rel_iff_altChain` that transfers
zero ramification into an edge-partition equality at *each* hop, using
`StableLocalProperties.edgePartition_rel_iff_of_divalent_localRamification_zero`
at whichever endpoint the hop lands on.

That transfer lemma is stated for a **divalent** target vertex only, and it has
no analogue for a trivalent one (Part I's Case {w3-r0} itself only discusses
the divalent endpoint `u`, never the trivalent `v`).  Consequently a hop of the
alternating chain that lands on the trivalent endpoint cannot be transferred by
that lemma, and a whole-block `JoinedOnBlock`/`DiscreteOnBlock` classification
at the trivalent endpoint, or of the contracted-edge partition as a whole, is
**not proved here**.

## The whole-block census holds nevertheless

A relation-shaped statement covering an arbitrary background block at both
endpoints does hold: `W3Nd2IncomingNormalization.background_whole_block_census`
proves it.  M11's *trichotomy shape*, classifying all three partitions as
`JoinedOnBlock`/`DiscreteOnBlock` in one of M11's three patterns, is
unavailable here: a background block built from one trivalent-side vertex whose
two survivors are both external is genuinely consistent, giving `k` dangling
divalent-side singletons, `k` contracted-occurrence blocks and one
trivalent-side block, so `ContractionForest` reads `k + 1 = k + 1`.

But a census does hold, and that configuration is an instance of it.  On every
background block, every occurrence incident to the **divalent** endpoint -- the
contracted one and both retained ones -- carries that endpoint partition's own
sheet relation, by
`StableLocalProperties.edgePartition_block_eq_of_divalent_localRamification_zero`,
which needs only the divalent endpoint.  The contracted occurrence and the
divalent endpoint partition therefore induce the same block count, and
`ContractionForest` forces the trivalent endpoint partition to induce exactly
one: it is `JoinedOnBlock` on the whole block.  The transfer lemma is used once,
at the divalent endpoint, with no alternating-chain induction, so no hop ever
lands on the trivalent vertex and the obstruction above does not arise.

A joined/discrete flag for the **divalent** side is not derived, and nothing
downstream needs it.

The vertex-level dichotomy proved in this file remains correct and useful; it is
just not the strongest available statement.

`PartitionNormalization` (representative-safe normalization of the stored
representatives) is a separate step and is not attempted here either.

## The `AnyBlock` forms

`background ≠ input.distinguishedBlock` is used at exactly one line, to obtain
`(contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0`.
Every statement of the `Contraction` section below is therefore also available
in the `AnyBlock` namespace with that vanishing as the hypothesis instead, and
with neither the `ThreeStar` nor the `W3SourceInput` occurring anywhere (the
two-orientation dispatch keeps the star as an explicit argument, since
`W3Nd2IncomingTargetPlacement.endpoint_valencies` is what needs it).  The
statements of the `Contraction` section are one-line wrappers around the
`AnyBlock` forms.

This is the generalisation a case with **two** `r = 1` blocks structurally
requires: there is then no single distinguished block to be different from, and
the background condition `background ∉ {A, B}` is again exactly a vanishing
local ramification.
-/

namespace DraismaVargas.LocalCases.W3Nd2IncomingBackground

open DraismaVargas.Infrastructure
open GraphContraction GluingContraction ContractionFibre ContractionRamification
open W4Assembly W4StableSource StableLocalProperties NonDanglingValency
open ThirdEquation W3R1SourceProfile FullDimensionalSource WallDegeneration
open W3Nd2IncomingTargetPlacement

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}

section Dichotomy

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fullDim : FullDimensionalSourcePresentation data coordinate)

include fullDim

/-- **Case `{w3-r0}` of the local properties, at an arbitrary divalent target
vertex.** A vanishing local ramification at
a divalent vertex forces the canonical source vertex there to be either fully
dangling -- a literal singleton sheet class -- or of non-dangling valency
two, in which case its class equals the class of *every* surviving adjacent
occurrence. No hypothesis that the vertex is a singleton is assumed: the
second alternative is the genuinely non-singleton case: background wall blocks
need not be singletons. -/
theorem background_divalent_dichotomy
    (place : target.V) (hDivalent : (GluingDatum.incidentEdges place).card = 2)
    (sheet : Fin degree)
    (hZero : data.localRamification place ((data.vertexPartition place).toBlock sheet) = 0) :
    (nonDanglingValency data (data.sourceEndpoint place sheet) = 0 ∧
        (data.vertexPartition place).block sheet = {sheet}) ∨
      (nonDanglingValency data (data.sourceEndpoint place sheet) = 2 ∧
        ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
          Incident data edge (data.sourceEndpoint place sheet) →
          (data.edgePartition edge.1.1).block edge.1.2 =
            (data.vertexPartition place).block sheet) := by
  classical
  have hAbove : (data.sourceEndpoint place sheet).1.1 = place := rfl
  have hZero' : data.localRamification (data.sourceEndpoint place sheet).1.1
      ⟨(data.sourceEndpoint place sheet).1.2, (data.sourceEndpoint place sheet).2⟩ = 0 := hZero
  have hLe := NonDanglingValency.nonDanglingValency_le_of_localRamification_zero data
    (data.sourceEndpoint place sheet) hZero'
  rw [hAbove, hDivalent] at hLe
  norm_num at hLe
  have hNe := NonDanglingValency.nonDanglingValency_ne_one data fullDim.valid.1
    (data.sourceEndpoint place sheet)
  have hCases : nonDanglingValency data (data.sourceEndpoint place sheet) = 0 ∨
      nonDanglingValency data (data.sourceEndpoint place sheet) = 2 := by
    have hLeNat : nonDanglingValency data (data.sourceEndpoint place sheet) ≤ 2 := by
      exact_mod_cast hLe
    omega
  rcases hCases with hND | hND
  · exact Or.inl ⟨hND,
      W3Nd2IncomingSheetClasses.inactive_endpoint_block_local data fullDim place sheet hND⟩
  · refine Or.inr ⟨hND, ?_⟩
    intro edge hSurvives hIncident
    have h := W4IncomingCensus.block_eq_of_survives_nd2_r0 data fullDim.danglingEdgeNoGlue
      (data.sourceEndpoint place sheet) hND hZero' edge hSurvives hIncident
    rw [hAbove] at h
    rwa [(data.vertexPartition place).block_eq_of_rel
      ((data.vertexPartition place).rel_repr_right sheet)]

end Dichotomy

section AnyBlockContraction

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)

/-! ### The `r = 0` census at *any* wall block of vanishing local ramification

The statements below are the ones the rest of this file proves, with the
hypothesis `background ≠ input.distinguishedBlock` replaced by the *conclusion*
that hypothesis was used, at exactly one line, to obtain:

```
(hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
```

`W3SourceInput.localRamification_eq_zero_of_ne` supplies `hZero` from
`background ≠ input.distinguishedBlock` in one step, so the statements of the
`Contraction` section are one-line wrappers around these.

This is the generalisation Case {w2-r1} structurally requires: with **two** `r = 1`
blocks `A` and `B` there is no single `input.distinguishedBlock` to be
different from, and the background condition is `background ∉ {A, B}` -- which
is again exactly a vanishing local ramification.  Neither the `ThreeStar` nor
the `W3SourceInput` occurs in any statement of this namespace, so a divalent
wall reaches them too. -/
namespace AnyBlock

include fullDim hForest

/-- Vanishing local ramification of a wall block descends to both original
endpoints, at every sheet in the block.  Forest additivity is the only input;
neither the wall star nor a source input occurs. -/
theorem background_localRamification_endpoints_eq_zero
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    data.localRamification a ((data.vertexPartition a).toBlock sheet) = 0 ∧
      data.localRamification b ((data.vertexPartition b).toBlock sheet) = 0 := by
  classical
  let wallData := contractDatum data hc hab hOne
  let wall : (contract target hab hOne).V := ⟨a, hab⟩
  let root : Fin degree := background.1
  have hWallRel : (wallData.vertexPartition wall).Rel root sheet := by
    have hPartition : wallData.vertexPartition wall = mergedPartition data a b := by
      dsimp only [wallData, wall]
      exact contractDatum_vertexPartition_merge data hc hab hOne
    rw [hPartition]
    exact hSheet
  have hZeroAtRoot : localRamificationAt wallData wall root = 0 :=
    (localRamificationAt_block wallData wall background).trans hZero
  have hZeroAtSheet : localRamificationAt wallData wall sheet = 0 :=
    (localRamificationAt_congr wallData wall hWallRel).symm.trans hZeroAtRoot
  exact StablePathContraction.endpoint_localRamification_eq_zero
    data hc hab hOne fullDim.valid hForest sheet hZeroAtSheet

/-- **`{w3-r0}` at the actual incoming contraction, left-divalent
orientation**, at any wall block of vanishing local ramification. -/
theorem background_dichotomy_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    (nonDanglingValency data (data.sourceEndpoint a sheet) = 0 ∧
        (data.vertexPartition a).block sheet = {sheet}) ∨
      (nonDanglingValency data (data.sourceEndpoint a sheet) = 2 ∧
        ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
          Incident data edge (data.sourceEndpoint a sheet) →
          (data.edgePartition edge.1.1).block edge.1.2 =
            (data.vertexPartition a).block sheet) :=
  background_divalent_dichotomy data fullDim a hLeftDivalent sheet
    (background_localRamification_endpoints_eq_zero data hc hab hOne fullDim hForest
      hZero sheet hSheet).1

/-- **`{w3-r0}` at the actual incoming contraction, right-divalent
orientation**, at any wall block of vanishing local ramification. -/
theorem background_dichotomy_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    (nonDanglingValency data (data.sourceEndpoint b sheet) = 0 ∧
        (data.vertexPartition b).block sheet = {sheet}) ∨
      (nonDanglingValency data (data.sourceEndpoint b sheet) = 2 ∧
        ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
          Incident data edge (data.sourceEndpoint b sheet) →
          (data.edgePartition edge.1.1).block edge.1.2 =
            (data.vertexPartition b).block sheet) :=
  background_divalent_dichotomy data fullDim b hRightDivalent sheet
    (background_localRamification_endpoints_eq_zero data hc hab hOne fullDim hForest
      hZero sheet hSheet).2

/-- **The two orientations at once.**  The wall star enters only through
`W3Nd2IncomingTargetPlacement.endpoint_valencies`, which decides which original
endpoint is the divalent one; it is an explicit argument here and no source
input is used. -/
theorem background_dichotomy
    (wallStar : ThreeStar (contract target hab hOne) ⟨a, hab⟩)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hZero : (contractDatum data hc hab hOne).localRamification ⟨a, hab⟩ background = 0)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    ((nonDanglingValency data (data.sourceEndpoint a sheet) = 0 ∧
          (data.vertexPartition a).block sheet = {sheet}) ∨
        (nonDanglingValency data (data.sourceEndpoint a sheet) = 2 ∧
          ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
            Incident data edge (data.sourceEndpoint a sheet) →
            (data.edgePartition edge.1.1).block edge.1.2 =
              (data.vertexPartition a).block sheet)) ∨
      ((nonDanglingValency data (data.sourceEndpoint b sheet) = 0 ∧
            (data.vertexPartition b).block sheet = {sheet}) ∨
          (nonDanglingValency data (data.sourceEndpoint b sheet) = 2 ∧
            ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
              Incident data edge (data.sourceEndpoint b sheet) →
              (data.edgePartition edge.1.1).block edge.1.2 =
                (data.vertexPartition b).block sheet)) := by
  rcases endpoint_valencies data hc hab hOne fullDim wallStar with
    ⟨hLeftDivalent, _, _, _⟩ | ⟨_, hRightDivalent, _, _⟩
  · exact Or.inl (background_dichotomy_of_left_divalent data hc hab hOne fullDim hForest
      hLeftDivalent hZero sheet hSheet)
  · exact Or.inr (background_dichotomy_of_right_divalent data hc hab hOne fullDim hForest
      hRightDivalent hZero sheet hSheet)

end AnyBlock

end AnyBlockContraction

section Contraction

variable {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation data coordinate)
  (hForest : ContractionForest data a b contracted)
  {star : ThreeStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W3SourceInput (contractDatum data hc hab hOne) star)

include fullDim hForest input

/-- Zero ramification of a background wall block descends to both original
endpoints, at every sheet in the block. Unlike the template of Case {w2}
(`M11IncomingBackground`), there is
no `selected`/`profile` pair to supply separately: the trivalent wall carries
its single unit of change on exactly one block
(`ThirdEquation.W3SourceInput.exists_unique_localRamification`), namely
`input.distinguishedBlock`, with no split branch. -/
theorem background_localRamification_endpoints_eq_zero
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    data.localRamification a ((data.vertexPartition a).toBlock sheet) = 0 ∧
      data.localRamification b ((data.vertexPartition b).toBlock sheet) = 0 :=
  AnyBlock.background_localRamification_endpoints_eq_zero data hc hab hOne fullDim hForest
    (input.localRamification_eq_zero_of_ne hBackground) sheet hSheet

/-- **`{w3-r0}` at the actual incoming contraction, left-divalent orientation.**
Every source vertex above `a` belonging to a background wall block is either
a dangling singleton, or has non-dangling valency two with its class equal to
that of every surviving adjacent occurrence -- background blocks are not
assumed to be singletons. -/
theorem background_dichotomy_of_left_divalent
    (hLeftDivalent : (GluingDatum.incidentEdges a).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    (nonDanglingValency data (data.sourceEndpoint a sheet) = 0 ∧
        (data.vertexPartition a).block sheet = {sheet}) ∨
      (nonDanglingValency data (data.sourceEndpoint a sheet) = 2 ∧
        ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
          Incident data edge (data.sourceEndpoint a sheet) →
          (data.edgePartition edge.1.1).block edge.1.2 =
            (data.vertexPartition a).block sheet) :=
  AnyBlock.background_dichotomy_of_left_divalent data hc hab hOne fullDim hForest
    hLeftDivalent (input.localRamification_eq_zero_of_ne hBackground) sheet hSheet

/-- **`{w3-r0}` at the actual incoming contraction, right-divalent
orientation.** The mirror of `background_dichotomy_of_left_divalent`. -/
theorem background_dichotomy_of_right_divalent
    (hRightDivalent : (GluingDatum.incidentEdges b).card = 2)
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    (nonDanglingValency data (data.sourceEndpoint b sheet) = 0 ∧
        (data.vertexPartition b).block sheet = {sheet}) ∨
      (nonDanglingValency data (data.sourceEndpoint b sheet) = 2 ∧
        ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
          Incident data edge (data.sourceEndpoint b sheet) →
          (data.edgePartition edge.1.1).block edge.1.2 =
            (data.vertexPartition b).block sheet) :=
  AnyBlock.background_dichotomy_of_right_divalent data hc hab hOne fullDim hForest
    hRightDivalent (input.localRamification_eq_zero_of_ne hBackground) sheet hSheet

/-- **The two orientations at once**, read off
`W3Nd2IncomingTargetPlacement.endpoint_valencies`: whichever original
endpoint of the contracted occurrence is divalent, `{w3-r0}`'s dichotomy holds
there for every background wall block. -/
theorem background_dichotomy
    {background : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩}
    (hBackground : background ≠ input.distinguishedBlock)
    (sheet : Fin degree)
    (hSheet : (mergedPartition data a b).Rel background.1 sheet) :
    ((nonDanglingValency data (data.sourceEndpoint a sheet) = 0 ∧
          (data.vertexPartition a).block sheet = {sheet}) ∨
        (nonDanglingValency data (data.sourceEndpoint a sheet) = 2 ∧
          ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
            Incident data edge (data.sourceEndpoint a sheet) →
            (data.edgePartition edge.1.1).block edge.1.2 =
              (data.vertexPartition a).block sheet)) ∨
      ((nonDanglingValency data (data.sourceEndpoint b sheet) = 0 ∧
            (data.vertexPartition b).block sheet = {sheet}) ∨
          (nonDanglingValency data (data.sourceEndpoint b sheet) = 2 ∧
            ∀ edge : data.SourceEdge, ¬ IsDangling data edge →
              Incident data edge (data.sourceEndpoint b sheet) →
              (data.edgePartition edge.1.1).block edge.1.2 =
                (data.vertexPartition b).block sheet)) :=
  AnyBlock.background_dichotomy data hc hab hOne fullDim hForest star
    (input.localRamification_eq_zero_of_ne hBackground) sheet hSheet

end Contraction

end DraismaVargas.LocalCases.W3Nd2IncomingBackground
