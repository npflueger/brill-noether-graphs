import DraismaVargas.LocalCases.W4IncomingGlobalMatching
import DraismaVargas.LocalCases.W4IncomingRepresentatives
import DraismaVargas.LocalCases.GlobalW4

/-!
# The incoming `PairingReceipts` construction

Source: Draisma--Vargas Part I, Case `{aux-r0}` (nd2/nd3) and Equation (1)
(see `W4IncomingGlobalMatching`); Equation (C) is the codimension-one
wall-vertex change equation used throughout the `W4Bridge`/
`SecondEquation`/`ThirdEquation` family.

`W4IncomingRepresentatives.stored_representative_normalization` takes one
hypothesis that it does not discharge itself, named exactly in its docstring:

```
receipts : GlobalW4.PairingReceipts M₀ star (blockPattern data hc hab hOne star pictures) q
```

This file builds that receipts term from the incoming bundle
(`W4IncomingGlobalMatching`'s `fd`, `hCompat`, `star`, `pictures`), so the W4
chain closes from the incoming side up to one additional, precisely named and
genuinely satisfiable hypothesis -- see "The forest hypothesis" below.

## The route

`GlobalW4.AuxR0Profile.ofValidChangeZero` needs three things, and the incoming
bundle plus the one extra hypothesis below supplies each of them:

1. `(M₀).Valid` -- from `ContractionRamification.valid_contractDatum`, given
   `data.Valid` (`fd.valid`) and `ContractionForest data a b contracted`.
2. An `ExteriorProfile`, assembled case by case from `pictures` --
   `exteriorProfile_of_pictures` below. This needs only `fd` (through
   `fd.danglingEdgeNoGlue`) and `hCompat` (through its `DanglingReflected`
   half); **no forest hypothesis is needed here**.
3. `(M₀).targetChange ⟨a, hab⟩ = 0`, the codimension-one Equation (C) fact --
   from `W4Bridge.targetChange_contractDatum_merge` (again needing
   `ContractionForest`) applied to `fd.targetExcess_eq_zero a` and
   `fd.targetExcess_eq_zero b`, combined with the four-star's valency `4` and
   `ContractionRamification.card_incidentEdges_merge`.

`AuxR0Profile.ofValidChangeZero` then feeds `AuxR0Profile.pairingCounts q` and
`PairingCounts.toPairingReceipts`, landing exactly on
`GlobalW4.PairingReceipts (M₀) star (blockPattern data hc hab hOne star
pictures) q` -- the type `stored_representative_normalization` asks for.

## The forest hypothesis: `ContractionForest data a b contracted`

Both items 1 and 3 above route through
`ContractionRamification.ContractionForest data a b contracted` (the purely
combinatorial statement that the sheet fibre above the single contracted
target edge, together with the two endpoint partitions, forms a tree at every
merged block -- `ContractionRamification.contractionForest_count`). This is
**not** derivable from the named incoming bundle (`fd`, `hCompat`, `star`,
`pictures`) alone: the routes to it (for instance
`SourceFibreForest.contractionForest_of_fullDimensional`) need an actual
nonnegative wall metric realizing the zero pattern at `contracted`, which is
external data about *which* boundary point is being resolved, not part of the
combinatorial type `fd` witnesses. Every sibling "Incoming" bridge at this
same level of construction (`IncomingSourceCases.exists_classification`,
`W2IncomingClassification.exists_classification`,
`W3IncomingClassification.exists_classification`,
`W4Bridge.auxR0SourceInput_of_contraction`) carries this exact hypothesis
explicitly, and every theorem below that needs it names it explicitly as
`hForest : ContractionForest data a b contracted`, satisfiable together with
the rest of the bundle (it is a standing hypothesis of the whole incoming
construction, not a disguised contradiction).

## Non-vacuity

`PairingReceipts` is not in the trap that catches
`AuxR0SourceInput`. `AuxR0SourceInput` is provably uninhabitable alongside a
full-dimensional presentation on the *same* datum
(`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`, because it
describes the codimension-one wall datum, one target edge smaller).
`PairingReceipts`'s fields are block-local Riemann--Hurwitz identities with no
`targetExcess`/`equation_c` value forced wrong, and `ContractionForest` is a
literal tree-count identity satisfiable alongside full-dimensionality (indeed
every other Incoming bridge assumes it), so the bundle proved satisfiable here
is jointly consistent.
-/

namespace DraismaVargas.LocalCases.W4IncomingPairingReceipts

open DraismaVargas.Infrastructure GraphContraction GluingContraction ContractionRamification
open TargetExpansion
open W4StableSource W4Assembly W4TargetPairings
open ResolutionM11 ResolutionW4
open FullDimensionalSource WallDegeneration
open DraismaVargas.LocalCases.W4IncomingGlobalMatching (blockPattern)

section Incoming

variable {target : CFGraph} {degree : ℕ} {coordinate : Type*}
  [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
  {a b : target.V} {contracted : target.edges}
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : FourStar (contract target hab hOne) ⟨a, hab⟩)

local notation "M₀" => contractDatum data hc hab hOne
local notation "q" => W4IncomingTargetNormalization.pairing data fd hc hab hOne star

/-! ### Item 2: the `ExteriorProfile`, case by case from `pictures` -/

/-- `M₀`'s dangling-no-glue: transported from the incoming datum's own
(derived, not assumed) dangling-no-glue across the contraction. Needs only
`fd` and the reflected half of `hCompat`; no forest hypothesis. -/
theorem danglingEdgeNoGlue_M₀
    (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hCompat : DanglingCompatible data hc hab hOne) :
    DanglingEdgeNoGlue (contractDatum data hc hab hOne) :=
  danglingEdgeNoGlue_contractDatum data hCompat.2 fd.danglingEdgeNoGlue

/-- **Item 2.** The actual auxiliary picture of every wall block gives the
exact block-local exterior compatibility `ExteriorProfile` needs, matching the
canonical `blockPattern` read off those same pictures. Every inactive branch
of a dangling/nd2/nd3 picture is dangling by the picture's own `only_surviving`
field (or, for a wholly dangling block, its `old_dangling` field), hence has a
singleton edge block by dangling-no-glue. -/
theorem exteriorProfile_of_pictures
    (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : W4IncomingRepresentatives.Pictures data hc hab hOne star) :
    GlobalW4.ExteriorProfile (contractDatum data hc hab hOne) star
      (blockPattern data hc hab hOne star pictures) where
  nd2_dangling := by
    intro anchor block hPattern label hFirst hSecond
    apply GlobalW4.refinesOnBlock_splitBlock_of_blockCard_eq_one
    intro sheet hSheet
    have hPattern' :
        (pictures (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor)).pattern =
          BlockPattern.nd2 block := hPattern
    have hSheetRel :
        ((contractDatum data hc hab hOne).vertexPartition
            (⟨a, hab⟩ : (contract target hab hOne).V)).Rel
          (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor).1 sheet :=
      (((contractDatum data hc hab hOne).vertexPartition
          (⟨a, hab⟩ : (contract target hab hOne).V)).rel_repr_left anchor).trans hSheet
    cases hPic : pictures
        (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) with
    | dangling oldDangling =>
        rw [← (contractDatum data hc hab hOne).sourceEdgeIndex_sourceEdge]
        apply danglingEdgeNoGlue_M₀ data fd hc hab hOne hCompat
        exact oldDangling ((contractDatum data hc hab hOne).sourceEdge (star.edge label) sheet)
          label
          (WallBlock.ofSourceEdge_eq_of_rel (contractDatum data hc hab hOne) star _ label sheet
            hSheetRel)
          rfl
    | nd2 model picture =>
        rw [hPic] at hPattern'
        simp only [AuxR0BlockPicture.pattern, AuxR0BlockPicture.kind] at hPattern'
        have hModel : model = block := BlockPattern.nd2.inj hPattern'
        subst model
        rw [← (contractDatum data hc hab hOne).sourceEdgeIndex_sourceEdge]
        apply danglingEdgeNoGlue_M₀ data fd hc hab hOne hCompat
        by_contra hSurvives
        rcases picture.only_surviving
            ((contractDatum data hc hab hOne).sourceEdge (star.edge label) sheet)
            (WallBlock.ofSourceEdge_eq_of_rel (contractDatum data hc hab hOne) star _ label sheet
              hSheetRel)
            ⟨label, rfl⟩ hSurvives with hEq | hEq
        · exact hFirst (star.edge_injective
            (congrArg (fun e : (contractDatum data hc hab hOne).SourceEdge ↦ e.1.1) hEq))
        · exact hSecond (star.edge_injective
            (congrArg (fun e : (contractDatum data hc hab hOne).SourceEdge ↦ e.1.1) hEq))
    | nd3 model picture =>
        rw [hPic] at hPattern'
        exact BlockPattern.noConfusion hPattern'
  nd3_dangling := by
    intro anchor block hPattern label hFirst hSecond hThird
    apply GlobalW4.refinesOnBlock_splitBlock_of_blockCard_eq_one
    intro sheet hSheet
    have hPattern' :
        (pictures (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor)).pattern =
          BlockPattern.nd3 block := hPattern
    have hSheetRel :
        ((contractDatum data hc hab hOne).vertexPartition
            (⟨a, hab⟩ : (contract target hab hOne).V)).Rel
          (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor).1 sheet :=
      (((contractDatum data hc hab hOne).vertexPartition
          (⟨a, hab⟩ : (contract target hab hOne).V)).rel_repr_left anchor).trans hSheet
    cases hPic : pictures
        (WallBlock.ofSheet (contractDatum data hc hab hOne) ⟨a, hab⟩ anchor) with
    | dangling oldDangling =>
        rw [hPic] at hPattern'
        exact BlockPattern.noConfusion hPattern'
    | nd2 model picture =>
        rw [hPic] at hPattern'
        exact BlockPattern.noConfusion hPattern'
    | nd3 model picture =>
        rw [hPic] at hPattern'
        simp only [AuxR0BlockPicture.pattern, AuxR0BlockPicture.kind] at hPattern'
        have hModel : model = block := BlockPattern.nd3.inj hPattern'
        subst model
        rw [← (contractDatum data hc hab hOne).sourceEdgeIndex_sourceEdge]
        apply danglingEdgeNoGlue_M₀ data fd hc hab hOne hCompat
        by_contra hSurvives
        obtain ⟨label', hLabel', hEq⟩ := picture.only_surviving
          ((contractDatum data hc hab hOne).sourceEdge (star.edge label) sheet)
          (WallBlock.ofSourceEdge_eq_of_rel (contractDatum data hc hab hOne) star _ label sheet
            hSheetRel)
          ⟨label, rfl⟩ hSurvives
        have hEqLabel : label = label' :=
          star.edge_injective
            (congrArg (fun e : (contractDatum data hc hab hOne).SourceEdge ↦ e.1.1) hEq)
        subst hEqLabel
        rcases (block.mem_activeLabels label).mp hLabel' with h | h | h
        · exact hFirst h
        · exact hSecond h
        · exact hThird h

/-! ### Items 1 and 3: the forest hypothesis `ContractionForest` -/

/-- **Item 1.** `(M₀).Valid`, given the incoming datum's own validity and the
one named extra hypothesis. -/
theorem contractDatum_valid_of_forest
    (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (hForest : ContractionForest data a b contracted) :
    (contractDatum data hc hab hOne).Valid :=
  valid_contractDatum data hc hab hOne hForest fd.valid

/-- **Item 3.** The codimension-one Equation (C) fact at the merged wall
vertex: `data`'s own change vanishes at both old endpoints (full-dimensional
change-minimality), and the four-star's valency-`4` plus the generic
valency-merge identity forces the two old valencies to sum to `6`, so the two
vanishing changes already sum to zero before transporting across the
contraction. -/
theorem targetChange_wall_eq_zero_of_forest
    (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted) :
    (contractDatum data hc hab hOne).targetChange (⟨a, hab⟩ : (contract target hab hOne).V) = 0 := by
  have hA := fd.targetExcess_eq_zero a
  have hB := fd.targetExcess_eq_zero b
  have hCard := card_incidentEdges_merge hc hab hOne
  rw [star.card_incidentEdges] at hCard
  unfold GluingDatum.targetExcess at hA hB
  rw [DraismaVargas.LocalCases.W4Bridge.targetChange_contractDatum_merge data hc hab hOne hForest]
  omega

/-- The change-zero sum consumed by `AuxR0Profile.ofValidChangeZero`, read off
`targetChange_wall_eq_zero_of_forest` through the four-star reindexing. -/
theorem changeZero_of_forest
    (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted) :
    ∑ sourceBlock : WallBlock (contractDatum data hc hab hOne)
        (⟨a, hab⟩ : (contract target hab hOne).V),
      GlobalW4.AuxR0Profile.wallBlockRamification (contractDatum data hc hab hOne) star
        sourceBlock = 0 := by
  rw [← GlobalW4.AuxR0Profile.targetChange_eq_sum_wallBlockRamification
    (contractDatum data hc hab hOne) star]
  exact targetChange_wall_eq_zero_of_forest data fd hc hab hOne star hForest

/-! ### Assembly -/

/-- **The linchpin.** The actual outgoing candidate datum's receipts,
constructed from the incoming bundle (`fd`, `hCompat`, `star`, `pictures`)
plus the one named `ContractionForest` hypothesis. -/
theorem receiptsOfForest
    (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : W4IncomingRepresentatives.Pictures data hc hab hOne star) :
    GlobalW4.PairingReceipts (contractDatum data hc hab hOne) star
      (blockPattern data hc hab hOne star pictures)
      (W4IncomingTargetNormalization.pairing data fd hc hab hOne star) :=
  ((GlobalW4.AuxR0Profile.ofValidChangeZero
      (exteriorProfile_of_pictures data fd hc hab hOne star hCompat pictures)
      (contractDatum_valid_of_forest data fd hc hab hOne hForest)
      (changeZero_of_forest data fd hc hab hOne star hForest)).pairingCounts
    (W4IncomingTargetNormalization.pairing data fd hc hab hOne star)).toPairingReceipts

/-- **The W4 chain closes from the incoming side.** Feeding `receiptsOfForest`
into `W4IncomingRepresentatives.stored_representative_normalization` produces
the actual within-block sheet relabelling identifying the transported
incoming datum with the outgoing candidate's datum, on the incoming bundle
plus the one named `ContractionForest` hypothesis and no further gap. -/
theorem stored_representative_normalization_of_forest
    (data : GluingDatum target degree) (fd : FullDimensionalSourcePresentation data coordinate)
    {a b : target.V} {contracted : target.edges}
    (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
    (hOne : num_edges target a b = 1)
    (star : FourStar (contract target hab hOne) ⟨a, hab⟩)
    (hForest : ContractionForest data a b contracted)
    (hCompat : DanglingCompatible data hc hab hOne)
    (pictures : W4IncomingRepresentatives.Pictures data hc hab hOne star) :
    ∃ relabeling : (GluingTransport.transport
        (W4IncomingTargetNormalization.targetIso data fd hc hab hOne star) data).SheetRelabeling,
      relabeling.apply =
        (receiptsOfForest data fd hc hab hOne star hForest hCompat pictures).candidate.datum :=
  W4IncomingRepresentatives.stored_representative_normalization data fd hc hab hOne star hCompat
    pictures (receiptsOfForest data fd hc hab hOne star hForest hCompat pictures)

end Incoming

end DraismaVargas.LocalCases.W4IncomingPairingReceipts
