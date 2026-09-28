import DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
import DraismaVargas.LocalCases.W4SourceClassification
import DraismaVargas.LocalCases.NonDanglingValency
import DraismaVargas.LocalCases.NonTrivalentValencyFourAnchor

/-!
# The rigid K = 0 background above a four-valent wall

Source: Vargas, Part II, Section 5.1 (rigidity above `w0`, and the statement
that `H_0` has a unique 4-valent vertex `A` while all other vertices are
trivalent) and Section 5.2, case `{v4-nd4}` (the `K = 0` construction, which
only needs existence after orienting the smaller pair).

## What is proved

`NonTrivalentValencyFourKZero.PrescribedPairing.candidate_datum_valid` takes
a `PairingBackground` for the wall blocks away from the distinguished
four-valent class.  This module *produces* that input from the incoming cover.

* `BlockDangling` is the block-local form of `GlobalW4.ExteriorProfile`: it only
  speaks about the single wall block being resolved.  `BlockDangling.exterior`
  and `BlockDangling.countAtSide` are the guarded forms of
  `GlobalW4.ExteriorProfile.exterior` and `GlobalW4.ExteriorProfile.countAtSide`.
  They are needed because `countAtSide` expects a *total* ordinary-block profile
  `pattern : Fin degree -> BlockPattern`, and no value of `BlockPattern`
  describes the nd4 anchor: the anchor block genuinely fails the nd2/nd3
  dangling conditions, so no neutral extension of the total profile exists.
* `OrdinaryBlockProfile` is the guarded active-branch census: the zero/two/three
  classification and dangling-no-glue singleton statement are required only away
  from the anchor block.  Its `pattern` assigns each ordinary block its canonical
  W4 split/join resolution, and the harmless dangling pattern on the anchor
  block, where the `K = 0` resolution overrides it anyway.  (Leaving an ordinary
  `r0` block *unchanged* is not an option: when its two active branches lie on
  the same side one endpoint has Riemann--Hurwitz left side `1` against a block
  of size bigger than one.)
* `blockLocalBackground` builds `PrescribedPairing.BlockLocalBackground` from
  that census, transported through the selected block-preserving branch gauge:
  the gauge permutation is the identity outside the anchor block, so every other
  block's edge classes, and hence its picture, transport verbatim.
* `exists_valid_candidate`, `candidate_datum_valid'` and the restated exact
  endpoint / new-edge sizes then carry **no** background hypothesis.

## What is not proved here

The residual source input is exactly one hypothesis, and it is the one
isolated in `NonDanglingValency` (see its module docstring):
every wall block *other than the anchor* has non-dangling valency at most three.
`NonDanglingValency` proves this is not a consequence of validity,
dangling-no-glue and Equation (C); in the paper it is the trivalence of
`H(M_0)` away from its unique four-valent vertex, i.e. full-dimensionality of
the incoming datum.  Here it enters as the `active_card` field of
`OrdinaryBlockProfile` (through `ordinaryBlockProfile_of_valency_le_three`), and
never as a hypothesis about the object being constructed.  At the wall of an
actual contraction of a full-dimensional incoming cover it is the *only* input
left: `ordinaryBlockProfile_of_fullDimensional` and
`ordinaryBlockProfile_of_contractionForest` discharge target-direction
injectivity through `NonTrivalentValencyFourAnchor.targetInjective`.

Everything else -- connectedness and genus zero of the target, incoming
validity, dangling-no-glue, `r(A) = 0` and the four-branch anchor -- is already
the input of the `K = 0` construction.

## Used by

The boundary dispatcher for Part II case `{v4-nd4}`, which in addition
identifies the outgoing stable type and its natural row dictionary.
-/

namespace DraismaVargas.LocalCases.NonTrivalentValencyFourBackground

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.GlobalW4
open DraismaVargas.LocalCases.W4SourceClassification
open DraismaVargas.LocalCases.NonTrivalentValencyFourKZero
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases.FullDimensionalSource

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-! ## 1.  Block-local W4 dangling data

`GlobalW4.ExteriorProfile` is a statement about *every* wall block.  The nd4
anchor cannot satisfy it, so the two consequences used by the assembly are
reproved with hypotheses about the single block being counted. -/

/-- The block-local form of `GlobalW4.DanglingSingletonProfile`, guarded to one
wall block.  It says exactly that the star branches which the block's classified
pattern declares inactive have singleton source classes throughout that block. -/
structure BlockDangling (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (anchor : Fin degree) : Prop where
  nd2_singleton : ∀ block : Nd2Block, pattern anchor = .nd2 block →
    ∀ label, label ≠ block.first → label ≠ block.second →
      ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
        (data.edgePartition (star.edge label)).blockCard sheet = 1
  nd3_singleton : ∀ block : Nd3Block, pattern anchor = .nd3 block →
    ∀ label, label ≠ block.first → label ≠ block.second → label ≠ block.third →
      ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
        (data.edgePartition (star.edge label)).blockCard sheet = 1

namespace BlockDangling

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall}
  {pattern : Fin degree → BlockPattern} {anchor : Fin degree}

/-- The `RefinesOnBlock` form of `nd2_singleton`, matching the corresponding
field of `GlobalW4.ExteriorProfile` at the single guarded block. -/
theorem refinesOnBlock_nd2 (facts : BlockDangling data star pattern anchor)
    (block : Nd2Block) (hPattern : pattern anchor = .nd2 block) (label : Fin 4)
    (hFirst : label ≠ block.first) (hSecond : label ≠ block.second) :
    (data.edgePartition (star.edge label)).RefinesOnBlock
      ((data.vertexPartition wall).splitBlock anchor)
      (data.vertexPartition wall) anchor :=
  refinesOnBlock_splitBlock_of_blockCard_eq_one
    (facts.nd2_singleton block hPattern label hFirst hSecond)

/-- The `RefinesOnBlock` form of `nd3_singleton`. -/
theorem refinesOnBlock_nd3 (facts : BlockDangling data star pattern anchor)
    (block : Nd3Block) (hPattern : pattern anchor = .nd3 block) (label : Fin 4)
    (hFirst : label ≠ block.first) (hSecond : label ≠ block.second)
    (hThird : label ≠ block.third) :
    (data.edgePartition (star.edge label)).RefinesOnBlock
      ((data.vertexPartition wall).splitBlock anchor)
      (data.vertexPartition wall) anchor :=
  refinesOnBlock_splitBlock_of_blockCard_eq_one
    (facts.nd3_singleton block hPattern label hFirst hSecond hThird)

/-- Block-local form of `GlobalW4.ExteriorProfile.nd2_dangling_count`. -/
theorem nd2_count (facts : BlockDangling data star pattern anchor)
    (block : Nd2Block) (hPattern : pattern anchor = .nd2 block) (label : Fin 4)
    (hFirst : label ≠ block.first) (hSecond : label ≠ block.second)
    (endpoint : SheetPartition degree)
    (hEndpoint : endpoint.Refines (data.vertexPartition wall))
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel anchor sheet) :
    (data.edgePartition (star.edge label)).blockCountWithin endpoint sheet =
      endpoint.blockCard sheet :=
  SheetPartition.blockCountWithin_eq_blockCard_of_refinesOnBlock_splitBlock
    (data.edgePartition (star.edge label)) endpoint
    (data.vertexPartition wall) anchor sheet
    (facts.refinesOnBlock_nd2 block hPattern label hFirst hSecond)
    hEndpoint hSheet

/-- Block-local form of `GlobalW4.ExteriorProfile.nd3_dangling_count`. -/
theorem nd3_count (facts : BlockDangling data star pattern anchor)
    (block : Nd3Block) (hPattern : pattern anchor = .nd3 block) (label : Fin 4)
    (hFirst : label ≠ block.first) (hSecond : label ≠ block.second)
    (hThird : label ≠ block.third) (endpoint : SheetPartition degree)
    (hEndpoint : endpoint.Refines (data.vertexPartition wall))
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel anchor sheet) :
    (data.edgePartition (star.edge label)).blockCountWithin endpoint sheet =
      endpoint.blockCard sheet :=
  SheetPartition.blockCountWithin_eq_blockCard_of_refinesOnBlock_splitBlock
    (data.edgePartition (star.edge label)) endpoint
    (data.vertexPartition wall) anchor sheet
    (facts.refinesOnBlock_nd3 block hPattern label hFirst hSecond hThird)
    hEndpoint hSheet

/-- Block-local form of `GlobalW4.ExteriorProfile.exterior`: the exterior
compatibility of the canonical W4 resolution on one wall block needs only that
block's own dangling data. -/
theorem exterior (facts : BlockDangling data star pattern anchor)
    (pairing : Fin 3) (edge : target.edges)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    (data.edgePartition edge).RefinesOnBlock
      (if star.right pairing edge then
        (blockwiseResolution data star pattern pairing anchor).right
      else
        (blockwiseResolution data star pattern pairing anchor).left)
      (data.vertexPartition wall) anchor := by
  have hMem : edge ∈ GluingDatum.incidentEdges wall := by
    simpa [GluingDatum.incidentEdges] using hIncident
  obtain ⟨label, rfl⟩ := star.exists_edge_eq edge hMem
  cases hPattern : pattern anchor with
  | nd2 block =>
      rw [blockwiseResolution, hPattern]
      simp only [resolutionAt, ResolutionW4.nd2ResolutionForPairing,
        W4TargetPairings.FourStar.right_edge]
      change
        (data.edgePartition (star.edge label)).RefinesOnBlock
          (if W4TargetPairings.Pairing.labelRight pairing label then
            (ResolutionW4.nd2Resolution (data.vertexPartition wall) anchor
              (W4TargetPairings.Pairing.labelRight pairing block.first)
              (W4TargetPairings.Pairing.labelRight pairing block.second)).right
          else
            (ResolutionW4.nd2Resolution (data.vertexPartition wall) anchor
              (W4TargetPairings.Pairing.labelRight pairing block.first)
              (W4TargetPairings.Pairing.labelRight pairing block.second)).left)
          (data.vertexPartition wall) anchor
      by_cases hSame :
          W4TargetPairings.Pairing.labelRight pairing block.first =
            W4TargetPairings.Pairing.labelRight pairing block.second
      · by_cases hSide :
          W4TargetPairings.Pairing.labelRight pairing label =
            W4TargetPairings.Pairing.labelRight pairing block.first
        · have hEndpoint := ResolutionW4.nd2Resolution_activeEndpoint_of_same
            (data.vertexPartition wall) anchor
            (W4TargetPairings.Pairing.labelRight pairing block.first)
            (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
          rw [hSide, hEndpoint]
          exact (star.edgePartition_refines_wall data label).refinesOnBlock
            anchor
        · have hFirst : label ≠ block.first := by
            intro h
            exact hSide (congrArg
              (W4TargetPairings.Pairing.labelRight pairing) h)
          have hSecond : label ≠ block.second := by
            intro h
            apply hSide
            exact (congrArg (W4TargetPairings.Pairing.labelRight pairing) h).trans
              hSame.symm
          have hOpposite :
              W4TargetPairings.Pairing.labelRight pairing label =
                !(W4TargetPairings.Pairing.labelRight pairing block.first) := by
            cases hLabel : W4TargetPairings.Pairing.labelRight pairing label <;>
              cases hFirstSide :
                W4TargetPairings.Pairing.labelRight pairing block.first <;>
              simp_all
          have hEndpoint := ResolutionW4.nd2Resolution_otherEndpoint_of_same
            (data.vertexPartition wall) anchor
            (W4TargetPairings.Pairing.labelRight pairing block.first)
            (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
          have hEndpoint' :
              (if W4TargetPairings.Pairing.labelRight pairing label then
                  (ResolutionW4.nd2Resolution (data.vertexPartition wall)
                    anchor
                    (W4TargetPairings.Pairing.labelRight pairing block.first)
                    (W4TargetPairings.Pairing.labelRight pairing
                      block.second)).right
                else
                  (ResolutionW4.nd2Resolution (data.vertexPartition wall)
                    anchor
                    (W4TargetPairings.Pairing.labelRight pairing block.first)
                    (W4TargetPairings.Pairing.labelRight pairing
                      block.second)).left) =
                (data.vertexPartition wall).splitBlock anchor := by
            rw [hOpposite]
            cases hFirstSide :
                W4TargetPairings.Pairing.labelRight pairing block.first
            · simp only [hFirstSide, Bool.not_false, if_true] at hEndpoint ⊢
              exact hEndpoint
            · simp only [hFirstSide, Bool.not_true, if_true] at hEndpoint ⊢
              exact hEndpoint
          rw [hEndpoint']
          exact facts.refinesOnBlock_nd2 block hPattern label hFirst
            hSecond
      · have hEndpoints := ResolutionW4.nd2Resolution_endpoints_of_ne
          (data.vertexPartition wall) anchor
          (W4TargetPairings.Pairing.labelRight pairing block.first)
          (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
        cases hLabel : W4TargetPairings.Pairing.labelRight pairing label
        · simp only [Bool.false_eq, hEndpoints.1]
          exact (star.edgePartition_refines_wall data label).refinesOnBlock
            anchor
        · simp only [if_true, hEndpoints.2]
          exact (star.edgePartition_refines_wall data label).refinesOnBlock
            anchor
  | nd3 block =>
      rw [blockwiseResolution, hPattern]
      let singleton := block.singletonLabel pairing
      let fine := data.edgePartition (star.edge singleton)
      have hFine : fine.Refines (data.vertexPartition wall) :=
        star.edgePartition_refines_wall data singleton
      simp only [resolutionAt, ResolutionW4.nd3ResolutionForPairing,
        W4TargetPairings.FourStar.right_edge]
      change
        (data.edgePartition (star.edge label)).RefinesOnBlock
          (if W4TargetPairings.Pairing.labelRight pairing label then
            (ResolutionW4.nd3Resolution (data.vertexPartition wall) fine hFine
              (W4TargetPairings.Pairing.labelRight pairing singleton)).right
          else
            (ResolutionW4.nd3Resolution (data.vertexPartition wall) fine hFine
              (W4TargetPairings.Pairing.labelRight pairing singleton)).left)
          (data.vertexPartition wall) anchor
      by_cases hSide : W4TargetPairings.Pairing.labelRight pairing label =
          W4TargetPairings.Pairing.labelRight pairing singleton
      · have hEndpoint := ResolutionW4.nd3Resolution_endpoint_of_same_side
          (data.vertexPartition wall) fine hFine
          (W4TargetPairings.Pairing.labelRight pairing singleton)
          (W4TargetPairings.Pairing.labelRight pairing label) hSide
        rw [hEndpoint]
        by_cases hActive : label = block.first ∨ label = block.second ∨
            label = block.third
        · have hEq : label = singleton :=
            block.eq_singletonLabel_of_active_of_same_side pairing label hActive
              hSide
          subst label
          exact (SheetPartition.Refines.refl fine).refinesOnBlock anchor
        · have hFirst : label ≠ block.first :=
            fun h ↦ hActive (Or.inl h)
          have hSecond : label ≠ block.second :=
            fun h ↦ hActive (Or.inr (Or.inl h))
          have hThird : label ≠ block.third :=
            fun h ↦ hActive (Or.inr (Or.inr h))
          exact (facts.refinesOnBlock_nd3 block hPattern label
            hFirst hSecond hThird).refinesAny_of_splitBlock fine
      · have hEndpoint := ResolutionW4.nd3Resolution_endpoint_of_other_side
          (data.vertexPartition wall) fine hFine
          (W4TargetPairings.Pairing.labelRight pairing singleton)
          (W4TargetPairings.Pairing.labelRight pairing label) hSide
        rw [hEndpoint]
        exact (star.edgePartition_refines_wall data label).refinesOnBlock anchor

/-- Block-local form of `GlobalW4.ExteriorProfile.countAtSide`: the four-valent
Riemann--Hurwitz inequality of the datum gives the exact trivalent block-count
inequality on either endpoint over one wall block, from that block's own
dangling data alone. -/
theorem countAtSide (facts : BlockDangling data star pattern anchor)
    (hRiemannHurwitz : data.RiemannHurwitzAtTargetVertex wall)
    (pairing : Fin 3)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel anchor sheet)
    (sideValue : Bool) :
    (((blockwiseResolution data star pattern pairing anchor).newEdge ::
        (oldEdgesAtSide star pairing sideValue).map data.edgePartition).map
      (fun edge ↦ (edge.blockCountWithin
        (endpointAtSide data star pattern pairing anchor sideValue) sheet :
          ℤ))).sum ≥
      (endpointAtSide data star pattern pairing anchor sideValue).blockCard
        sheet + 2 := by
  simp only [List.map_cons, List.sum_cons, List.map_map]
  rw [sum_oldEdgesAtSide_eq_sideSum star pairing sideValue]
  simp only [Function.comp_apply]
  have hPositive : ∀ label,
      1 ≤ ((data.edgePartition (star.edge label)).blockCountWithin
        (endpointAtSide data star pattern pairing anchor sideValue) sheet : ℤ) :=
    fun label ↦ by
      exact_mod_cast (data.edgePartition
        (star.edge label)).blockCountWithin_pos
          (endpointAtSide data star pattern pairing anchor sideValue) sheet
  cases hPattern : pattern anchor with
  | nd2 block =>
      by_cases hSame :
          W4TargetPairings.Pairing.labelRight pairing block.first =
            W4TargetPairings.Pairing.labelRight pairing block.second
      · by_cases hActiveSide : sideValue =
            W4TargetPairings.Pairing.labelRight pairing block.first
        · have hEndpoint :
              endpointAtSide data star pattern pairing anchor sideValue =
                data.vertexPartition wall := by
            unfold endpointAtSide blockwiseResolution
            rw [hPattern]
            simp only [resolutionAt, ResolutionW4.nd2ResolutionForPairing,
              W4TargetPairings.FourStar.right_edge]
            rw [hActiveSide]
            exact ResolutionW4.nd2Resolution_activeEndpoint_of_same
              (data.vertexPartition wall) anchor
              (W4TargetPairings.Pairing.labelRight pairing block.first)
              (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
          have hNewEdge :
              (blockwiseResolution data star pattern pairing anchor).newEdge =
                (data.vertexPartition wall).splitBlock anchor := by
            unfold blockwiseResolution
            rw [hPattern]
            simp only [resolutionAt, ResolutionW4.nd2ResolutionForPairing,
              W4TargetPairings.FourStar.right_edge]
            exact ResolutionW4.nd2Resolution_newEdge_of_same
              (data.vertexPartition wall) anchor
              (W4TargetPairings.Pairing.labelRight pairing block.first)
              (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
          have hNewCount :
              (((blockwiseResolution data star pattern pairing anchor).newEdge).blockCountWithin
                  (endpointAtSide data star pattern pairing anchor sideValue)
                  sheet : ℤ) =
                (data.vertexPartition wall).blockCard sheet := by
            rw [hEndpoint, hNewEdge]
            exact_mod_cast
              (data.vertexPartition wall).splitBlock_blockCountWithin_of_rel
                anchor sheet hSheet
          have hSideSum := W4TargetPairings.Pairing.sideSum_ge_two pairing
            sideValue
            (fun label ↦
              ((data.edgePartition (star.edge label)).blockCountWithin
                (endpointAtSide data star pattern pairing anchor sideValue)
                sheet : ℤ)) hPositive
          rw [hEndpoint] at hSideSum
          rw [hNewCount, hEndpoint]
          omega
        · have hOpposite : sideValue =
              !(W4TargetPairings.Pairing.labelRight pairing block.first) := by
            cases sideValue <;>
              cases hFirst :
                W4TargetPairings.Pairing.labelRight pairing block.first <;>
              simp_all
          have hEndpoint :
              endpointAtSide data star pattern pairing anchor sideValue =
                (data.vertexPartition wall).splitBlock anchor := by
            unfold endpointAtSide blockwiseResolution
            rw [hPattern]
            simp only [resolutionAt, ResolutionW4.nd2ResolutionForPairing,
              W4TargetPairings.FourStar.right_edge]
            rw [hOpposite]
            have hOther := ResolutionW4.nd2Resolution_otherEndpoint_of_same
              (data.vertexPartition wall) anchor
              (W4TargetPairings.Pairing.labelRight pairing block.first)
              (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
            cases hFirstSide :
                W4TargetPairings.Pairing.labelRight pairing block.first <;>
              simp [hFirstSide] at hOther ⊢
            · exact hOther
            · exact hOther
          have hNewEdge :
              (blockwiseResolution data star pattern pairing anchor).newEdge =
                (data.vertexPartition wall).splitBlock anchor := by
            unfold blockwiseResolution
            rw [hPattern]
            simp only [resolutionAt, ResolutionW4.nd2ResolutionForPairing,
              W4TargetPairings.FourStar.right_edge]
            exact ResolutionW4.nd2Resolution_newEdge_of_same
              (data.vertexPartition wall) anchor
              (W4TargetPairings.Pairing.labelRight pairing block.first)
              (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
          have hEndpointCard :
              (endpointAtSide data star pattern pairing anchor sideValue).blockCard
                sheet = 1 := by
            rw [hEndpoint]
            exact (data.vertexPartition wall).splitBlock_blockCard_of_rel
              anchor sheet hSheet
          have hNewCount :
              ((blockwiseResolution data star pattern pairing anchor).newEdge).blockCountWithin
                    (endpointAtSide data star pattern pairing anchor sideValue)
                    sheet = 1 := by
            rw [hEndpoint, hNewEdge]
            exact SheetPartition.blockCountWithin_self _ _
          have hSideSum := W4TargetPairings.Pairing.sideSum_ge_two pairing
            sideValue
            (fun label ↦
              ((data.edgePartition (star.edge label)).blockCountWithin
                (endpointAtSide data star pattern pairing anchor sideValue)
                sheet : ℤ)) hPositive
          rw [hNewCount, hEndpointCard]
          omega
      · have hEndpoint :
            endpointAtSide data star pattern pairing anchor sideValue =
              data.vertexPartition wall := by
          unfold endpointAtSide blockwiseResolution
          rw [hPattern]
          simp only [resolutionAt, ResolutionW4.nd2ResolutionForPairing,
            W4TargetPairings.FourStar.right_edge]
          have hEndpoints := ResolutionW4.nd2Resolution_endpoints_of_ne
            (data.vertexPartition wall) anchor
            (W4TargetPairings.Pairing.labelRight pairing block.first)
            (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
          cases sideValue <;> simp [hEndpoints]
        have hNewEdge :
            (blockwiseResolution data star pattern pairing anchor).newEdge =
              data.vertexPartition wall := by
          unfold blockwiseResolution
          rw [hPattern]
          simp only [resolutionAt, ResolutionW4.nd2ResolutionForPairing,
            W4TargetPairings.FourStar.right_edge]
          exact ResolutionW4.nd2Resolution_newEdge_of_ne
            (data.vertexPartition wall) anchor
            (W4TargetPairings.Pairing.labelRight pairing block.first)
            (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
        have hNewCount :
            ((blockwiseResolution data star pattern pairing anchor).newEdge).blockCountWithin
                  (endpointAtSide data star pattern pairing anchor sideValue)
                  sheet = 1 := by
          rw [hEndpoint, hNewEdge]
          exact SheetPartition.blockCountWithin_self _ _
        have hSideSum :=
          W4TargetPairings.Pairing.sideSum_ge_add_of_card_filter_eq_one
            pairing sideValue block.activeLabels
            (block.card_activeLabels_onSide_of_ne pairing sideValue hSame)
            (fun label ↦
              ((data.edgePartition (star.edge label)).blockCountWithin
                (endpointAtSide data star pattern pairing anchor sideValue)
                sheet : ℤ))
            ((data.vertexPartition wall).blockCard sheet : ℤ)
            (fun label _hSide _hActive ↦ hPositive label)
            (fun label _hSide hInactive ↦ by
              have hFirst : label ≠ block.first := by
                intro hEq
                exact hInactive ((block.mem_activeLabels label).mpr
                  (Or.inl hEq))
              have hSecond : label ≠ block.second := by
                intro hEq
                exact hInactive ((block.mem_activeLabels label).mpr
                  (Or.inr hEq))
              rw [hEndpoint]
              exact_mod_cast (facts.nd2_count block hPattern
                label hFirst hSecond (data.vertexPartition wall)
                (SheetPartition.Refines.refl _) sheet hSheet).ge)
        rw [hEndpoint] at hSideSum
        rw [hNewCount, hEndpoint]
        omega
  | nd3 block =>
      let singleton := block.singletonLabel pairing
      let fine := data.edgePartition (star.edge singleton)
      have hFine : fine.Refines (data.vertexPartition wall) :=
        star.edgePartition_refines_wall data singleton
      by_cases hSingletonSide : sideValue =
          W4TargetPairings.Pairing.labelRight pairing singleton
      · have hEndpoint :
            endpointAtSide data star pattern pairing anchor sideValue = fine := by
          unfold endpointAtSide blockwiseResolution
          rw [hPattern]
          simp only [resolutionAt, ResolutionW4.nd3ResolutionForPairing,
            W4TargetPairings.FourStar.right_edge]
          rw [hSingletonSide]
          exact ResolutionW4.nd3Resolution_endpoint_of_same_side
            (data.vertexPartition wall) fine hFine
            (W4TargetPairings.Pairing.labelRight pairing singleton)
            (W4TargetPairings.Pairing.labelRight pairing singleton) rfl
        have hNewEdge :
            (blockwiseResolution data star pattern pairing anchor).newEdge =
              fine := by
          unfold blockwiseResolution
          rw [hPattern]
          exact resolutionAt_nd3_newEdge data star pairing anchor block
        have hNewCount :
            ((blockwiseResolution data star pattern pairing anchor).newEdge).blockCountWithin
                  (endpointAtSide data star pattern pairing anchor sideValue)
                  sheet = 1 := by
          rw [hEndpoint, hNewEdge]
          exact SheetPartition.blockCountWithin_self _ _
        have hSideSum :=
          W4TargetPairings.Pairing.sideSum_eq_add_of_card_filter_eq_one
            pairing sideValue block.activeLabels (by
              rw [hSingletonSide]
              exact block.card_activeLabels_on_singletonSide pairing)
            (fun label ↦
              ((data.edgePartition (star.edge label)).blockCountWithin
                (endpointAtSide data star pattern pairing anchor sideValue)
                sheet : ℤ)) 1 (fine.blockCard sheet : ℤ)
            (fun label hLabel hActive ↦ by
              have hSameSide :=
                (W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mp hLabel
              rw [hSingletonSide] at hSameSide
              have hEq := block.eq_singletonLabel_of_active_of_same_side
                pairing label ((block.mem_activeLabels label).mp hActive)
                hSameSide
              subst label
              rw [hEndpoint]
              exact_mod_cast SheetPartition.blockCountWithin_self fine sheet)
            (fun label _hLabel hInactive ↦ by
              have hFirst : label ≠ block.first := by
                intro hEq
                exact hInactive ((block.mem_activeLabels label).mpr
                  (Or.inl hEq))
              have hSecond : label ≠ block.second := by
                intro hEq
                exact hInactive ((block.mem_activeLabels label).mpr
                  (Or.inr (Or.inl hEq)))
              have hThird : label ≠ block.third := by
                intro hEq
                exact hInactive ((block.mem_activeLabels label).mpr
                  (Or.inr (Or.inr hEq)))
              rw [hEndpoint]
              exact_mod_cast facts.nd3_count block hPattern
                label hFirst hSecond hThird fine hFine sheet hSheet)
        rw [hEndpoint] at hSideSum
        rw [hNewCount, hEndpoint]
        omega
      · have hEndpoint :
            endpointAtSide data star pattern pairing anchor sideValue =
              data.vertexPartition wall := by
          unfold endpointAtSide blockwiseResolution
          rw [hPattern]
          simp only [resolutionAt, ResolutionW4.nd3ResolutionForPairing,
            W4TargetPairings.FourStar.right_edge]
          exact ResolutionW4.nd3Resolution_endpoint_of_other_side
            (data.vertexPartition wall) fine hFine
            (W4TargetPairings.Pairing.labelRight pairing singleton) sideValue
            hSingletonSide
        have hNewEdge :
            (blockwiseResolution data star pattern pairing anchor).newEdge =
              fine := by
          unfold blockwiseResolution
          rw [hPattern]
          exact resolutionAt_nd3_newEdge data star pairing anchor block
        let value : Fin 4 → ℤ := fun label ↦
          ((data.edgePartition (star.edge label)).blockCountWithin
            (data.vertexPartition wall) sheet : ℤ)
        have hSingletonSum :=
          W4TargetPairings.Pairing.sideSum_eq_add_of_card_filter_eq_one
            pairing
            (W4TargetPairings.Pairing.labelRight pairing singleton)
            block.activeLabels (block.card_activeLabels_on_singletonSide pairing)
            value (value singleton)
            ((data.vertexPartition wall).blockCard sheet : ℤ)
            (fun label hLabel hActive ↦ by
              have hSameSide :=
                (W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mp hLabel
              have hEq := block.eq_singletonLabel_of_active_of_same_side
                pairing label ((block.mem_activeLabels label).mp hActive)
                hSameSide
              subst label
              rfl)
            (fun label _hLabel hInactive ↦ by
              have hFirst : label ≠ block.first := by
                intro hEq
                exact hInactive ((block.mem_activeLabels label).mpr
                  (Or.inl hEq))
              have hSecond : label ≠ block.second := by
                intro hEq
                exact hInactive ((block.mem_activeLabels label).mpr
                  (Or.inr (Or.inl hEq)))
              have hThird : label ≠ block.third := by
                intro hEq
                exact hInactive ((block.mem_activeLabels label).mpr
                  (Or.inr (Or.inr hEq)))
              change
                ((data.edgePartition (star.edge label)).blockCountWithin
                  (data.vertexPartition wall) sheet : ℤ) =
                  (data.vertexPartition wall).blockCard sheet
              exact_mod_cast facts.nd3_count block hPattern
                label hFirst hSecond hThird (data.vertexPartition wall)
                (SheetPartition.Refines.refl _) sheet hSheet)
        have hPartition := W4TargetPairings.Pairing.sideSum_false_add_true
          pairing value
        have hTotal := star.branchCount_sum_ge_two_mul_add_two
          data hRiemannHurwitz sheet
        change
          2 * ((data.vertexPartition wall).blockCard sheet : ℤ) + 2 ≤
            ∑ label : Fin 4, value label at hTotal
        rw [hEndpoint, hNewEdge]
        change
          ((fine.blockCountWithin (data.vertexPartition wall) sheet : ℤ) +
              W4TargetPairings.Pairing.sideSum pairing sideValue value) ≥
            (data.vertexPartition wall).blockCard sheet + 2
        have hNewValue :
            (fine.blockCountWithin (data.vertexPartition wall) sheet : ℤ) =
              value singleton := rfl
        rw [hNewValue]
        cases hSide : W4TargetPairings.Pairing.labelRight pairing singleton <;>
          cases sideValue <;> simp_all <;> omega

end BlockDangling

/-! ## 2.  The guarded ordinary-block census

`W4SourceClassification.ActiveBranchProfile` asks for the zero/two/three
active-branch classification at *every* wall block.  The nd4 anchor has four
active branches, so the total structure is unavailable; this is its guarded
form.  The anchor block is given the empty active set, whose classification is
the harmless dangling pattern -- the `K = 0` resolution overrides the anchor
block anyway. -/

/-- The literal active-branch census of the wall blocks away from a
distinguished block: zero, two or three active target branches there, and
dangling-no-glue's cardinality-one statement on the inactive ones. -/
structure OrdinaryBlockProfile (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (anchor : Fin degree) where
  active : WallBlock data wall → Finset (Fin 4)
  active_card : ∀ block : WallBlock data wall,
    ¬ (data.vertexPartition wall).Rel anchor block.1 →
      (active block).card = 0 ∨ (active block).card = 2 ∨
        (active block).card = 3
  inactive_singleton : ∀ block : WallBlock data wall,
    ¬ (data.vertexPartition wall).Rel anchor block.1 →
      ∀ label, label ∉ active block →
        ∀ sheet, (data.vertexPartition wall).Rel block.1 sheet →
          (data.edgePartition (star.edge label)).blockCard sheet = 1

namespace OrdinaryBlockProfile

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : Fin degree}

/-- Extend the census to the anchor block by the empty active set. -/
def activeTotal (profile : OrdinaryBlockProfile data star anchor)
    (block : WallBlock data wall) : Finset (Fin 4) :=
  if (data.vertexPartition wall).Rel anchor block.1 then ∅
    else profile.active block

theorem activeTotal_eq (profile : OrdinaryBlockProfile data star anchor)
    (block : WallBlock data wall)
    (hBlock : ¬ (data.vertexPartition wall).Rel anchor block.1) :
    profile.activeTotal block = profile.active block :=
  if_neg hBlock

theorem activeTotal_eq_empty (profile : OrdinaryBlockProfile data star anchor)
    (block : WallBlock data wall)
    (hBlock : (data.vertexPartition wall).Rel anchor block.1) :
    profile.activeTotal block = ∅ :=
  if_pos hBlock

theorem activeTotal_card (profile : OrdinaryBlockProfile data star anchor)
    (block : WallBlock data wall) :
    (profile.activeTotal block).card = 0 ∨
      (profile.activeTotal block).card = 2 ∨
        (profile.activeTotal block).card = 3 := by
  by_cases hBlock : (data.vertexPartition wall).Rel anchor block.1
  · left
    rw [profile.activeTotal_eq_empty block hBlock]
    simp
  · rw [profile.activeTotal_eq block hBlock]
    exact profile.active_card block hBlock

/-- Canonically classify the extended census of one wall block. -/
noncomputable def classification (profile : OrdinaryBlockProfile data star anchor)
    (block : WallBlock data wall) :
    ActiveBlockClassification (profile.activeTotal block) :=
  ActiveBlockClassification.of_card_zero_two_or_three
    (profile.activeTotal block) (profile.activeTotal_card block)

/-- The total W4 resolution pattern chosen by the guarded census.  It is
constant on every old wall block because it is indexed through the block
representative. -/
noncomputable def pattern (profile : OrdinaryBlockProfile data star anchor)
    (sheet : Fin degree) : BlockPattern :=
  (profile.classification (WallBlock.ofSheet data wall sheet)).pattern

/-- Away from the anchor block, the chosen pattern really carries the guarded
census's dangling data. -/
theorem blockDangling (profile : OrdinaryBlockProfile data star anchor)
    (sheet : Fin degree)
    (hSheet : ¬ (data.vertexPartition wall).Rel anchor sheet) :
    BlockDangling data star profile.pattern sheet := by
  classical
  have hNotRel :
      ¬ (data.vertexPartition wall).Rel anchor
        (WallBlock.ofSheet data wall sheet).1 := by
    intro hRel
    exact hSheet (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet))
  have hSingleton : ∀ label : Fin 4,
      label ∉ profile.activeTotal (WallBlock.ofSheet data wall sheet) →
        ∀ other, (data.vertexPartition wall).Rel sheet other →
          (data.edgePartition (star.edge label)).blockCard other = 1 := by
    intro label hLabel other hOther
    rw [profile.activeTotal_eq _ hNotRel] at hLabel
    exact profile.inactive_singleton (WallBlock.ofSheet data wall sheet) hNotRel
      label hLabel other
      (((data.vertexPartition wall).rel_repr_left sheet).trans hOther)
  constructor
  · intro nd2block hPattern label hFirst hSecond other hOther
    have hAtBlock :
        (profile.classification (WallBlock.ofSheet data wall sheet)).pattern =
          .nd2 nd2block := by
      simpa only [OrdinaryBlockProfile.pattern] using hPattern
    cases hClassification :
        profile.classification (WallBlock.ofSheet data wall sheet) with
    | dangling hActive =>
        refine hSingleton label ?_ other hOther
        rw [← hActive]
        simp
    | nd2 actual hActive =>
        rw [hClassification] at hAtBlock
        simp only [ActiveBlockClassification.pattern] at hAtBlock
        have hActual : actual = nd2block := BlockPattern.nd2.inj hAtBlock
        subst actual
        refine hSingleton label ?_ other hOther
        rw [← hActive]
        simp [Nd2Block.activeLabels, hFirst, hSecond]
    | nd3 actual hActive =>
        rw [hClassification] at hAtBlock
        exact BlockPattern.noConfusion hAtBlock
  · intro nd3block hPattern label hFirst hSecond hThird other hOther
    have hAtBlock :
        (profile.classification (WallBlock.ofSheet data wall sheet)).pattern =
          .nd3 nd3block := by
      simpa only [OrdinaryBlockProfile.pattern] using hPattern
    cases hClassification :
        profile.classification (WallBlock.ofSheet data wall sheet) with
    | dangling hActive =>
        rw [hClassification] at hAtBlock
        exact BlockPattern.noConfusion hAtBlock
    | nd2 actual hActive =>
        rw [hClassification] at hAtBlock
        exact BlockPattern.noConfusion hAtBlock
    | nd3 actual hActive =>
        rw [hClassification] at hAtBlock
        simp only [ActiveBlockClassification.pattern] at hAtBlock
        have hActual : actual = nd3block := BlockPattern.nd3.inj hAtBlock
        subst actual
        refine hSingleton label ?_ other hOther
        rw [← hActive]
        simp [Nd3Block.activeLabels, hFirst, hSecond, hThird]

/-- Any total active-branch census is in particular a guarded one. -/
def ofActiveBranchProfile (profile : ActiveBranchProfile data star)
    (anchor : Fin degree) : OrdinaryBlockProfile data star anchor where
  active := profile.active
  active_card := fun block _ ↦ profile.active_card block
  inactive_singleton := fun block _ label hLabel sheet hSheet ↦
    profile.inactive_singleton block label hLabel sheet hSheet

end OrdinaryBlockProfile

/-! ## 3.  The census of the actual incoming cover -/

/-- The actual active-label census of the incoming stable source, guarded away
from the anchor.  Beyond dangling-no-glue the only input is the zero/two/three
cardinality of the actual active-label finsets of the ordinary blocks. -/
noncomputable def ordinaryBlockProfile (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (anchor : Fin degree)
    (hNoGlue : DanglingEdgeNoGlue data)
    (hCard : ∀ block : WallBlock data wall,
      ¬ (data.vertexPartition wall).Rel anchor block.1 →
        (activeLabels data star block).card = 0 ∨
          (activeLabels data star block).card = 2 ∨
            (activeLabels data star block).card = 3) :
    OrdinaryBlockProfile data star anchor where
  active := activeLabels data star
  active_card := hCard
  inactive_singleton := fun block _ label hLabel sheet hSheet ↦
    blockCard_eq_one_of_not_mem_activeLabels data star hNoGlue block label
      hLabel sheet hSheet

/-- With target-direction injectivity the actual active-label count is the
non-dangling valency, so the trivalence bound `nd ≤ 3` gives the
zero/two/three classification through `NonDanglingValency`'s exclusion of
`nd = 1`. -/
theorem card_activeLabels_eq_zero_two_or_three
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (hConnected : data.Connected) (block : WallBlock data wall)
    (hInjective : NonDanglingStarInjective data star block)
    (hValency : nonDanglingValency data
      (WallBlock.sourceVertex data wall block) ≤ 3) :
    (activeLabels data star block).card = 0 ∨
      (activeLabels data star block).card = 2 ∨
        (activeLabels data star block).card = 3 := by
  rw [card_activeLabels_eq_nonDanglingValency data star block hInjective]
  exact NonDanglingValency.nonDanglingValency_eq_zero_or_two_or_three data
    hConnected _ hValency

/-- **The guarded census from the trivalence bound.**  This is the shape in
which Part II supplies the ordinary blocks: `H_0` has a unique four-valent
vertex `A`, and every other vertex above `w_0` is trivalent. -/
noncomputable def ordinaryBlockProfile_of_valency_le_three
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (anchor : Fin degree)
    (hNoGlue : DanglingEdgeNoGlue data) (hConnected : data.Connected)
    (hInjective : ∀ block : WallBlock data wall,
      ¬ (data.vertexPartition wall).Rel anchor block.1 →
        NonDanglingStarInjective data star block)
    (hValency : ∀ block : WallBlock data wall,
      ¬ (data.vertexPartition wall).Rel anchor block.1 →
        nonDanglingValency data (WallBlock.sourceVertex data wall block) ≤ 3) :
    OrdinaryBlockProfile data star anchor :=
  ordinaryBlockProfile data star anchor hNoGlue fun block hBlock ↦
    card_activeLabels_eq_zero_two_or_three data star hConnected block
      (hInjective block hBlock) (hValency block hBlock)

/-! ### Non-vacuity

At degree one every sheet partition is discrete, so both guarded structures are
inhabited for every four-valent wall of every degree-one cover, with no source
receipt at all. -/

theorem blockCard_degree_one (partition : SheetPartition 1) (sheet : Fin 1) :
    partition.blockCard sheet = 1 := by
  have hPos := partition.blockCard_pos sheet
  have hLe : partition.blockCard sheet ≤ 1 := by
    have := Finset.card_le_card (Finset.subset_univ (partition.block sheet))
    simpa [SheetPartition.blockCard] using this
  omega

/-- Non-vacuity witness for `BlockDangling`. -/
theorem blockDangling_degree_one (data : GluingDatum target 1)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin 1 → BlockPattern) (anchor : Fin 1) :
    BlockDangling data star pattern anchor where
  nd2_singleton := fun _ _ label _ _ sheet _ ↦
    blockCard_degree_one (data.edgePartition (star.edge label)) sheet
  nd3_singleton := fun _ _ label _ _ _ sheet _ ↦
    blockCard_degree_one (data.edgePartition (star.edge label)) sheet

/-- Non-vacuity witness for `OrdinaryBlockProfile`. -/
def ordinaryBlockProfile_degree_one (data : GluingDatum target 1)
    (star : W4TargetPairings.FourStar target wall) (anchor : Fin 1) :
    OrdinaryBlockProfile data star anchor where
  active := fun _ ↦ (∅ : Finset (Fin 4))
  active_card := fun _ _ ↦ Or.inl (by simp)
  inactive_singleton := fun _ _ label _ sheet _ ↦
    blockCard_degree_one (data.edgePartition (star.edge label)) sheet

/-! ## 4.  Transport through the selected block-preserving branch gauge -/

section Gauge

variable {data : GluingDatum target degree}
  {star : W4TargetPairings.FourStar target wall} {anchor : WallBlock data wall}
  (source : FourBranchAnchor data star anchor) (pairing : Fin 3)
  (hNoGlue : DanglingEdgeNoGlue data)
  (hRamification : data.localRamification wall anchor = 0)

/-- The selected gauge permutation is the identity outside the anchor's wall
block, so every other block's target-branch classes -- hence its whole nd2/nd3
picture -- transport verbatim to the gauged datum. -/
theorem gauged_blockCard_eq_of_not_rel
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (label : Fin 4) (sheet : Fin degree)
    (hSheet : ¬ (data.vertexPartition wall).Rel anchor.1 sheet) :
    ((PrescribedPairing.gaugedData source pairing hNoGlue
        hRamification).edgePartition (star.edge label)).blockCard sheet =
      (data.edgePartition (star.edge label)).blockCard sheet := by
  by_cases hLabel : label = PrescribedPairing.secondSelectedLabel source pairing
  · subst hLabel
    have hFixed :
        PrescribedPairing.permutation source pairing hNoGlue hRamification
          sheet = sheet := by
      apply PrescribedPairing.permutation_outside source pairing hNoGlue
        hRamification sheet
      intro hMem
      exact hSheet (((data.vertexPartition wall).mem_block_iff _ _).mp hMem)
    have hCard := SheetPartition.relabel_blockCard
      (data.edgePartition
        (star.edge (PrescribedPairing.secondSelectedLabel source pairing)))
      (PrescribedPairing.permutation source pairing hNoGlue hRamification) sheet
    rw [hFixed] at hCard
    rw [PrescribedPairing.gaugedData_edgePartition_second source pairing
      hNoGlue hRamification]
    exact hCard
  · rw [PrescribedPairing.gaugedData_edgePartition_other source pairing hNoGlue
      hRamification hConnected hGenus label hLabel]

/-- The guarded census of the incoming cover is a guarded census of the gauged
cover on every block that is not related to the anchor. -/
theorem gauged_blockDangling
    (profile : OrdinaryBlockProfile data star anchor.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (block : Fin degree)
    (hBlock : ¬ (data.vertexPartition wall).Rel anchor.1 block) :
    BlockDangling
      (PrescribedPairing.gaugedData source pairing hNoGlue hRamification) star
      profile.pattern block := by
  have hBase := profile.blockDangling block hBlock
  have hWall := PrescribedPairing.gaugedData_vertexPartition_wall source pairing
    hNoGlue hRamification
  have hTransfer : ∀ (label : Fin 4) (sheet : Fin degree),
      ((PrescribedPairing.gaugedData source pairing hNoGlue
          hRamification).vertexPartition wall).Rel block sheet →
        ((PrescribedPairing.gaugedData source pairing hNoGlue
            hRamification).edgePartition (star.edge label)).blockCard sheet =
          (data.edgePartition (star.edge label)).blockCard sheet ∧
          (data.vertexPartition wall).Rel block sheet := by
    intro label sheet hRel
    rw [hWall] at hRel
    have hNot : ¬ (data.vertexPartition wall).Rel anchor.1 sheet := by
      intro hAnchor
      exact hBlock (hAnchor.trans hRel.symm)
    exact ⟨gauged_blockCard_eq_of_not_rel source pairing hNoGlue hRamification
      hConnected hGenus label sheet hNot, hRel⟩
  constructor
  · intro nd2block hPattern label hFirst hSecond sheet hSheet
    obtain ⟨hCard, hRel⟩ := hTransfer label sheet hSheet
    rw [hCard]
    exact hBase.nd2_singleton nd2block hPattern label hFirst hSecond sheet hRel
  · intro nd3block hPattern label hFirst hSecond hThird sheet hSheet
    obtain ⟨hCard, hRel⟩ := hTransfer label sheet hSheet
    rw [hCard]
    exact hBase.nd3_singleton nd3block hPattern label hFirst hSecond hThird
      sheet hRel

/-- **The rigid background of the ordinary wall blocks.**  Every block not
related to the anchor receives its canonical W4 split/join resolution for the
prescribed target pairing, and the guarded census supplies all three receipts
`BlockLocalBackground` asks for. -/
noncomputable def blockLocalBackground
    (profile : OrdinaryBlockProfile data star anchor.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) :
    PrescribedPairing.BlockLocalBackground source pairing hNoGlue
      hRamification where
  resolution :=
    blockwiseResolution
      (PrescribedPairing.gaugedData source pairing hNoGlue hRamification) star
      profile.pattern pairing
  contracts := fun block _ ↦
    blockwiseResolution_contracts
      (PrescribedPairing.gaugedData source pairing hNoGlue hRamification) star
      profile.pattern pairing block
  exterior := by
    intro edge hIncident block hBlock
    rw [PrescribedPairing.gaugedData_vertexPartition_wall source pairing hNoGlue
      hRamification] at hBlock
    exact (gauged_blockDangling source pairing hNoGlue hRamification profile
      hConnected hGenus block hBlock).exterior pairing edge hIncident
  left_riemannHurwitz := by
    intro block _hCanonical hBlock
    rw [PrescribedPairing.gaugedData_vertexPartition_wall source pairing hNoGlue
      hRamification] at hBlock
    intro sheet hSheet
    have hCounts :
        (((blockwiseResolution
              (PrescribedPairing.gaugedData source pairing hNoGlue
                hRamification) star profile.pattern pairing block).newEdge ::
            (star.leftEdges pairing).map
              (PrescribedPairing.gaugedData source pairing hNoGlue
                hRamification).edgePartition).map
          (fun edge ↦ (edge.blockCountWithin
            (blockwiseResolution
              (PrescribedPairing.gaugedData source pairing hNoGlue
                hRamification) star profile.pattern pairing block).left
              sheet : ℤ))).sum ≥
          ((blockwiseResolution
            (PrescribedPairing.gaugedData source pairing hNoGlue hRamification)
              star profile.pattern pairing block).left.blockCard sheet : ℤ) +
            2 := by
      simpa [oldEdgesAtSide, endpointAtSide] using
        (gauged_blockDangling source pairing hNoGlue hRamification profile
          hConnected hGenus block hBlock).countAtSide
          ((PrescribedPairing.gaugedData_valid source pairing hNoGlue
            hRamification hValid).2 wall) pairing sheet hSheet false
    have hLength :
        ((blockwiseResolution
            (PrescribedPairing.gaugedData source pairing hNoGlue hRamification)
              star profile.pattern pairing block).newEdge ::
          (star.leftEdges pairing).map
            (PrescribedPairing.gaugedData source pairing hNoGlue
              hRamification).edgePartition).length = 3 := by
      simp
    rw [hLength]
    omega
  right_riemannHurwitz := by
    intro block _hCanonical hBlock
    rw [PrescribedPairing.gaugedData_vertexPartition_wall source pairing hNoGlue
      hRamification] at hBlock
    intro sheet hSheet
    have hCounts :
        (((blockwiseResolution
              (PrescribedPairing.gaugedData source pairing hNoGlue
                hRamification) star profile.pattern pairing block).newEdge ::
            (star.rightEdges pairing).map
              (PrescribedPairing.gaugedData source pairing hNoGlue
                hRamification).edgePartition).map
          (fun edge ↦ (edge.blockCountWithin
            (blockwiseResolution
              (PrescribedPairing.gaugedData source pairing hNoGlue
                hRamification) star profile.pattern pairing block).right
              sheet : ℤ))).sum ≥
          ((blockwiseResolution
            (PrescribedPairing.gaugedData source pairing hNoGlue hRamification)
              star profile.pattern pairing block).right.blockCard sheet : ℤ) +
            2 := by
      simpa [oldEdgesAtSide, endpointAtSide] using
        (gauged_blockDangling source pairing hNoGlue hRamification profile
          hConnected hGenus block hBlock).countAtSide
          ((PrescribedPairing.gaugedData_valid source pairing hNoGlue
            hRamification hValid).2 wall) pairing sheet hSheet true
    have hLength :
        ((blockwiseResolution
            (PrescribedPairing.gaugedData source pairing hNoGlue hRamification)
              star profile.pattern pairing block).newEdge ::
          (star.rightEdges pairing).map
            (PrescribedPairing.gaugedData source pairing hNoGlue
              hRamification).edgePartition).length = 3 := by
      simp
    rw [hLength]
    omega

/-! ## 5.  The unconditional `K = 0` candidate -/

/-- The global background contract, produced from the incoming cover through
the proved nested-paste adapter. -/
noncomputable def pairingBackground
    (profile : OrdinaryBlockProfile data star anchor.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) :
    PrescribedPairing.PairingBackground source pairing hNoGlue hRamification :=
  (blockLocalBackground source pairing hNoGlue hRamification profile hConnected
    hGenus hValid).pairingBackground

/-- The actual outgoing `K = 0` candidate, with no supplied background. -/
noncomputable def candidate
    (profile : OrdinaryBlockProfile data star anchor.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) :
    BalancedGlobal.Candidate target degree
      (PrescribedPairing.gaugedData source pairing hNoGlue hRamification) wall :=
  PrescribedPairing.candidate source pairing hNoGlue hRamification
    (pairingBackground source pairing hNoGlue hRamification profile hConnected
      hGenus hValid) hConnected hGenus

/-- **`candidate_datum_valid` without a background hypothesis.** -/
theorem candidate_datum_valid'
    (profile : OrdinaryBlockProfile data star anchor.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) :
    (candidate source pairing hNoGlue hRamification profile hConnected hGenus
      hValid).datum.Valid :=
  PrescribedPairing.candidate_datum_valid source pairing hNoGlue hRamification
    (pairingBackground source pairing hNoGlue hRamification profile hConnected
      hGenus hValid) hConnected hGenus hValid

/-- Exact `K = 0` endpoint sizes on the produced candidate. -/
theorem candidate_endpoint_blockCard_add_one'
    (profile : OrdinaryBlockProfile data star anchor.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) (sideValue : Bool) :
    (if sideValue then
        ((candidate source pairing hNoGlue hRamification profile hConnected
          hGenus hValid).resolution anchor.1).right
      else ((candidate source pairing hNoGlue hRamification profile hConnected
        hGenus hValid).resolution anchor.1).left).blockCard
          (PrescribedPairing.selectedRepresentative source pairing) + 1 =
      if sideValue = PrescribedPairing.smallerSide source pairing then
        PrescribedPairing.sideIndex source pairing
          (PrescribedPairing.smallerSide source pairing)
      else (data.vertexPartition wall).blockCard anchor.1 + 1 :=
  PrescribedPairing.candidate_endpoint_blockCard_add_one source pairing hNoGlue
    hRamification
    (pairingBackground source pairing hNoGlue hRamification profile hConnected
      hGenus hValid) hConnected hGenus sideValue

/-- Exact `K = 0` bridge size in the outgoing gluing datum of the produced
candidate. -/
theorem candidate_newSourceEdge_index_add_one'
    (profile : OrdinaryBlockProfile data star anchor.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) :
    (candidate source pairing hNoGlue hRamification profile hConnected hGenus
        hValid).datum.sourceEdgeIndex
      ((candidate source pairing hNoGlue hRamification profile hConnected hGenus
        hValid).newSourceEdge
          (PrescribedPairing.selectedRepresentative source pairing)) + 1 =
      PrescribedPairing.sideIndex source pairing
        (PrescribedPairing.smallerSide source pairing) :=
  PrescribedPairing.candidate_newSourceEdge_index_add_one source pairing hNoGlue
    hRamification
    (pairingBackground source pairing hNoGlue hRamification profile hConnected
      hGenus hValid) hConnected hGenus

/-- **The existence statement.**  From the actual four-branch anchor, the
incoming dangling-no-glue and `r(A) = 0` receipts, incoming validity, a
genus-zero connected target, and the guarded ordinary-block census, the rigid
`K = 0` background exists; the candidate installed on it is valid and carries
the exact endpoint and bridge sizes. -/
theorem exists_valid_candidate
    (profile : OrdinaryBlockProfile data star anchor.1)
    (hConnected : graph_connected target) (hGenus : genus target = 0)
    (hValid : data.Valid) :
    ∃ geometry :
        PrescribedPairing.PairingBackground source pairing hNoGlue
          hRamification,
      (PrescribedPairing.candidate source pairing hNoGlue hRamification
        geometry hConnected hGenus).datum.Valid ∧
      (∀ sideValue : Bool,
        (if sideValue then
            ((PrescribedPairing.candidate source pairing hNoGlue hRamification
              geometry hConnected hGenus).resolution anchor.1).right
          else ((PrescribedPairing.candidate source pairing hNoGlue
            hRamification geometry hConnected hGenus).resolution
              anchor.1).left).blockCard
            (PrescribedPairing.selectedRepresentative source pairing) + 1 =
          if sideValue = PrescribedPairing.smallerSide source pairing then
            PrescribedPairing.sideIndex source pairing
              (PrescribedPairing.smallerSide source pairing)
          else (data.vertexPartition wall).blockCard anchor.1 + 1) ∧
      (PrescribedPairing.candidate source pairing hNoGlue hRamification
          geometry hConnected hGenus).datum.sourceEdgeIndex
        ((PrescribedPairing.candidate source pairing hNoGlue hRamification
          geometry hConnected hGenus).newSourceEdge
            (PrescribedPairing.selectedRepresentative source pairing)) + 1 =
        PrescribedPairing.sideIndex source pairing
          (PrescribedPairing.smallerSide source pairing) :=
  ⟨pairingBackground source pairing hNoGlue hRamification profile hConnected
      hGenus hValid,
    candidate_datum_valid' source pairing hNoGlue hRamification profile
      hConnected hGenus hValid,
    candidate_endpoint_blockCard_add_one' source pairing hNoGlue hRamification
      profile hConnected hGenus hValid,
    candidate_newSourceEdge_index_add_one' source pairing hNoGlue hRamification
      profile hConnected hGenus hValid⟩

end Gauge

/-! ## 6.  Discharging target-direction injectivity at an actual wall

At the wall of an actual contraction of a full-dimensional incoming cover,
`NonTrivalentValencyFourAnchor.targetInjective` gives target-direction
injectivity at *every* block above the wall.  Its consequence
`card_activeLabels_eq_nonDanglingValency` then turns the guarded census into a
single numerical input: the trivalence of `H(M_0)` away from its unique
four-valent vertex.  This is exactly the residual obligation that
`NonDanglingValency`'s module docstring isolates; it is *not* a consequence of
validity, dangling-no-glue and Equation (C). -/

section ActualWall

variable {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (data : GluingDatum target degree)
  (fd : FullDimensionalSourcePresentation data coordinate)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (star : W4TargetPairings.FourStar (contract target hab hOne) ⟨a, hab⟩)

/-- **The residual source input, isolated.**  Given the incoming
full-dimensional presentation and preservation of danglingness, the guarded
ordinary-block census of the wall datum follows from dangling-no-glue,
connectedness, and the bound `nd ≤ 3` on the blocks above the wall other than
the anchor -- nothing else. -/
noncomputable def ordinaryBlockProfile_of_fullDimensional
    (hPreserved : WallDegeneration.DanglingPreserved data hc hab hOne)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum data hc hab hOne))
    (hConnected : (contractDatum data hc hab hOne).Connected)
    (anchorBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hValency : ∀ block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          anchorBlock.1 block.1 →
        nonDanglingValency (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne)
            ⟨a, hab⟩ block) ≤ 3) :
    OrdinaryBlockProfile (contractDatum data hc hab hOne) star anchorBlock.1 :=
  ordinaryBlockProfile_of_valency_le_three (contractDatum data hc hab hOne) star
    anchorBlock.1 hNoGlue hConnected
    (fun block _ ↦ NonTrivalentValencyFourAnchor.targetInjective data fd hc hab
      hOne star hPreserved block)
    hValency

/-- The forest of a legal wall contraction supplies the danglingness transfer,
so the same census follows from the actual contraction forest. -/
noncomputable def ordinaryBlockProfile_of_contractionForest
    (hForest : ContractionForest data a b contracted)
    (hNoGlue : DanglingEdgeNoGlue (contractDatum data hc hab hOne))
    (hConnected : (contractDatum data hc hab hOne).Connected)
    (anchorBlock : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩)
    (hValency : ∀ block : WallBlock (contractDatum data hc hab hOne) ⟨a, hab⟩,
      ¬ ((contractDatum data hc hab hOne).vertexPartition ⟨a, hab⟩).Rel
          anchorBlock.1 block.1 →
        nonDanglingValency (contractDatum data hc hab hOne)
          (WallBlock.sourceVertex (contractDatum data hc hab hOne)
            ⟨a, hab⟩ block) ≤ 3) :
    OrdinaryBlockProfile (contractDatum data hc hab hOne) star anchorBlock.1 :=
  ordinaryBlockProfile_of_fullDimensional data fd hc hab hOne star
    (WallAdmissibility.danglingPreserved_of_contractionForest data hc hab hOne
      hForest)
    hNoGlue hConnected anchorBlock hValency

end ActualWall

end DraismaVargas.LocalCases.NonTrivalentValencyFourBackground
