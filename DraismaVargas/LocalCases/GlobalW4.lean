module

public import DraismaVargas.Infrastructure.Change
public import DraismaVargas.LocalCases.BalancedGlobal
public import DraismaVargas.LocalCases.W4Assembly
public import DraismaVargas.LocalCases.GlobalBookends

@[expose] public section

/-!
# Global candidates for the four-valent wall case

This is Case `{w4}` of Draisma--Vargas Part I, Section 6 (arXiv:1909.12924):
the contracted target vertex is four-valent, and the source there reduces it to
the auxiliary Cases `{aux-r0-nd2}` and `{aux-r0-nd3}`.
`W4Assembly` constructs and contracts the three whole-wall sheet resolutions.
This module supplies the occurrence-level boundary to `BalancedGlobal`: the
old edge lists are canonical consequences of the four-star pairing, so a
source classifier records the genuinely dangling branches once.
`AuxR0Profile` combines that classification with the source's exact
zero-ramification equation, derives all three candidates' block-local
exterior compatibility and endpoint counts, and recovers the two active nd2
branch sizes.

No validity hypothesis is stored here.  Once these exact counts are given,
`PairingReceipts.candidate` is an actual `BalancedGlobal.Candidate`, whose
outgoing gluing datum and validity are derived by the generic global assembly.
The occurrence-level index theorems identify the actual regrown source edge's
dilation with the corresponding old nd2/nd3 branch denominator.
`presentedFamilyOfCountsAndOccurrenceReceipts` is the basic assembled W4
endpoint: it combines those valid candidates with exact literal path
occurrence classifications, indexed by the existing canonical
`SheetPartition.Blocks` subtype, derives the weighted term receipts, and
retains the presentations through semantic lowering.

`canonicalPresentationOfPaths` is the sharper load-bearing boundary.  It
constructs all three matrices from one common family of retained old paths
and the regrown sheets assigned to each row, labels the wall column by
`none`, proves all other columns agree, and reduces the actual matrix
occurrences to two source-level multisets (`canonicalNewSheetOccurrences` and
`canonicalOldPathOccurrences`).
-/

namespace DraismaVargas.LocalCases.GlobalW4

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.W4DeterminantContributions
open DraismaVargas.LocalCases.GlobalBookends

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- A fine partition whose blocks are singleton on one selected wall block
refines the canonical singleton split there.  This is the direct conversion
from the source's dangling-no-glue cardinality statement to the block-local
partition language used by `GlobalAssembly`. -/
theorem refinesOnBlock_splitBlock_of_blockCard_eq_one
    {fine wallPartition : SheetPartition degree} {anchor : Fin degree}
    (hSingleton : ∀ sheet, wallPartition.Rel anchor sheet →
      fine.blockCard sheet = 1) :
    fine.RefinesOnBlock (wallPartition.splitBlock anchor) wallPartition
      anchor := by
  intro first second hFirst hFine
  have hBlock := fine.block_eq_singleton_of_blockCard_eq_one first
    (hSingleton first hFirst)
  have hSecond : second ∈ fine.block first :=
    (fine.mem_block_iff first second).mpr hFine
  rw [hBlock] at hSecond
  have hEq : second = first := Finset.mem_singleton.mp hSecond
  subst second
  exact rfl

/-- The literal dangling-no-glue information for source Case `{aux-r0}`.
Every absent old branch induces singleton edge blocks throughout the selected
wall block.  This is weaker and closer to the paper than directly asking for
a refinement of a newly constructed endpoint partition. -/
structure DanglingSingletonProfile (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) where
  nd2_dangling : ∀ anchor block, pattern anchor = .nd2 block →
    ∀ label, label ≠ block.first → label ≠ block.second →
      ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
        (data.edgePartition (star.edge label)).blockCard sheet = 1
  nd3_dangling : ∀ anchor block, pattern anchor = .nd3 block →
    ∀ label,
      label ≠ block.first → label ≠ block.second → label ≠ block.third →
      ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
        (data.edgePartition (star.edge label)).blockCard sheet = 1

/-- The literal exterior-incidence information supplied by source Case
`{aux-r0}`.  An nd2 block's two absent branches are dangling, hence split
into singletons on that wall block.  For an nd3 block the unique absent
branch refines the singleton active branch on its endpoint. -/
structure ExteriorProfile (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) where
  nd2_dangling : ∀ anchor block, pattern anchor = .nd2 block →
    ∀ label, label ≠ block.first → label ≠ block.second →
      (data.edgePartition (star.edge label)).RefinesOnBlock
        ((data.vertexPartition wall).splitBlock anchor)
        (data.vertexPartition wall) anchor
  nd3_dangling : ∀ anchor block, pattern anchor = .nd3 block →
    ∀ label,
      label ≠ block.first → label ≠ block.second → label ≠ block.third →
      (data.edgePartition (star.edge label)).RefinesOnBlock
        ((data.vertexPartition wall).splitBlock anchor)
        (data.vertexPartition wall) anchor

/-- The actual common source input for the W4 auxiliary case.  Besides the
dangling-singleton classification, every old wall block has ramification
exactly zero.  At a four-valent target this is the displayed equality
`sum k_q = 2 |A| + 2`. -/
structure AuxR0Profile (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    extends ExteriorProfile data star pattern where
  ramificationZero : ∀ anchor sheet,
    (data.vertexPartition wall).Rel anchor sheet →
      (∑ label : Fin 4,
        ((data.edgePartition (star.edge label)).blockCountWithin
          (data.vertexPartition wall) sheet : ℤ)) =
        2 * ((data.vertexPartition wall).blockCard sheet : ℤ) + 2

namespace DanglingSingletonProfile

/-- Dangling-no-glue supplies the exact block-local singleton refinement used
by all three W4 resolutions. -/
theorem exterior {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : DanglingSingletonProfile data star pattern) :
    ExteriorProfile data star pattern where
  nd2_dangling := by
    intro anchor block hPattern label hFirst hSecond
    apply refinesOnBlock_splitBlock_of_blockCard_eq_one
    intro sheet hSheet
    exact profile.nd2_dangling anchor block hPattern label hFirst hSecond
      sheet hSheet
  nd3_dangling := by
    intro anchor block hPattern label hFirst hSecond hThird
    apply refinesOnBlock_splitBlock_of_blockCard_eq_one
    intro sheet hSheet
    exact profile.nd3_dangling anchor block hPattern label hFirst hSecond hThird
      sheet hSheet

end DanglingSingletonProfile

namespace ExteriorProfile

/-- The auxiliary source classification implies the exact block-local
exterior compatibility needed by every one of the three W4 resolutions. -/
theorem exterior {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : ExteriorProfile data star pattern) (pairing : Fin 3) :
    ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      ∀ anchor, (data.edgePartition edge).RefinesOnBlock
        (if star.right pairing edge then
          (blockwiseResolution data star pattern pairing anchor).right
        else
          (blockwiseResolution data star pattern pairing anchor).left)
        (data.vertexPartition wall) anchor := by
  intro edge hIncident anchor
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
            · simp only [hFirstSide, Bool.not_false, ite_true] at hEndpoint ⊢
              exact hEndpoint
            · simp only [hFirstSide, Bool.not_true, ite_true] at hEndpoint ⊢
              exact hEndpoint
          rw [hEndpoint']
          exact profile.nd2_dangling anchor block hPattern label hFirst
            hSecond
      · have hEndpoints := ResolutionW4.nd2Resolution_endpoints_of_ne
          (data.vertexPartition wall) anchor
          (W4TargetPairings.Pairing.labelRight pairing block.first)
          (W4TargetPairings.Pairing.labelRight pairing block.second) hSame
        cases hLabel : W4TargetPairings.Pairing.labelRight pairing label
        · simp only [Bool.false_eq, hEndpoints.1]
          exact (star.edgePartition_refines_wall data label).refinesOnBlock
            anchor
        · simp only [ite_true, hEndpoints.2]
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
          exact (profile.nd3_dangling anchor block hPattern label
            hFirst hSecond hThird).refinesAny_of_splitBlock fine
      · have hEndpoint := ResolutionW4.nd3Resolution_endpoint_of_other_side
          (data.vertexPartition wall) fine hFine
          (W4TargetPairings.Pairing.labelRight pairing singleton)
          (W4TargetPairings.Pairing.labelRight pairing label) hSide
        rw [hEndpoint]
        exact (star.edgePartition_refines_wall data label).refinesOnBlock anchor

/-- An nd2 dangling branch contributes one block for every block of any
endpoint partition refining the old wall partition. -/
theorem nd2_dangling_count {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : ExteriorProfile data star pattern)
    (anchor : Fin degree) (block : Nd2Block)
    (hPattern : pattern anchor = .nd2 block) (label : Fin 4)
    (hFirst : label ≠ block.first) (hSecond : label ≠ block.second)
    (endpoint : SheetPartition degree)
    (hEndpoint : endpoint.Refines (data.vertexPartition wall))
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel anchor sheet) :
    (data.edgePartition (star.edge label)).blockCountWithin endpoint sheet =
      endpoint.blockCard sheet := by
  exact SheetPartition.blockCountWithin_eq_blockCard_of_refinesOnBlock_splitBlock
    (data.edgePartition (star.edge label)) endpoint
    (data.vertexPartition wall) anchor sheet
    (profile.nd2_dangling anchor block hPattern label hFirst hSecond)
    hEndpoint hSheet

/-- The analogous exact contribution for the unique dangling branch of an
nd3 block. -/
theorem nd3_dangling_count {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : ExteriorProfile data star pattern)
    (anchor : Fin degree) (block : Nd3Block)
    (hPattern : pattern anchor = .nd3 block) (label : Fin 4)
    (hFirst : label ≠ block.first) (hSecond : label ≠ block.second)
    (hThird : label ≠ block.third) (endpoint : SheetPartition degree)
    (hEndpoint : endpoint.Refines (data.vertexPartition wall))
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel anchor sheet) :
    (data.edgePartition (star.edge label)).blockCountWithin endpoint sheet =
      endpoint.blockCard sheet := by
  exact SheetPartition.blockCountWithin_eq_blockCard_of_refinesOnBlock_splitBlock
    (data.edgePartition (star.edge label)) endpoint
    (data.vertexPartition wall) anchor sheet
    (profile.nd3_dangling anchor block hPattern label hFirst hSecond hThird)
    hEndpoint hSheet

/-- The original four-valent Riemann--Hurwitz inequality implies the exact
trivalent block-count inequality on either endpoint of every canonical W4
resolution. -/
theorem countAtSide {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : ExteriorProfile data star pattern)
    (hRiemannHurwitz : data.RiemannHurwitzAtTargetVertex wall)
    (pairing : Fin 3) (anchor : Fin degree)
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
              exact_mod_cast (profile.nd2_dangling_count anchor block hPattern
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
              exact_mod_cast profile.nd3_dangling_count anchor block hPattern
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
              exact_mod_cast profile.nd3_dangling_count anchor block hPattern
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

end ExteriorProfile

namespace AuxR0Profile

/-- The local ramification contribution of one canonical source block above
the four-valent wall.  This is the source's `r₀(A₀)`: the four induced edge
blocks, minus twice the sheet-block size and the constant two. -/
def wallBlockRamification
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (sourceBlock : WallBlock data wall) : ℤ :=
  (∑ label : Fin 4,
    ((data.edgePartition (star.edge label)).blockCountWithin
      (data.vertexPartition wall) sourceBlock.1 : ℤ)) -
    2 * ((data.vertexPartition wall).blockCard sourceBlock.1 : ℤ) - 2

/-- The W4 block sum is not an ad hoc quantity: it is exactly the target
change `ch(w₀)`.  The four-star equivalence merely reindexes the incident
target occurrences by `Fin 4`. -/
theorem targetChange_eq_sum_wallBlockRamification
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) :
    data.targetChange wall =
      ∑ sourceBlock : WallBlock data wall,
        wallBlockRamification data star sourceBlock := by
  unfold GluingDatum.targetChange GluingDatum.localRamification
  apply Finset.sum_congr rfl
  intro sourceBlock _
  rw [star.card_incidentEdges]
  rw [← star.sum_edge_eq_sum_incident (fun edge ↦
    ((data.edgePartition edge).blockCountWithin
      (data.vertexPartition wall) sourceBlock.1 : ℤ))]
  unfold wallBlockRamification
  ring

/-- Incoming Riemann--Hurwitz validity makes every W4 block ramification
nonnegative.  The four-star equivalence is used here to replace the abstract
incident-edge sum by the four source labels. -/
theorem wallBlockRamification_nonneg
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    (hRiemannHurwitz : data.RiemannHurwitzAtTargetVertex wall)
    (sourceBlock : WallBlock data wall) :
    0 ≤ wallBlockRamification data star sourceBlock := by
  have h := hRiemannHurwitz sourceBlock.1
  rw [star.card_incidentEdges] at h
  rw [← star.sum_edge_eq_sum_incident (fun edge ↦
    ((data.edgePartition edge).blockCountWithin
      (data.vertexPartition wall) sourceBlock.1 : ℤ))] at h
  unfold wallBlockRamification
  omega

/-- At a change-zero four-valent target, the sum of the nonnegative local
ramifications is zero, so every source block has `r₀ = 0`.  This is the exact
finite passage from Equation (C) in the paper to Case `{aux-r0}`. -/
theorem wallBlockRamification_eq_zero_of_sum_eq_zero
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    (hRiemannHurwitz : data.RiemannHurwitzAtTargetVertex wall)
    (hChangeZero :
      ∑ sourceBlock : WallBlock data wall,
        wallBlockRamification data star sourceBlock = 0)
    (sourceBlock : WallBlock data wall) :
    wallBlockRamification data star sourceBlock = 0 := by
  have hNonnegative : ∀ block ∈
      (Finset.univ : Finset (WallBlock data wall)),
      0 ≤ wallBlockRamification data star block := by
    intro block _hBlock
    exact wallBlockRamification_nonneg hRiemannHurwitz block
  exact (Finset.sum_eq_zero_iff_of_nonneg hNonnegative).mp hChangeZero
    sourceBlock (Finset.mem_univ sourceBlock)

/-- Construct the complete auxiliary W4 profile from the paper's genuinely
global source input.  Incoming validity supplies nonnegativity; the single
change-zero equation forces zero ramification on every source block.  Thus a
source classifier need not supply one equality per representative. -/
theorem ofValidChangeZero
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (exterior : ExteriorProfile data star pattern)
    (hValid : data.Valid)
    (hChangeZero :
      ∑ sourceBlock : WallBlock data wall,
        wallBlockRamification data star sourceBlock = 0) :
    AuxR0Profile data star pattern where
  toExteriorProfile := exterior
  ramificationZero := by
    intro _anchor sheet _hSheet
    let sourceBlock : WallBlock data wall := WallBlock.ofSheet data wall sheet
    have hZero := wallBlockRamification_eq_zero_of_sum_eq_zero
      (hValid.2 wall) hChangeZero sourceBlock
    have hRel : (data.vertexPartition wall).Rel sourceBlock.1 sheet := by
      exact (data.vertexPartition wall).rel_repr_left sheet
    have hBlock :
        (data.vertexPartition wall).block sourceBlock.1 =
          (data.vertexPartition wall).block sheet :=
      (data.vertexPartition wall).block_eq_of_rel hRel
    have hCount : ∀ label : Fin 4,
        (data.edgePartition (star.edge label)).blockCountWithin
            (data.vertexPartition wall) sourceBlock.1 =
          (data.edgePartition (star.edge label)).blockCountWithin
            (data.vertexPartition wall) sheet := by
      intro label
      simp only [SheetPartition.blockCountWithin, hBlock]
    have hCard :
        (data.vertexPartition wall).blockCard sourceBlock.1 =
          (data.vertexPartition wall).blockCard sheet := by
      simp only [SheetPartition.blockCard, hBlock]
    unfold wallBlockRamification at hZero
    simp_rw [hCount] at hZero
    rw [hCard] at hZero
    omega

/-- Exact zero ramification on every wall block implies the incoming datum's
four-valent Riemann--Hurwitz inequality at the wall vertex. -/
theorem riemannHurwitzAtTargetVertex
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : AuxR0Profile data star pattern) :
    data.RiemannHurwitzAtTargetVertex wall := by
  intro sheet
  have hZero := profile.ramificationZero
    ((data.vertexPartition wall).repr sheet) sheet
    ((data.vertexPartition wall).rel_repr_left sheet)
  rw [star.card_incidentEdges]
  rw [← star.sum_edge_eq_sum_incident (fun edge ↦
    ((data.edgePartition edge).blockCountWithin
      (data.vertexPartition wall) sheet : ℤ))]
  omega

/-- In an r0-nd2 block, the two active target branches each induce exactly
one source-edge block inside the old wall block. -/
theorem nd2_active_blockCountWithin
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : AuxR0Profile data star pattern)
    (anchor : Fin degree) (block : Nd2Block)
    (hPattern : pattern anchor = .nd2 block) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel anchor sheet) :
    (data.edgePartition (star.edge block.first)).blockCountWithin
          (data.vertexPartition wall) sheet = 1 ∧
      (data.edgePartition (star.edge block.second)).blockCountWithin
          (data.vertexPartition wall) sheet = 1 := by
  classical
  let active := block.activeLabels
  let value : Fin 4 → ℤ := fun label ↦
    ((data.edgePartition (star.edge label)).blockCountWithin
      (data.vertexPartition wall) sheet : ℤ)
  have hActiveFilter :
      (Finset.univ : Finset (Fin 4)).filter
          (fun label ↦ label ∈ active) = active := by
    ext label
    simp
  have hActiveCard : active.card = 2 := by
    simp [active, Nd2Block.activeLabels, block.distinct]
  have hInactiveCard :
      ((Finset.univ : Finset (Fin 4)).filter
        fun label ↦ ¬ label ∈ active).card = 2 := by
    have hPartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 4)))
      (fun label ↦ label ∈ active)
    rw [hActiveFilter, hActiveCard] at hPartition
    norm_num at hPartition
    omega
  have hInactiveSum :
      (∑ label ∈ (Finset.univ : Finset (Fin 4)).filter
        (fun label ↦ ¬ label ∈ active), value label) =
        2 * ((data.vertexPartition wall).blockCard sheet : ℤ) := by
    calc
      (∑ label ∈ (Finset.univ : Finset (Fin 4)).filter
          (fun label ↦ ¬ label ∈ active), value label) =
          ∑ _label ∈ (Finset.univ : Finset (Fin 4)).filter
            (fun label ↦ ¬ label ∈ active),
              ((data.vertexPartition wall).blockCard sheet : ℤ) := by
        apply Finset.sum_congr rfl
        intro label hLabel
        have hInactive : label ∉ block.activeLabels := by
          simpa [active] using (Finset.mem_filter.mp hLabel).2
        have hFirst : label ≠ block.first := by
          intro hEq
          exact hInactive ((block.mem_activeLabels label).mpr (Or.inl hEq))
        have hSecond : label ≠ block.second := by
          intro hEq
          exact hInactive ((block.mem_activeLabels label).mpr (Or.inr hEq))
        change
          ((data.edgePartition (star.edge label)).blockCountWithin
            (data.vertexPartition wall) sheet : ℤ) = _
        exact_mod_cast profile.toExteriorProfile.nd2_dangling_count anchor block
          hPattern label hFirst hSecond (data.vertexPartition wall)
          (SheetPartition.Refines.refl _) sheet hSheet
      _ = 2 * ((data.vertexPartition wall).blockCard sheet : ℤ) := by
        simp [hInactiveCard]
  have hPartition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 4)) (fun label ↦ label ∈ active) value
  rw [hActiveFilter, hInactiveSum] at hPartition
  have hZero := profile.ramificationZero anchor sheet hSheet
  change (∑ label : Fin 4, value label) =
    2 * ((data.vertexPartition wall).blockCard sheet : ℤ) + 2 at hZero
  rw [hZero] at hPartition
  have hActiveEquation :
      value block.first + value block.second +
          2 * ((data.vertexPartition wall).blockCard sheet : ℤ) =
        2 * ((data.vertexPartition wall).blockCard sheet : ℤ) + 2 := by
    simpa [active, Nd2Block.activeLabels, block.distinct] using hPartition
  have hFirstPositive : 1 ≤ value block.first := by
    have hNat := (data.edgePartition
      (star.edge block.first)).blockCountWithin_pos
        (data.vertexPartition wall) sheet
    have hInt : 0 < value block.first := by
      change (0 : ℤ) <
        ((data.edgePartition (star.edge block.first)).blockCountWithin
          (data.vertexPartition wall) sheet : ℤ)
      exact_mod_cast hNat
    omega
  have hSecondPositive : 1 ≤ value block.second := by
    have hNat := (data.edgePartition
      (star.edge block.second)).blockCountWithin_pos
        (data.vertexPartition wall) sheet
    have hInt : 0 < value block.second := by
      change (0 : ℤ) <
        ((data.edgePartition (star.edge block.second)).blockCountWithin
          (data.vertexPartition wall) sheet : ℤ)
      exact_mod_cast hNat
    omega
  have hFirst : value block.first = 1 := by omega
  have hSecond : value block.second = 1 := by omega
  constructor
  · change
      (((data.edgePartition (star.edge block.first)).blockCountWithin
        (data.vertexPartition wall) sheet : ℕ) : ℤ) = 1 at hFirst
    exact_mod_cast hFirst
  · change
      (((data.edgePartition (star.edge block.second)).blockCountWithin
        (data.vertexPartition wall) sheet : ℕ) : ℤ) = 1 at hSecond
    exact_mod_cast hSecond

/-- Cardinality form of the r0-nd2 local property: both active source-edge
classes are the complete old wall block. -/
theorem nd2_active_blockCard
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : AuxR0Profile data star pattern)
    (anchor : Fin degree) (block : Nd2Block)
    (hPattern : pattern anchor = .nd2 block) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel anchor sheet) :
    (data.edgePartition (star.edge block.first)).blockCard sheet =
          (data.vertexPartition wall).blockCard sheet ∧
      (data.edgePartition (star.edge block.second)).blockCard sheet =
          (data.vertexPartition wall).blockCard sheet := by
  obtain ⟨hFirst, hSecond⟩ :=
    profile.nd2_active_blockCountWithin anchor block hPattern sheet hSheet
  exact ⟨
    SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one
        (data.edgePartition (star.edge block.first))
        (data.vertexPartition wall)
        (star.edgePartition_refines_wall data block.first) sheet hFirst,
    SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one
        (data.edgePartition (star.edge block.second))
        (data.vertexPartition wall)
        (star.edgePartition_refines_wall data block.second) sheet hSecond⟩

end AuxR0Profile

/-- The source receipts still required after the W4 target, block-resolution,
and occurrence-list classifications have been constructed. -/
structure PairingReceipts (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) where
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ anchor, (data.edgePartition edge).RefinesOnBlock
      (if star.right pairing edge then
        (blockwiseResolution data star pattern pairing anchor).right
      else
        (blockwiseResolution data star pattern pairing anchor).left)
      (data.vertexPartition wall) anchor
  left_riemannHurwitz : ∀ anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (blockwiseResolution data star pattern pairing anchor).left
      ((blockwiseResolution data star pattern pairing anchor).newEdge ::
        (star.leftEdges pairing).map data.edgePartition) anchor
  right_riemannHurwitz : ∀ anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    LocalResolution.RiemannHurwitzAtBlock (data.vertexPartition wall)
      (blockwiseResolution data star pattern pairing anchor).right
      ((blockwiseResolution data star pattern pairing anchor).newEdge ::
        (star.rightEdges pairing).map data.edgePartition) anchor

/-- Source-facing W4 receipts stated as the actual trivalent block-count
inequalities.  The two old occurrences on each endpoint are already enumerated
canonically by `FourStar.leftEdges` and `FourStar.rightEdges`; the full local
Riemann--Hurwitz propositions are derived below. -/
structure PairingCounts (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) where
  exterior : ∀ edge : target.edges,
    ((edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) →
    ∀ anchor, (data.edgePartition edge).RefinesOnBlock
      (if star.right pairing edge then
        (blockwiseResolution data star pattern pairing anchor).right
      else
        (blockwiseResolution data star pattern pairing anchor).left)
      (data.vertexPartition wall) anchor
  left_counts : ∀ anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
      (((blockwiseResolution data star pattern pairing anchor).newEdge ::
          (star.leftEdges pairing).map data.edgePartition).map
        (fun edge ↦ (edge.blockCountWithin
          (blockwiseResolution data star pattern pairing anchor).left sheet :
            ℤ))).sum ≥
        ((blockwiseResolution data star pattern pairing anchor).left.blockCard
          sheet : ℤ) + 2
  right_counts : ∀ anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
      (((blockwiseResolution data star pattern pairing anchor).newEdge ::
          (star.rightEdges pairing).map data.edgePartition).map
        (fun edge ↦ (edge.blockCountWithin
          (blockwiseResolution data star pattern pairing anchor).right sheet :
            ℤ))).sum ≥
        ((blockwiseResolution data star pattern pairing anchor).right.blockCard
          sheet : ℤ) + 2

/-- Source-facing validity input for all three W4 pairings.  The auxiliary
`r0` classification supplies dangling branches once, while endpoint count
inequalities remain indexed by the three target pairings. -/
structure SourceCounts (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) where
  exterior : ExteriorProfile data star pattern
  left_counts : ∀ pairing anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
      (((blockwiseResolution data star pattern pairing anchor).newEdge ::
          (star.leftEdges pairing).map data.edgePartition).map
        (fun edge ↦ (edge.blockCountWithin
          (blockwiseResolution data star pattern pairing anchor).left sheet :
            ℤ))).sum ≥
        ((blockwiseResolution data star pattern pairing anchor).left.blockCard
          sheet : ℤ) + 2
  right_counts : ∀ pairing anchor,
    (data.vertexPartition wall).repr anchor = anchor →
    ∀ sheet, (data.vertexPartition wall).Rel anchor sheet →
      (((blockwiseResolution data star pattern pairing anchor).newEdge ::
          (star.rightEdges pairing).map data.edgePartition).map
        (fun edge ↦ (edge.blockCountWithin
          (blockwiseResolution data star pattern pairing anchor).right sheet :
            ℤ))).sum ≥
        ((blockwiseResolution data star pattern pairing anchor).right.blockCard
          sheet : ℤ) + 2

/-- The auxiliary dangling classification plus the original four-valent
Riemann--Hurwitz condition supplies every source-count receipt; no additional
endpoint inequality is an independent input. -/
theorem ExteriorProfile.sourceCounts
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : ExteriorProfile data star pattern)
    (hRiemannHurwitz : data.RiemannHurwitzAtTargetVertex wall) :
    SourceCounts data star pattern where
  exterior := profile
  left_counts := by
    intro pairing anchor _hAnchor sheet hSheet
    simpa [oldEdgesAtSide, endpointAtSide] using
      profile.countAtSide hRiemannHurwitz pairing anchor sheet hSheet false
  right_counts := by
    intro pairing anchor _hAnchor sheet hSheet
    simpa [oldEdgesAtSide, endpointAtSide] using
      profile.countAtSide hRiemannHurwitz pairing anchor sheet hSheet true

namespace SourceCounts

/-- Derive one pairing's complete validity receipts from the common source
classification. -/
theorem pairingCounts {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (source : SourceCounts data star pattern) (pairing : Fin 3) :
    PairingCounts data star pattern pairing where
  exterior := source.exterior.exterior pairing
  left_counts := source.left_counts pairing
  right_counts := source.right_counts pairing

end SourceCounts

/-- The paper's common auxiliary r0 profile supplies all three pairings'
source-count receipts without a separate validity hypothesis. -/
theorem AuxR0Profile.sourceCounts
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : AuxR0Profile data star pattern) :
    SourceCounts data star pattern :=
  profile.toExteriorProfile.sourceCounts
    profile.riemannHurwitzAtTargetVertex

/-- Produce one pairing's complete count receipts directly from the auxiliary
dangling classification and the incoming datum's wall validity. -/
theorem ExteriorProfile.pairingCounts
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : ExteriorProfile data star pattern)
    (hRiemannHurwitz : data.RiemannHurwitzAtTargetVertex wall)
    (pairing : Fin 3) :
    PairingCounts data star pattern pairing :=
  (profile.sourceCounts hRiemannHurwitz).pairingCounts pairing

/-- One pairing's receipts directly from the source's zero-ramification
auxiliary profile. -/
theorem AuxR0Profile.pairingCounts
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (profile : AuxR0Profile data star pattern) (pairing : Fin 3) :
    PairingCounts data star pattern pairing :=
  profile.sourceCounts.pairingCounts pairing

namespace PairingCounts

/-- Trivalent count receipts imply the exact endpoint Riemann--Hurwitz
receipts required by global assembly. -/
theorem toPairingReceipts {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (counts : PairingCounts data star pattern pairing) :
    PairingReceipts data star pattern pairing where
  exterior := counts.exterior
  left_riemannHurwitz := by
    intro anchor hAnchor sheet hSheet
    have hCounts := counts.left_counts anchor hAnchor sheet hSheet
    have hLength :
        ((blockwiseResolution data star pattern pairing anchor).newEdge ::
          (star.leftEdges pairing).map data.edgePartition).length = 3 := by
      simp
    rw [hLength]
    omega
  right_riemannHurwitz := by
    intro anchor hAnchor sheet hSheet
    have hCounts := counts.right_counts anchor hAnchor sheet hSheet
    have hLength :
        ((blockwiseResolution data star pattern pairing anchor).newEdge ::
          (star.rightEdges pairing).map data.edgePartition).length = 3 := by
      simp
    rw [hLength]
    omega

end PairingCounts

namespace PairingReceipts

/-- Assemble one pairing's source receipts into an actual global candidate. -/
noncomputable def candidate {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing) :
    Candidate target degree data wall where
  right := star.right pairing
  resolution := blockwiseResolution data star pattern pairing
  contracts := blockwiseResolution_contracts data star pattern pairing
  exterior := receipts.exterior
  leftEdges := star.leftEdges pairing
  rightEdges := star.rightEdges pairing
  leftEdges_eq := star.leftEdges_eq pairing
  rightEdges_eq := star.rightEdges_eq pairing
  left_riemannHurwitz := receipts.left_riemannHurwitz
  right_riemannHurwitz := receipts.right_riemannHurwitz

/-- Classifying the actual regrown source occurrence by old wall blocks
returns the canonical block containing its sheet. -/
theorem wallBlock_newSourceEdge
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) :
    WallBlock.ofSourceEdge data wall receipts.candidate.datum
        (receipts.candidate.newSourceEdge sheet) =
      WallBlock.ofSheet data wall sheet := by
  apply Subtype.ext
  change
    (data.vertexPartition wall).repr
        ((wholeResolution data star pattern pairing).newEdge.repr sheet) =
      (data.vertexPartition wall).repr sheet
  have hRefines :
      (wholeResolution data star pattern pairing).newEdge.Refines
        (data.vertexPartition wall) :=
    (wholeResolution data star pattern pairing).edge_refines_left.trans
      (wholeResolution_contracts data star pattern pairing).left_refines
  exact hRefines.rel
    ((wholeResolution data star pattern pairing).newEdge.rel_repr_left sheet)

/-- A retained old source occurrence incident to the W4 wall is classified by
the same canonical wall block as its chosen sheet. -/
theorem wallBlock_oldSourceEdge_of_incident
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (edge : target.edges) (sheet : Fin degree)
    (hIncident : (edge : target.V × target.V).1 = wall ∨
      (edge : target.V × target.V).2 = wall) :
    WallBlock.ofSourceEdge data wall receipts.candidate.datum
        (receipts.candidate.oldSourceEdge (data.sourceEdge edge sheet)) =
      WallBlock.ofSheet data wall sheet := by
  apply Subtype.ext
  change
    (data.vertexPartition wall).repr
        ((data.edgePartition edge).repr sheet) =
      (data.vertexPartition wall).repr sheet
  have hRefines : (data.edgePartition edge).Refines
      (data.vertexPartition wall) := by
    rcases hIncident with hLeft | hRight
    · simpa [hLeft] using data.refines_left edge
    · simpa [hRight] using data.refines_right edge
  exact hRefines.rel ((data.edgePartition edge).rel_repr_left sheet)

/-- For a same-side nd2 block, the actual new quotient-source edge in the
globally valid candidate has unit dilation index. -/
theorem sourceEdgeIndex_newSourceEdge_nd2_of_same
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) (block : Nd2Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd2 block)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    receipts.candidate.datum.sourceEdgeIndex
        (receipts.candidate.newSourceEdge sheet) = 1 := by
  rw [Candidate.sourceEdgeIndex_newSourceEdge]
  change (wholeResolution data star pattern pairing).newEdge.blockCard sheet = 1
  exact wholeResolution_nd2_newEdge_blockCard_of_same data star pattern pairing
    sheet block hPattern hSame

/-- For an opposite-side nd2 block, the actual new quotient-source edge
retains the old wall-block dilation index. -/
theorem sourceEdgeIndex_newSourceEdge_nd2_of_ne
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) (block : Nd2Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd2 block)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    receipts.candidate.datum.sourceEdgeIndex
        (receipts.candidate.newSourceEdge sheet) =
      (data.vertexPartition wall).blockCard sheet := by
  rw [Candidate.sourceEdgeIndex_newSourceEdge]
  change
    (wholeResolution data star pattern pairing).newEdge.blockCard sheet =
      (data.vertexPartition wall).blockCard sheet
  exact wholeResolution_nd2_newEdge_blockCard_of_ne data star pattern pairing
    sheet block hPattern hNe

/-- If the first old branch fills the classified nd2 wall block, the regrown
edge and that literal old source occurrence have equal dilation indices. -/
theorem sourceEdgeIndex_newSourceEdge_nd2_eq_first
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) (block : Nd2Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd2 block)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (hFirst : (data.edgePartition (star.edge block.first)).blockCard sheet =
      (data.vertexPartition wall).blockCard sheet) :
    receipts.candidate.datum.sourceEdgeIndex
        (receipts.candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex (data.sourceEdge (star.edge block.first) sheet) := by
  rw [sourceEdgeIndex_newSourceEdge_nd2_of_ne receipts sheet block hPattern hNe]
  rw [GluingDatum.sourceEdgeIndex_sourceEdge, hFirst]

/-- The same nd2 denominator comparison for the second old branch. -/
theorem sourceEdgeIndex_newSourceEdge_nd2_eq_second
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) (block : Nd2Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd2 block)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (hSecond : (data.edgePartition (star.edge block.second)).blockCard sheet =
      (data.vertexPartition wall).blockCard sheet) :
    receipts.candidate.datum.sourceEdgeIndex
        (receipts.candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex (data.sourceEdge (star.edge block.second) sheet) := by
  rw [sourceEdgeIndex_newSourceEdge_nd2_of_ne receipts sheet block hPattern hNe]
  rw [GluingDatum.sourceEdgeIndex_sourceEdge, hSecond]

/-- For an nd3 block, the actual new quotient-source edge has the same
dilation index as the old branch isolated by the pairing. -/
theorem sourceEdgeIndex_newSourceEdge_nd3
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) (block : Nd3Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd3 block) :
    receipts.candidate.datum.sourceEdgeIndex
        (receipts.candidate.newSourceEdge sheet) =
      (data.edgePartition
        (star.edge (block.singletonLabel pairing))).blockCard sheet := by
  rw [Candidate.sourceEdgeIndex_newSourceEdge]
  change
    (wholeResolution data star pattern pairing).newEdge.blockCard sheet =
      (data.edgePartition
        (star.edge (block.singletonLabel pairing))).blockCard sheet
  exact wholeResolution_nd3_newEdge_blockCard data star pattern pairing sheet
    block hPattern

/-- The nd3 index formula identifies the regrown edge with the literal old
source occurrence on the singleton branch. -/
theorem sourceEdgeIndex_newSourceEdge_nd3_eq_old
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing)
    (sheet : Fin degree) (block : Nd3Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd3 block) :
    receipts.candidate.datum.sourceEdgeIndex
        (receipts.candidate.newSourceEdge sheet) =
      data.sourceEdgeIndex
        (data.sourceEdge (star.edge (block.singletonLabel pairing)) sheet) := by
  rw [sourceEdgeIndex_newSourceEdge_nd3 receipts sheet block hPattern]
  rw [GluingDatum.sourceEdgeIndex_sourceEdge]

/-- The candidate's pasted local resolution is the whole-wall W4 resolution
constructed independently in `W4Assembly`. -/
theorem pasted_resolution_eq {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (receipts : PairingReceipts data star pattern pairing) :
    LocalResolution.paste (data.vertexPartition wall)
        receipts.candidate.resolution receipts.candidate.contracts =
      wholeResolution data star pattern pairing := by
  rfl

end PairingReceipts

namespace PairingCounts

/-- Assemble one pairing directly from the source's trivalent count
inequalities. -/
noncomputable def candidate {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern} {pairing : Fin 3}
    (counts : PairingCounts data star pattern pairing) :
    Candidate target degree data wall :=
  counts.toPairingReceipts.candidate

end PairingCounts

/-- The three occurrence-labelled global candidates required by Equation (1). -/
noncomputable def candidates (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    (receipts : ∀ pairing, PairingReceipts data star pattern pairing) :
    Fin 3 → Candidate target degree data wall :=
  fun pairing ↦ (receipts pairing).candidate

/-- The same three global candidates, with source obligations exposed as the
paper's block-count inequalities rather than preassembled RH propositions. -/
noncomputable def candidatesOfCounts (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    (counts : ∀ pairing, PairingCounts data star pattern pairing) :
    Fin 3 → Candidate target degree data wall :=
  fun pairing ↦ (counts pairing).candidate

/-! ## Canonical W4 length-matrix presentations

Every outgoing target edge has the common coordinate type
`Option target.edges`: `none` is the regrown wall edge and `some edge` is a
retained old occurrence.  A source classifier therefore needs only one common
list of retained old source edges for every stable row and the list of
regrown-edge sheets inserted in that row for each pairing.  The construction
below turns those lists into the three actual length-matrix presentations and
proves their off-wall columns agree automatically. -/

/-- The canonical W4 presentation obtained by lifting a common old path and
then adjoining the regrown source-edge occurrences assigned to its row.  Path
order is immaterial to the length matrix; retaining lists preserves repeated
occurrences. -/
noncomputable def canonicalPresentationOfPaths
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) :
    (counts pairing).candidate.datum.LengthMatrixPresentation
      (Option target.edges) where
  targetEdge := TargetExpansion.occurrenceEquiv target wall
    (counts pairing).candidate.right
  path row :=
    (oldPath row).map (counts pairing).candidate.oldSourceEdge ++
      (newSheets pairing row).map (counts pairing).candidate.newSourceEdge

/-- A retained source edge contributes to precisely its canonically labelled
old target column, with its original dilation index. -/
@[simp] theorem canonicalPresentationOfPaths_coefficient_oldSourceEdge
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (edge : data.SourceEdge)
    (column : Option target.edges) :
    GluingDatum.LengthMatrixPresentation.coefficient
      (canonicalPresentationOfPaths counts oldPath newSheets pairing)
      ((counts pairing).candidate.oldSourceEdge edge) column =
        if column = some edge.1.1 then
          (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) else 0 := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.coefficient
  rw [Candidate.sourceEdgeIndex_oldSourceEdge]
  simp [canonicalPresentationOfPaths]

/-- A regrown source edge contributes zero to every retained old target
column. -/
@[simp] theorem canonicalPresentationOfPaths_coefficient_newSourceEdge_some
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (sheet : Fin degree) (edge : target.edges) :
    GluingDatum.LengthMatrixPresentation.coefficient
      (canonicalPresentationOfPaths counts oldPath newSheets pairing)
      ((counts pairing).candidate.newSourceEdge sheet) (some edge) = 0 := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.coefficient
  simp [canonicalPresentationOfPaths]

/-- Every retained old column of a canonical W4 presentation is computed
solely from the common old path, hence is independent of the pairing and of
the regrown-edge assignments. -/
theorem canonicalPresentationOfPaths_matrix_some
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (row : Option target.edges) (column : target.edges) :
    GluingDatum.LengthMatrixPresentation.matrix
        (canonicalPresentationOfPaths counts oldPath newSheets pairing)
        row (some column) =
      ((oldPath row).map fun edge ↦
        if (some column : Option target.edges) = some edge.1.1 then
          (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) else 0).sum := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.matrix
    GluingDatum.LengthMatrixPresentation.row
  rw [show
    (canonicalPresentationOfPaths counts oldPath newSheets pairing).path row =
      (oldPath row).map (counts pairing).candidate.oldSourceEdge ++
        (newSheets pairing row).map
          (counts pairing).candidate.newSourceEdge by rfl]
  rw [List.map_append, List.sum_append, List.map_map, List.map_map]
  change
    (((oldPath row).map fun edge ↦
      GluingDatum.LengthMatrixPresentation.coefficient
        (canonicalPresentationOfPaths counts oldPath newSheets pairing)
        ((counts pairing).candidate.oldSourceEdge edge) (some column)).sum +
      ((newSheets pairing row).map fun sheet ↦
        GluingDatum.LengthMatrixPresentation.coefficient
          (canonicalPresentationOfPaths counts oldPath newSheets pairing)
          ((counts pairing).candidate.newSourceEdge sheet) (some column)).sum) = _
  have hOld :
      ((oldPath row).map fun edge ↦
        GluingDatum.LengthMatrixPresentation.coefficient
          (canonicalPresentationOfPaths counts oldPath newSheets pairing)
          ((counts pairing).candidate.oldSourceEdge edge) (some column)).sum =
        ((oldPath row).map fun edge ↦
          if (some column : Option target.edges) = some edge.1.1 then
            (1 : ℚ) / (data.sourceEdgeIndex edge : ℚ) else 0).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro edge _hEdge
    exact canonicalPresentationOfPaths_coefficient_oldSourceEdge
      counts oldPath newSheets pairing edge (some column)
  have hNew :
      ((newSheets pairing row).map fun sheet ↦
        GluingDatum.LengthMatrixPresentation.coefficient
          (canonicalPresentationOfPaths counts oldPath newSheets pairing)
          ((counts pairing).candidate.newSourceEdge sheet) (some column)).sum =
        0 := by
    simp_rw [canonicalPresentationOfPaths_coefficient_newSourceEdge_some]
    simp
  rw [hOld, hNew, add_zero]

/-- Canonically presented W4 resolutions agree in every column except the
regrown edge `none`.  This is the length-matrix compatibility needed by the
wall determinant argument, derived from the path construction rather than
assumed independently. -/
theorem canonicalPresentations_agreeOffWall
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree)) :
    ∀ first second,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix
          (canonicalPresentationOfPaths counts oldPath newSheets first))
        (GluingDatum.LengthMatrixPresentation.matrix
          (canonicalPresentationOfPaths counts oldPath newSheets second)) none := by
  intro first second row column hColumn
  cases column with
  | none => exact (hColumn rfl).elim
  | some edge =>
      rw [canonicalPresentationOfPaths_matrix_some,
        canonicalPresentationOfPaths_matrix_some]

/-- Source-level record of the regrown sheets assigned to one wall block,
before they are turned into source edges of a particular outgoing candidate.
This is the finite path-incidence object that the auxiliary W4 classification
must compute. -/
noncomputable def canonicalNewSheetOccurrences
    {data : GluingDatum target degree}
    (sourceBlock : WallBlock data wall)
    (newSheets : Option target.edges → List (Fin degree)) :
    Multiset (Option target.edges × Fin degree) :=
  ∑ row, Multiset.ofList
    ((newSheets row).filterMap fun sheet ↦
      if WallBlock.ofSheet data wall sheet = sourceBlock then
        some (row, sheet)
      else none)

/-- Retained old path edges never contribute to the regrown wall column of a
canonical presentation. -/
@[simp] theorem canonicalPresentationOfPaths_matchingOccurrence_old_none
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (row : Option target.edges) (edge : data.SourceEdge) :
    GluingDatum.LengthMatrixPresentation.matchingOccurrence
      (canonicalPresentationOfPaths counts oldPath newSheets pairing)
      (WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
      sourceBlock none row ((counts pairing).candidate.oldSourceEdge edge) =
        none := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.matchingOccurrence
  simp [canonicalPresentationOfPaths]

/-- A regrown sheet contributes to its canonical old wall block in the wall
column, and to no other block. -/
@[simp] theorem canonicalPresentationOfPaths_matchingOccurrence_new_none
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (row : Option target.edges) (sheet : Fin degree) :
    GluingDatum.LengthMatrixPresentation.matchingOccurrence
      (canonicalPresentationOfPaths counts oldPath newSheets pairing)
      (WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
      sourceBlock none row ((counts pairing).candidate.newSourceEdge sheet) =
        if WallBlock.ofSheet data wall sheet = sourceBlock then
          some (row, (counts pairing).candidate.newSourceEdge sheet)
        else none := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.matchingOccurrence
  have hWallBlock :
      WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum
          ((counts pairing).candidate.newSourceEdge sheet) =
        WallBlock.ofSheet data wall sheet :=
    PairingReceipts.wallBlock_newSourceEdge
      (counts pairing).toPairingReceipts sheet
  rw [hWallBlock]
  simp [canonicalPresentationOfPaths]

/-- The literal wall-column occurrences of a canonical presentation are
exactly its source-level regrown-sheet occurrences, mapped to the actual new
source edges.  In particular, old path data cannot contaminate the W4 local
classification. -/
theorem canonicalPresentationOfPaths_blockColumnOccurrences_none
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) :
    GluingDatum.LengthMatrixPresentation.blockColumnOccurrences
      (canonicalPresentationOfPaths counts oldPath newSheets pairing)
      (WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
      sourceBlock none =
        (canonicalNewSheetOccurrences sourceBlock (newSheets pairing)).map
          (fun occurrence ↦
            (occurrence.1,
              (counts pairing).candidate.newSourceEdge occurrence.2)) := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.blockColumnOccurrences
  have hMap :
      (canonicalNewSheetOccurrences sourceBlock (newSheets pairing)).map
          (fun occurrence ↦
            (occurrence.1,
              (counts pairing).candidate.newSourceEdge occurrence.2)) =
        ∑ row, (Multiset.ofList
          ((newSheets pairing row).filterMap fun sheet ↦
            if WallBlock.ofSheet data wall sheet = sourceBlock then
              some (row, sheet)
            else none)).map
          (fun occurrence ↦
            (occurrence.1,
              (counts pairing).candidate.newSourceEdge occurrence.2)) := by
    unfold canonicalNewSheetOccurrences
    exact map_sum
      (Multiset.mapAddMonoidHom fun occurrence :
        Option target.edges × Fin degree ↦
          (occurrence.1,
            (counts pairing).candidate.newSourceEdge occurrence.2))
      (fun row ↦ Multiset.ofList
        ((newSheets pairing row).filterMap fun sheet ↦
          if WallBlock.ofSheet data wall sheet = sourceBlock then
            some (row, sheet)
          else none)) Finset.univ
  rw [hMap]
  apply Finset.sum_congr rfl
  intro row _hRow
  rw [show
    (canonicalPresentationOfPaths counts oldPath newSheets pairing).path row =
      (oldPath row).map (counts pairing).candidate.oldSourceEdge ++
        (newSheets pairing row).map
          (counts pairing).candidate.newSourceEdge by rfl]
  rw [List.filterMap_append]
  change Multiset.ofList _ + Multiset.ofList _ = _
  have hOld :
      ((oldPath row).map (counts pairing).candidate.oldSourceEdge).filterMap
        (GluingDatum.LengthMatrixPresentation.matchingOccurrence
          (canonicalPresentationOfPaths counts oldPath newSheets pairing)
          (WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
          sourceBlock none row) = [] := by
    simp
  rw [hOld]
  change 0 + _ = _
  rw [zero_add]
  simp only [List.filterMap_map]
  generalize hSheets : newSheets pairing row = sheets
  clear hSheets
  induction sheets with
  | nil => simp
  | cons sheet rest ih =>
      have ih' := ih
      simp only [Function.comp_apply] at ih'
      simp_rw [canonicalPresentationOfPaths_matchingOccurrence_new_none] at ih'
      by_cases hSheet : WallBlock.ofSheet data wall sheet = sourceBlock
      · simp [Function.comp_apply,
          canonicalPresentationOfPaths_matchingOccurrence_new_none, hSheet]
        exact Multiset.coe_eq_coe.mp (by
          simpa only [Multiset.map_coe] using ih')
      · simp [Function.comp_apply,
          canonicalPresentationOfPaths_matchingOccurrence_new_none, hSheet]
        exact Multiset.coe_eq_coe.mp (by
          simpa only [Multiset.map_coe] using ih')

/-- The four retained target columns incident to the contracted W4 vertex.
These, rather than every old target column, are the right-hand terms in the
source's Equation (1). -/
noncomputable def canonicalW4OldColumns
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges] : Finset (Option target.edges) :=
  Finset.univ.image fun label ↦ some (star.edge label)

/-- A canonical incident old column is never the regrown wall column. -/
theorem canonicalW4OldColumns_ne_none
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (column : Option target.edges)
    (hColumn : column ∈ canonicalW4OldColumns star) :
    column ≠ none := by
  intro hEq
  subst column
  simp [canonicalW4OldColumns] at hColumn

/-- Occurrences from one common old stable path at one retained target column,
still expressed in the contracted datum before lifting to an outgoing
candidate. -/
noncomputable def canonicalOldPathRowOccurrences
    {data : GluingDatum target degree}
    [DecidableEq target.edges]
    (sourceBlock : WallBlock data wall)
    (oldPath : Option target.edges → List data.SourceEdge)
    (column row : Option target.edges) :
    Multiset (Option target.edges × data.SourceEdge) :=
  Multiset.ofList ((oldPath row).filterMap fun edge ↦
    if WallBlock.ofSheet data wall edge.1.2 = sourceBlock ∧
        column = some edge.1.1 then
      some (row, edge)
    else none)

/-- The contracted source's literal occurrences over the four W4 branches,
grouped by one old wall block. -/
noncomputable def canonicalOldPathOccurrences
    {data : GluingDatum target degree}
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (sourceBlock : WallBlock data wall)
    (oldPath : Option target.edges → List data.SourceEdge) :
    Multiset (Option target.edges × data.SourceEdge) :=
  ∑ column ∈ canonicalW4OldColumns star,
    ∑ row, canonicalOldPathRowOccurrences sourceBlock oldPath column row

/-- For an arbitrary retained column, matching a lifted old edge is exactly
the corresponding source-level wall-block and target-occurrence test. -/
@[simp] theorem canonicalPresentationOfPaths_matchingOccurrence_old
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (row column : Option target.edges) (edge : data.SourceEdge) :
    GluingDatum.LengthMatrixPresentation.matchingOccurrence
      (canonicalPresentationOfPaths counts oldPath newSheets pairing)
      (WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
      sourceBlock column row ((counts pairing).candidate.oldSourceEdge edge) =
        if WallBlock.ofSheet data wall edge.1.2 = sourceBlock ∧
            column = some edge.1.1 then
          some (row, (counts pairing).candidate.oldSourceEdge edge)
        else none := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.matchingOccurrence
  simp [canonicalPresentationOfPaths, WallBlock.ofSourceEdge,
    WallBlock.ofSheet]
  rfl

/-- Regrown source edges contribute nothing to a retained old column. -/
@[simp] theorem canonicalPresentationOfPaths_matchingOccurrence_new_some
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (sourceBlock : WallBlock data wall)
    (row : Option target.edges) (column : target.edges) (sheet : Fin degree) :
    GluingDatum.LengthMatrixPresentation.matchingOccurrence
      (canonicalPresentationOfPaths counts oldPath newSheets pairing)
      (WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
      sourceBlock (some column) row
        ((counts pairing).candidate.newSourceEdge sheet) = none := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.matchingOccurrence
  simp [canonicalPresentationOfPaths]

/-- The four incident old-column occurrences in any canonical outgoing
presentation are precisely the common contracted old-path occurrences, with
each source edge lifted into that candidate.  Thus the right-hand side of
Equation (1) is independent of all regrown-edge choices. -/
theorem canonicalPresentationOfPaths_blockColumnsOccurrences_old
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (pairing : Fin 3) (sourceBlock : WallBlock data wall) :
    GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
      (canonicalPresentationOfPaths counts oldPath newSheets pairing)
      (WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
      sourceBlock (canonicalW4OldColumns star) =
        (canonicalOldPathOccurrences star sourceBlock oldPath).map
          (fun occurrence ↦
            (occurrence.1,
              (counts pairing).candidate.oldSourceEdge occurrence.2)) := by
  classical
  unfold GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
  let liftOccurrence :
      Option target.edges × data.SourceEdge →
        Option target.edges × (counts pairing).candidate.datum.SourceEdge :=
    fun occurrence ↦
      (occurrence.1,
        (counts pairing).candidate.oldSourceEdge occurrence.2)
  have hMap :
      (canonicalOldPathOccurrences star sourceBlock oldPath).map
          liftOccurrence =
        ∑ column ∈ canonicalW4OldColumns star,
          ∑ row, (canonicalOldPathRowOccurrences sourceBlock oldPath column row).map
            liftOccurrence := by
    unfold canonicalOldPathOccurrences
    calc
      (∑ column ∈ canonicalW4OldColumns star,
          ∑ row, canonicalOldPathRowOccurrences sourceBlock oldPath column row).map
          liftOccurrence =
          ∑ column ∈ canonicalW4OldColumns star,
            (∑ row,
              canonicalOldPathRowOccurrences sourceBlock oldPath column row).map
              liftOccurrence := by
            exact map_sum (Multiset.mapAddMonoidHom liftOccurrence)
              (fun column ↦ ∑ row,
                canonicalOldPathRowOccurrences sourceBlock oldPath column row)
              (canonicalW4OldColumns star)
      _ = ∑ column ∈ canonicalW4OldColumns star,
          ∑ row, (canonicalOldPathRowOccurrences sourceBlock oldPath column row).map
            liftOccurrence := by
            apply Finset.sum_congr rfl
            intro column _hColumn
            exact map_sum (Multiset.mapAddMonoidHom liftOccurrence)
              (fun row ↦
                canonicalOldPathRowOccurrences sourceBlock oldPath column row)
              Finset.univ
  change _ = (canonicalOldPathOccurrences star sourceBlock oldPath).map
    liftOccurrence
  rw [hMap]
  apply Finset.sum_congr rfl
  intro column hColumn
  have hColumnNe := canonicalW4OldColumns_ne_none star column hColumn
  cases column with
  | none => exact (hColumnNe rfl).elim
  | some targetEdge =>
      apply Finset.sum_congr rfl
      intro row _hRow
      rw [show
        (canonicalPresentationOfPaths counts oldPath newSheets pairing).path row =
          (oldPath row).map (counts pairing).candidate.oldSourceEdge ++
            (newSheets pairing row).map
              (counts pairing).candidate.newSourceEdge by rfl]
      rw [List.filterMap_append]
      change Multiset.ofList _ + Multiset.ofList _ = _
      have hNew :
          ((newSheets pairing row).map
            (counts pairing).candidate.newSourceEdge).filterMap
            (GluingDatum.LengthMatrixPresentation.matchingOccurrence
              (canonicalPresentationOfPaths counts oldPath newSheets pairing)
              (WallBlock.ofSourceEdge data wall
                (counts pairing).candidate.datum)
              sourceBlock (some targetEdge) row) = [] := by
        simp
      rw [hNew]
      change _ + 0 = _
      rw [add_zero]
      simp only [List.filterMap_map]
      unfold canonicalOldPathRowOccurrences
      generalize hEdges : oldPath row = edges
      clear hEdges
      induction edges with
      | nil => simp
      | cons edge rest ih =>
          have ih' := ih
          simp only [Function.comp_apply] at ih'
          simp_rw [canonicalPresentationOfPaths_matchingOccurrence_old] at ih'
          simp only [Option.some.injEq] at ih'
          by_cases hEdge :
              WallBlock.ofSheet data wall edge.1.2 = sourceBlock ∧
                targetEdge = edge.1.1
          · simp [Function.comp_apply,
              canonicalPresentationOfPaths_matchingOccurrence_old, hEdge,
              liftOccurrence]
            rw [hEdge.2] at ih'
            exact Multiset.coe_eq_coe.mp (by
              simpa only [Multiset.map_coe, liftOccurrence] using ih')
          · simp [Function.comp_apply,
              canonicalPresentationOfPaths_matchingOccurrence_old, hEdge,
              liftOccurrence]
            exact Multiset.coe_eq_coe.mp (by
              simpa only [Multiset.map_coe, liftOccurrence] using ih')

/-- The literal regrown-edge path occurrence for one candidate, with its
stable-row label supplied by the source presentation. -/
noncomputable def newPathOccurrenceOfCounts
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    {coordinate : Type*} (newRow : Fin 3 → coordinate)
    (sourceSheet : Fin degree) (pairing : Fin 3) :
    coordinate × (counts pairing).candidate.datum.SourceEdge :=
  (newRow pairing,
    (counts pairing).candidate.newSourceEdge sourceSheet)

/-- The literal retained old-branch occurrence in candidate zero, with its
stable-row label supplied by the source presentation. -/
noncomputable def oldPathOccurrenceOfCounts
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    {pattern : Fin degree → BlockPattern}
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    {coordinate : Type*} (oldRow : Fin 4 → coordinate)
    (sourceSheet : Fin degree) (label : Fin 4) :
    coordinate × (counts 0).candidate.datum.SourceEdge :=
  (oldRow label,
    (counts 0).candidate.oldSourceEdge
      (data.sourceEdge (star.edge label) sourceSheet))

/-- Construct the nd2 receipt for an actual W4 wall block.  The source supplies
only its common auxiliary r0 profile, the literal occurrence profiles, and
their stable-row labels.  Zero ramification and the dangling classification
prove internally that both old branches fill the wall block; the globally
assembled candidate then discharges every rational denominator identity. -/
noncomputable def occurrenceReceiptNd2OfCounts
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    (profile : AuxR0Profile data star pattern)
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (presentation : ∀ pairing,
      ((counts pairing).candidate.datum).LengthMatrixPresentation coordinate)
    (sourceBlock : WallBlock data wall) (wallColumn : coordinate)
    (oldColumns : Finset coordinate) (block : Nd2Block)
    (hPattern : pattern sourceBlock.1 = .nd2 block)
    (newRow : Fin 3 → coordinate) (oldRow : Fin 4 → coordinate)
    (candidate_occurrences : ∀ pairing,
      (if W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second then 0
        else
          {⟨pairing,
            newPathOccurrenceOfCounts counts newRow sourceBlock.1 pairing⟩}) =
        w4TaggedBlockColumnOccurrences
          (candidatesOfCounts data star pattern counts) presentation
          (fun pairing ↦
            WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
          sourceBlock wallColumn pairing)
    (wall_occurrences :
      {oldPathOccurrenceOfCounts counts oldRow sourceBlock.1 block.first,
          oldPathOccurrenceOfCounts counts oldRow sourceBlock.1 block.second} =
        GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (presentation 0)
          (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
          sourceBlock oldColumns)
    (new_row : ∀ pairing,
      W4TargetPairings.Pairing.labelRight pairing block.first ≠
        W4TargetPairings.Pairing.labelRight pairing block.second →
      newRow pairing = oldRow block.first)
    (old_row : oldRow block.first = oldRow block.second) :
    OccurrenceReceipt
      (fun pairing ↦
        w4TaggedBlockColumnOccurrences
          (candidatesOfCounts data star pattern counts) presentation
          (fun pairing ↦
            WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
          sourceBlock wallColumn pairing)
      (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
        (presentation 0)
        (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
        sourceBlock oldColumns)
      (w4CandidateOccurrenceWeight
        (candidatesOfCounts data star pattern counts) presentation wallColumn)
      (w4WallOccurrenceWeight
        (candidatesOfCounts data star pattern counts) presentation wallColumn)
      (.nd2 block) := by
  have hActiveSizes := profile.nd2_active_blockCard sourceBlock.1 block hPattern
    sourceBlock.1 rfl
  apply w4OccurrenceReceiptNd2
    (candidatesOfCounts data star pattern counts) presentation
    (fun pairing ↦
      WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
    sourceBlock wallColumn oldColumns block
    (fun pairing ↦
      newPathOccurrenceOfCounts counts newRow sourceBlock.1 pairing)
    (oldPathOccurrenceOfCounts counts oldRow sourceBlock.1)
    candidate_occurrences wall_occurrences
  · intro pairing hNe
    exact new_row pairing hNe
  · intro pairing hNe
    change
      (counts pairing).candidate.datum.sourceEdgeIndex
          ((counts pairing).candidate.newSourceEdge sourceBlock.1) =
        (counts 0).candidate.datum.sourceEdgeIndex
          ((counts 0).candidate.oldSourceEdge
            (data.sourceEdge (star.edge block.first) sourceBlock.1))
    have hPattern' :
        pattern ((data.vertexPartition wall).repr sourceBlock.1) =
          .nd2 block := by
      simpa [sourceBlock.2] using hPattern
    have hNew :
        (counts pairing).candidate.datum.sourceEdgeIndex
            ((counts pairing).candidate.newSourceEdge sourceBlock.1) =
          data.sourceEdgeIndex
            (data.sourceEdge (star.edge block.first) sourceBlock.1) :=
      PairingReceipts.sourceEdgeIndex_newSourceEdge_nd2_eq_first
        (counts pairing).toPairingReceipts (sourceBlock.1) block hPattern'
          hNe hActiveSizes.1
    exact hNew.trans
      (Candidate.sourceEdgeIndex_oldSourceEdge (counts 0).candidate
        (data.sourceEdge (star.edge block.first) sourceBlock.1)).symm
  · exact old_row
  · change
      (counts 0).candidate.datum.sourceEdgeIndex
          ((counts 0).candidate.oldSourceEdge
            (data.sourceEdge (star.edge block.first) sourceBlock.1)) =
        (counts 0).candidate.datum.sourceEdgeIndex
          ((counts 0).candidate.oldSourceEdge
            (data.sourceEdge (star.edge block.second) sourceBlock.1))
    simp only [Candidate.sourceEdgeIndex_oldSourceEdge,
      GluingDatum.sourceEdgeIndex_sourceEdge]
    exact hActiveSizes.1.trans hActiveSizes.2.symm

/-- Construct the nd3 receipt for an actual W4 wall block.  The source chooses
one sheet on each active old branch because a proper active edge class need
not contain the wall block's canonical representative.  Once those literal
occurrences and their stable-row labels are classified, the regrown-edge
denominator equality is exactly the proved nd3 index formula. -/
noncomputable def occurrenceReceiptNd3OfCounts
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (presentation : ∀ pairing,
      ((counts pairing).candidate.datum).LengthMatrixPresentation coordinate)
    (sourceBlock : WallBlock data wall) (wallColumn : coordinate)
    (oldColumns : Finset coordinate) (block : Nd3Block)
    (hPattern : pattern sourceBlock.1 = .nd3 block)
    (activeSheet : Fin 4 → Fin degree)
    (hActiveSheet : ∀ label, label ∈ block.activeLabels →
      (data.vertexPartition wall).Rel sourceBlock.1 (activeSheet label))
    (newRow : Fin 3 → coordinate) (oldRow : Fin 4 → coordinate)
    (candidate_occurrences : ∀ pairing,
      {⟨pairing,
        newPathOccurrenceOfCounts counts newRow
          (activeSheet (block.singletonLabel pairing)) pairing⟩} =
        w4TaggedBlockColumnOccurrences
          (candidatesOfCounts data star pattern counts) presentation
          (fun pairing ↦
            WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
          sourceBlock wallColumn pairing)
    (wall_occurrences :
      {oldPathOccurrenceOfCounts counts oldRow (activeSheet block.first)
          block.first,
        oldPathOccurrenceOfCounts counts oldRow (activeSheet block.second)
          block.second,
        oldPathOccurrenceOfCounts counts oldRow (activeSheet block.third)
          block.third} =
        GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (presentation 0)
          (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
          sourceBlock oldColumns)
    (new_row : ∀ pairing,
      newRow pairing = oldRow (block.singletonLabel pairing)) :
    OccurrenceReceipt
      (fun pairing ↦
        w4TaggedBlockColumnOccurrences
          (candidatesOfCounts data star pattern counts) presentation
          (fun pairing ↦
            WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
          sourceBlock wallColumn pairing)
      (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
        (presentation 0)
        (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
        sourceBlock oldColumns)
      (w4CandidateOccurrenceWeight
        (candidatesOfCounts data star pattern counts) presentation wallColumn)
      (w4WallOccurrenceWeight
        (candidatesOfCounts data star pattern counts) presentation wallColumn)
      (.nd3 block) := by
  apply w4OccurrenceReceiptNd3
    (candidatesOfCounts data star pattern counts) presentation
    (fun pairing ↦
      WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
    sourceBlock wallColumn oldColumns block
    (fun pairing ↦
      newPathOccurrenceOfCounts counts newRow
        (activeSheet (block.singletonLabel pairing)) pairing)
    (fun label ↦
      oldPathOccurrenceOfCounts counts oldRow (activeSheet label) label)
    candidate_occurrences wall_occurrences
  · intro pairing
    exact new_row pairing
  · intro pairing
    change
      (counts pairing).candidate.datum.sourceEdgeIndex
          ((counts pairing).candidate.newSourceEdge
            (activeSheet (block.singletonLabel pairing))) =
        (counts 0).candidate.datum.sourceEdgeIndex
          ((counts 0).candidate.oldSourceEdge
            (data.sourceEdge
              (star.edge (block.singletonLabel pairing))
              (activeSheet (block.singletonLabel pairing))))
    have hSingletonActive :
        block.singletonLabel pairing ∈ block.activeLabels :=
      block.singletonLabel_mem_activeLabels pairing
    have hSheet := hActiveSheet (block.singletonLabel pairing) hSingletonActive
    have hRepr :
        (data.vertexPartition wall).repr
            (activeSheet (block.singletonLabel pairing)) = sourceBlock.1 := by
      unfold SheetPartition.Rel at hSheet
      rw [sourceBlock.2] at hSheet
      exact hSheet.symm
    have hPattern' :
        pattern ((data.vertexPartition wall).repr
          (activeSheet (block.singletonLabel pairing))) =
          .nd3 block := by
      rw [hRepr]
      exact hPattern
    have hNew :
        (counts pairing).candidate.datum.sourceEdgeIndex
            ((counts pairing).candidate.newSourceEdge
              (activeSheet (block.singletonLabel pairing))) =
          data.sourceEdgeIndex
            (data.sourceEdge
              (star.edge (block.singletonLabel pairing))
              (activeSheet (block.singletonLabel pairing))) :=
      PairingReceipts.sourceEdgeIndex_newSourceEdge_nd3_eq_old
        (counts pairing).toPairingReceipts
          (activeSheet (block.singletonLabel pairing)) block hPattern'
    exact hNew.trans
      (Candidate.sourceEdgeIndex_oldSourceEdge (counts 0).candidate
        (data.sourceEdge
          (star.edge (block.singletonLabel pairing))
          (activeSheet (block.singletonLabel pairing)))).symm

/-- Canonical nd2 receipt from source-level path data.  The hypotheses mention
only the regrown sheet assigned to each stable row and the two contracted old
source edges.  The canonical presentation machinery lifts those occurrences
to the three outgoing data, tags them, and supplies all matrix compatibility
and denominator facts. -/
noncomputable def occurrenceReceiptNd2OfCanonicalPaths
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (profile : AuxR0Profile data star pattern)
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (sourceBlock : WallBlock data wall) (block : Nd2Block)
    (hPattern : pattern sourceBlock.1 = .nd2 block)
    (newRow : Fin 3 → Option target.edges)
    (oldRow : Fin 4 → Option target.edges)
    (new_sheet_occurrences : ∀ pairing,
      (if W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second then 0
        else {(newRow pairing, sourceBlock.1)}) =
          canonicalNewSheetOccurrences sourceBlock (newSheets pairing))
    (old_path_occurrences :
      {(oldRow block.first,
          data.sourceEdge (star.edge block.first) sourceBlock.1),
        (oldRow block.second,
          data.sourceEdge (star.edge block.second) sourceBlock.1)} =
        canonicalOldPathOccurrences star sourceBlock oldPath)
    (new_row : ∀ pairing,
      W4TargetPairings.Pairing.labelRight pairing block.first ≠
        W4TargetPairings.Pairing.labelRight pairing block.second →
      newRow pairing = oldRow block.first)
    (old_row : oldRow block.first = oldRow block.second) :
    OccurrenceReceipt
      (fun pairing ↦
        w4TaggedBlockColumnOccurrences
          (candidatesOfCounts data star pattern counts) (canonicalPresentationOfPaths counts oldPath newSheets)
          (fun pairing ↦
            WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
          sourceBlock none pairing)
      (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
        ((canonicalPresentationOfPaths counts oldPath newSheets) 0)
        (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
        sourceBlock (canonicalW4OldColumns star))
      (w4CandidateOccurrenceWeight
        (candidatesOfCounts data star pattern counts) (canonicalPresentationOfPaths counts oldPath newSheets) none)
      (w4WallOccurrenceWeight
        (candidatesOfCounts data star pattern counts) (canonicalPresentationOfPaths counts oldPath newSheets) none)
      (.nd2 block) := by
  apply occurrenceReceiptNd2OfCounts data star pattern profile counts
    (canonicalPresentationOfPaths counts oldPath newSheets)
    sourceBlock none (canonicalW4OldColumns star) block hPattern newRow oldRow
  · intro pairing
    unfold w4TaggedBlockColumnOccurrences certify candidatesOfCounts
      Candidate.certified
    rw [canonicalPresentationOfPaths_blockColumnOccurrences_none]
    rw [← new_sheet_occurrences pairing]
    by_cases hSame :
        W4TargetPairings.Pairing.labelRight pairing block.first =
          W4TargetPairings.Pairing.labelRight pairing block.second
    · simp [hSame]
      rfl
    · simp [hSame, newPathOccurrenceOfCounts]
      rfl
  · rw [canonicalPresentationOfPaths_blockColumnsOccurrences_old]
    rw [← old_path_occurrences]
    simp [oldPathOccurrenceOfCounts]
  · exact new_row
  · exact old_row

/-- Canonical nd3 receipt from source-level path data.  Its active sheets are
the honest representatives of the three old branch classes; their singleton
selection under each target pairing determines the unique regrown occurrence.
All lifting, tagging, and index comparison is derived. -/
noncomputable def occurrenceReceiptNd3OfCanonicalPaths
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (sourceBlock : WallBlock data wall) (block : Nd3Block)
    (hPattern : pattern sourceBlock.1 = .nd3 block)
    (activeSheet : Fin 4 → Fin degree)
    (hActiveSheet : ∀ label, label ∈ block.activeLabels →
      (data.vertexPartition wall).Rel sourceBlock.1 (activeSheet label))
    (newRow : Fin 3 → Option target.edges)
    (oldRow : Fin 4 → Option target.edges)
    (new_sheet_occurrences : ∀ pairing,
      {(newRow pairing, activeSheet (block.singletonLabel pairing))} =
        canonicalNewSheetOccurrences sourceBlock (newSheets pairing))
    (old_path_occurrences :
      {(oldRow block.first,
          data.sourceEdge (star.edge block.first) (activeSheet block.first)),
        (oldRow block.second,
          data.sourceEdge (star.edge block.second) (activeSheet block.second)),
        (oldRow block.third,
          data.sourceEdge (star.edge block.third) (activeSheet block.third))} =
        canonicalOldPathOccurrences star sourceBlock oldPath)
    (new_row : ∀ pairing,
      newRow pairing = oldRow (block.singletonLabel pairing)) :
    OccurrenceReceipt
      (fun pairing ↦
        w4TaggedBlockColumnOccurrences
          (candidatesOfCounts data star pattern counts) (canonicalPresentationOfPaths counts oldPath newSheets)
          (fun pairing ↦
            WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
          sourceBlock none pairing)
      (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
        ((canonicalPresentationOfPaths counts oldPath newSheets) 0)
        (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
        sourceBlock (canonicalW4OldColumns star))
      (w4CandidateOccurrenceWeight
        (candidatesOfCounts data star pattern counts) (canonicalPresentationOfPaths counts oldPath newSheets) none)
      (w4WallOccurrenceWeight
        (candidatesOfCounts data star pattern counts) (canonicalPresentationOfPaths counts oldPath newSheets) none)
      (.nd3 block) := by
  apply occurrenceReceiptNd3OfCounts data star pattern counts
    (canonicalPresentationOfPaths counts oldPath newSheets)
    sourceBlock none (canonicalW4OldColumns star) block hPattern
    activeSheet hActiveSheet newRow oldRow
  · intro pairing
    unfold w4TaggedBlockColumnOccurrences certify candidatesOfCounts
      Candidate.certified
    rw [canonicalPresentationOfPaths_blockColumnOccurrences_none]
    rw [← new_sheet_occurrences pairing]
    simp [newPathOccurrenceOfCounts]
    rfl
  · rw [canonicalPresentationOfPaths_blockColumnsOccurrences_old]
    rw [← old_path_occurrences]
    simp [oldPathOccurrenceOfCounts]
  · exact new_row

/-- A wall block with no retained old occurrence and no regrown stable
occurrence contributes zero to every candidate and to the incoming wall,
regardless of the harmless resolution pattern chosen for its singleton
sheets. -/
noncomputable def occurrenceReceiptZeroOfCanonicalPaths
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (sourceBlock : WallBlock data wall) (blockPattern : BlockPattern)
    (hPattern : pattern sourceBlock.1 = blockPattern)
    (new_sheet_occurrences : ∀ pairing,
      0 = canonicalNewSheetOccurrences sourceBlock (newSheets pairing))
    (old_path_occurrences :
      0 = canonicalOldPathOccurrences star sourceBlock oldPath) :
    OccurrenceReceipt
      (fun pairing ↦
        w4TaggedBlockColumnOccurrences
          (candidatesOfCounts data star pattern counts)
          (canonicalPresentationOfPaths counts oldPath newSheets)
          (fun candidate ↦ WallBlock.ofSourceEdge data wall
            (counts candidate).candidate.datum)
          sourceBlock none pairing)
      (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
        (canonicalPresentationOfPaths counts oldPath newSheets 0)
        (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
        sourceBlock (canonicalW4OldColumns star))
      (w4CandidateOccurrenceWeight
        (candidatesOfCounts data star pattern counts)
        (canonicalPresentationOfPaths counts oldPath newSheets) none)
      (w4WallOccurrenceWeight
        (candidatesOfCounts data star pattern counts)
        (canonicalPresentationOfPaths counts oldPath newSheets) none)
      (pattern sourceBlock.1) := by
  rw [hPattern]
  apply OccurrenceReceipt.zero blockPattern
  · intro pairing
    unfold w4TaggedBlockColumnOccurrences certify candidatesOfCounts
      Candidate.certified
    rw [canonicalPresentationOfPaths_blockColumnOccurrences_none]
    rw [← new_sheet_occurrences pairing]
    exact (Multiset.map_zero _).symm
  · rw [canonicalPresentationOfPaths_blockColumnsOccurrences_old]
    rw [← old_path_occurrences]
    rfl

/-- The complete source-level classification of one W4 wall block, before any
outgoing candidate types or rational matrix weights appear.  The two
constructors are the paper's `aux-r0-nd2` and `aux-r0-nd3` path pictures. -/
inductive CanonicalBlockClassification
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (sourceBlock : WallBlock data wall) : Type where
  | zero (blockPattern : BlockPattern)
      (is_pattern : pattern sourceBlock.1 = blockPattern)
      (new_sheet_occurrences : ∀ pairing,
        0 = canonicalNewSheetOccurrences sourceBlock (newSheets pairing))
      (old_path_occurrences :
        0 = canonicalOldPathOccurrences star sourceBlock oldPath) :
      CanonicalBlockClassification data star pattern oldPath newSheets
        sourceBlock
  | nd2 (block : Nd2Block)
      (is_pattern : pattern sourceBlock.1 = .nd2 block)
      (newRow : Fin 3 → Option target.edges)
      (oldRow : Fin 4 → Option target.edges)
      (new_sheet_occurrences : ∀ pairing,
        (if W4TargetPairings.Pairing.labelRight pairing block.first =
            W4TargetPairings.Pairing.labelRight pairing block.second then 0
          else {(newRow pairing, sourceBlock.1)}) =
            canonicalNewSheetOccurrences sourceBlock (newSheets pairing))
      (old_path_occurrences :
        {(oldRow block.first,
            data.sourceEdge (star.edge block.first) sourceBlock.1),
          (oldRow block.second,
            data.sourceEdge (star.edge block.second) sourceBlock.1)} =
          canonicalOldPathOccurrences star sourceBlock oldPath)
      (new_row : ∀ pairing,
        W4TargetPairings.Pairing.labelRight pairing block.first ≠
          W4TargetPairings.Pairing.labelRight pairing block.second →
        newRow pairing = oldRow block.first)
      (old_row : oldRow block.first = oldRow block.second) :
      CanonicalBlockClassification data star pattern oldPath newSheets
        sourceBlock
  | nd3 (block : Nd3Block)
      (is_pattern : pattern sourceBlock.1 = .nd3 block)
      (activeSheet : Fin 4 → Fin degree)
      (active_sheet : ∀ label, label ∈ block.activeLabels →
        (data.vertexPartition wall).Rel sourceBlock.1 (activeSheet label))
      (newRow : Fin 3 → Option target.edges)
      (oldRow : Fin 4 → Option target.edges)
      (new_sheet_occurrences : ∀ pairing,
        {(newRow pairing, activeSheet (block.singletonLabel pairing))} =
          canonicalNewSheetOccurrences sourceBlock (newSheets pairing))
      (old_path_occurrences :
        {(oldRow block.first,
            data.sourceEdge (star.edge block.first) (activeSheet block.first)),
          (oldRow block.second,
            data.sourceEdge (star.edge block.second) (activeSheet block.second)),
          (oldRow block.third,
            data.sourceEdge (star.edge block.third) (activeSheet block.third))} =
          canonicalOldPathOccurrences star sourceBlock oldPath)
      (new_row : ∀ pairing,
        newRow pairing = oldRow (block.singletonLabel pairing)) :
      CanonicalBlockClassification data star pattern oldPath newSheets
        sourceBlock

namespace CanonicalBlockClassification

/-- Lower one source-level auxiliary classification to the exact occurrence
receipt used in Equation (1). -/
noncomputable def occurrenceReceipt
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (profile : AuxR0Profile data star pattern)
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (sourceBlock : WallBlock data wall)
    (classified : CanonicalBlockClassification data star pattern oldPath
      newSheets sourceBlock) :
    OccurrenceReceipt
      (fun pairing ↦
        w4TaggedBlockColumnOccurrences
          (candidatesOfCounts data star pattern counts)
          (canonicalPresentationOfPaths counts oldPath newSheets)
          (fun candidate ↦ WallBlock.ofSourceEdge data wall
            (counts candidate).candidate.datum)
          sourceBlock none pairing)
      (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
        (canonicalPresentationOfPaths counts oldPath newSheets 0)
        (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
        sourceBlock (canonicalW4OldColumns star))
      (w4CandidateOccurrenceWeight
        (candidatesOfCounts data star pattern counts)
        (canonicalPresentationOfPaths counts oldPath newSheets) none)
      (w4WallOccurrenceWeight
        (candidatesOfCounts data star pattern counts)
        (canonicalPresentationOfPaths counts oldPath newSheets) none)
      (pattern sourceBlock.1) := by
  cases classified with
  | zero blockPattern hPattern newOccurrences oldOccurrences =>
      exact occurrenceReceiptZeroOfCanonicalPaths data star pattern counts
        oldPath newSheets sourceBlock blockPattern hPattern newOccurrences
        oldOccurrences
  | nd2 block hPattern newRow oldRow newOccurrences oldOccurrences newRowEq
      oldRowEq =>
      rw [hPattern]
      exact occurrenceReceiptNd2OfCanonicalPaths data star pattern profile counts
        oldPath newSheets sourceBlock block hPattern newRow oldRow newOccurrences
        oldOccurrences newRowEq oldRowEq
  | nd3 block hPattern activeSheet activeSheetMem newRow oldRow newOccurrences
      oldOccurrences newRowEq =>
      rw [hPattern]
      exact occurrenceReceiptNd3OfCanonicalPaths data star pattern counts
        oldPath newSheets sourceBlock block hPattern activeSheet activeSheetMem
        newRow oldRow newOccurrences oldOccurrences newRowEq

end CanonicalBlockClassification

/-- Complete W4 balanced family from the two remaining concrete source
classifications: trivalent exterior/count receipts for candidate validity and
multiplicity-preserving stable-path term receipts for Equation (1).  Source
blocks are indexed by canonical wall-partition representatives, never by
duplicate sheet names. -/
noncomputable def balancedFamilyOfCountsAndTermReceipts
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (presentation : ∀ pairing,
      ((counts pairing).candidate.datum).LengthMatrixPresentation coordinate)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation i))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation j))
        wallColumn)
    (receipt : ∀ sourceBlock : WallBlock data wall,
      TermReceipt
        (fun pairing ↦
          GluingDatum.LengthMatrixPresentation.blockColumnTerms
            (presentation pairing)
            (WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
            sourceBlock wallColumn
            (fun sourceRow ↦
              (GluingDatum.LengthMatrixPresentation.matrix
                (presentation 0)).adjugate wallColumn sourceRow))
        (GluingDatum.LengthMatrixPresentation.blockColumnsTerms
          (presentation 0)
          (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
          sourceBlock oldColumns
          (fun sourceRow ↦
            (GluingDatum.LengthMatrixPresentation.matrix
              (presentation 0)).adjugate wallColumn sourceRow))
        (pattern sourceBlock.1)) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamilyOfLengthMatrixTermReceipts
    (candidatesOfCounts data star pattern counts) presentation
    (fun pairing ↦
      WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
    wallColumn oldColumns hOld hAgree (fun sourceBlock ↦ pattern sourceBlock.1)
    receipt

/-- Complete W4 balanced family from trivalent count receipts and a
classification of the literal `(stable row, source edge)` occurrence
multisets.  Candidate occurrences are tagged by their pairing; all rational
term profiles are derived from the generic weighting bridge. -/
noncomputable def balancedFamilyOfCountsAndOccurrenceReceipts
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (presentation : ∀ pairing,
      ((counts pairing).candidate.datum).LengthMatrixPresentation coordinate)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation i))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation j))
        wallColumn)
    (receipt : ∀ sourceBlock : WallBlock data wall,
      OccurrenceReceipt
        (fun pairing ↦
          w4TaggedBlockColumnOccurrences
            (candidatesOfCounts data star pattern counts) presentation
            (fun pairing ↦
              WallBlock.ofSourceEdge data wall
                (counts pairing).candidate.datum)
            sourceBlock wallColumn pairing)
        (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (presentation 0)
          (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
          sourceBlock oldColumns)
        (w4CandidateOccurrenceWeight
          (candidatesOfCounts data star pattern counts) presentation wallColumn)
        (w4WallOccurrenceWeight
          (candidatesOfCounts data star pattern counts) presentation wallColumn)
        (pattern sourceBlock.1)) :
    Family (coordinate := coordinate) 3 data :=
  w4BalancedFamilyOfLengthMatrixOccurrenceReceipts
    (candidatesOfCounts data star pattern counts) presentation
    (fun pairing ↦
      WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
    wallColumn oldColumns hOld hAgree (fun sourceBlock ↦ pattern sourceBlock.1)
    receipt

/-- The same complete W4 assembly while retaining its actual presentations.
This is the load-bearing semantic endpoint: its positive-exit theorem returns
a cleared subdivision pencil on the selected outgoing candidate. -/
noncomputable def presentedFamilyOfCountsAndOccurrenceReceipts
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
    (presentation : ∀ pairing,
      ((counts pairing).candidate.datum).LengthMatrixPresentation coordinate)
    (wallColumn : coordinate) (oldColumns : Finset coordinate)
    (hOld : ∀ column ∈ oldColumns, column ≠ wallColumn)
    (hAgree : ∀ i j,
      AgreeOffColumn
        (GluingDatum.LengthMatrixPresentation.matrix (presentation i))
        (GluingDatum.LengthMatrixPresentation.matrix (presentation j))
        wallColumn)
    (receipt : ∀ sourceBlock : WallBlock data wall,
      OccurrenceReceipt
        (fun pairing ↦
          w4TaggedBlockColumnOccurrences
            (candidatesOfCounts data star pattern counts) presentation
            (fun pairing ↦
              WallBlock.ofSourceEdge data wall
                (counts pairing).candidate.datum)
            sourceBlock wallColumn pairing)
        (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (presentation 0)
          (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
          sourceBlock oldColumns)
        (w4CandidateOccurrenceWeight
          (candidatesOfCounts data star pattern counts) presentation wallColumn)
        (w4WallOccurrenceWeight
          (candidatesOfCounts data star pattern counts) presentation wallColumn)
        (pattern sourceBlock.1)) :
    PresentedFamily (coordinate := coordinate) 3 data wall :=
  w4PresentedFamilyOfLengthMatrixOccurrenceReceipts
    (candidatesOfCounts data star pattern counts) presentation
    (fun pairing ↦
      WallBlock.ofSourceEdge data wall (counts pairing).candidate.datum)
    wallColumn oldColumns hOld hAgree (fun sourceBlock ↦ pattern sourceBlock.1)
    receipt

/-- Canonical source-facing W4 endpoint.  One common old path family and the
pairing-specific regrown sheets construct the actual presentations, fix
`none` as the wall column, enumerate every retained old column, and prove
off-wall agreement.  The sole remaining determinant input is therefore the
literal occurrence classification for those canonical paths. -/
noncomputable def presentedFamilyOfCanonicalPathsAndOccurrenceReceipts
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (counts : ∀ pairing, PairingCounts data star pattern pairing)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (receipt : ∀ sourceBlock : WallBlock data wall,
      OccurrenceReceipt
        (fun pairing ↦
          w4TaggedBlockColumnOccurrences
            (candidatesOfCounts data star pattern counts)
            (canonicalPresentationOfPaths counts oldPath newSheets)
            (fun pairing ↦
              WallBlock.ofSourceEdge data wall
                (counts pairing).candidate.datum)
            sourceBlock none pairing)
        (GluingDatum.LengthMatrixPresentation.blockColumnsOccurrences
          (canonicalPresentationOfPaths counts oldPath newSheets 0)
          (WallBlock.ofSourceEdge data wall (counts 0).candidate.datum)
          sourceBlock (canonicalW4OldColumns star))
        (w4CandidateOccurrenceWeight
          (candidatesOfCounts data star pattern counts)
          (canonicalPresentationOfPaths counts oldPath newSheets) none)
        (w4WallOccurrenceWeight
          (candidatesOfCounts data star pattern counts)
          (canonicalPresentationOfPaths counts oldPath newSheets) none)
        (pattern sourceBlock.1)) :
    PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  presentedFamilyOfCountsAndOccurrenceReceipts data star pattern counts
    (canonicalPresentationOfPaths counts oldPath newSheets) none
    (canonicalW4OldColumns star) (canonicalW4OldColumns_ne_none star)
    (canonicalPresentations_agreeOffWall counts oldPath newSheets) receipt

/-- End-to-end W4 local continuation from the paper's source-level auxiliary
classification.  Exact zero ramification supplies all candidate validity
counts; the common old paths, regrown sheet assignments, and one nd2/nd3
classification per wall block supply Equation (1).  The result retains the
three actual outgoing candidates and canonical length presentations for the
semantic cone exit. -/
noncomputable def presentedFamilyOfAuxR0CanonicalClassification
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (profile : AuxR0Profile data star pattern)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (classified : ∀ sourceBlock : WallBlock data wall,
      CanonicalBlockClassification data star pattern oldPath newSheets
        sourceBlock) :
    PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  presentedFamilyOfCanonicalPathsAndOccurrenceReceipts data star pattern
    (fun pairing ↦ profile.pairingCounts pairing) oldPath newSheets
    (fun sourceBlock ↦
      CanonicalBlockClassification.occurrenceReceipt data star pattern profile
        (fun pairing ↦ profile.pairingCounts pairing) oldPath newSheets
        sourceBlock (classified sourceBlock))

/-- Source-facing W4 endpoint with the paper's global change equation as its
ramification input.  Validity proves every local ramification is nonnegative,
so the one equation `∑ r₀(A₀) = 0` constructs `AuxR0Profile`; the remaining
arguments are exactly the dangling and stable-path classifications from
Cases `{aux-r0-nd2}` and `{aux-r0-nd3}`. -/
noncomputable def presentedFamilyOfValidChangeZeroCanonicalClassification
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (hValid : data.Valid)
    (exterior : ExteriorProfile data star pattern)
    (hChangeZero :
      ∑ sourceBlock : WallBlock data wall,
        AuxR0Profile.wallBlockRamification data star sourceBlock = 0)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (classified : ∀ sourceBlock : WallBlock data wall,
      CanonicalBlockClassification data star pattern oldPath newSheets
        sourceBlock) :
    PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  presentedFamilyOfAuxR0CanonicalClassification data star pattern
    (AuxR0Profile.ofValidChangeZero exterior hValid hChangeZero)
    oldPath newSheets classified

/-- The literal source version of the W4 endpoint.  Its dangling hypotheses
are only the cardinality-one assertions of dangling-no-glue; Lean converts
them to exterior refinements, derives local `r₀ = 0` from the global change
sum, and then performs the complete candidate and determinant assembly. -/
noncomputable def presentedFamilyOfDanglingChangeZeroClassification
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern)
    [DecidableEq target.edges]
    (hValid : data.Valid)
    (dangling : DanglingSingletonProfile data star pattern)
    (hChangeZero :
      ∑ sourceBlock : WallBlock data wall,
        AuxR0Profile.wallBlockRamification data star sourceBlock = 0)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (classified : ∀ sourceBlock : WallBlock data wall,
      CanonicalBlockClassification data star pattern oldPath newSheets
        sourceBlock) :
    PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  presentedFamilyOfValidChangeZeroCanonicalClassification data star pattern
    hValid dangling.exterior hChangeZero oldPath newSheets classified

end DraismaVargas.LocalCases.GlobalW4
