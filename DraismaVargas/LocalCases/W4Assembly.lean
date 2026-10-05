module

public import DraismaVargas.LocalCases.ResolutionAssembly
public import DraismaVargas.LocalCases.ResolutionW4

@[expose] public section

/-!
# Whole-wall assembly for the W4 resolutions

The W4 source case resolves every block above the four-valent target wall in
each of the three `2+2` target expansions.  A block has non-dangling valency
two or three.  This module records those two source shapes, chooses the local
resolution prescribed by `aux-r0-nd2` or `aux-r0-nd3`, and pastes all block
choices into one genuine resolution of the complete sheet partition.

For an nd3 block the singleton branch is determined, rather than supplied:
three distinct star labels always split `1+2` under a `2+2` pairing.  Its old
edge partition is the fine partition on the singleton endpoint and new edge.
The rest of the W4 construction (`GlobalW4`) attaches the four old occurrence
lists, proves the two
endpoint Riemann--Hurwitz inequalities, and packages the results as three
`BalancedGlobal.Candidate`s.  The final theorems also compute the new-edge
block cardinality after whole-wall pasting: unit for a same-side nd2 block,
the old wall-block cardinality for an opposite-side nd2 block, and the
singleton old-branch cardinality for an nd3 block.
-/

namespace DraismaVargas.LocalCases.W4Assembly

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.ResolutionM11
open DraismaVargas.LocalCases.ResolutionW4

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- The two distinct external star branches of an r0-nd2 wall block. -/
structure Nd2Block where
  first : Fin 4
  second : Fin 4
  distinct : first ≠ second

/-- The three distinct external star branches of an r0-nd3 wall block. -/
structure Nd3Block where
  first : Fin 4
  second : Fin 4
  third : Fin 4
  first_ne_second : first ≠ second
  first_ne_third : first ≠ third
  second_ne_third : second ≠ third

namespace Nd2Block

/-- The two non-dangling branch labels of an nd2 source block. -/
def activeLabels (block : Nd2Block) : Finset (Fin 4) :=
  {block.first, block.second}

@[simp] theorem mem_activeLabels (block : Nd2Block) (label : Fin 4) :
    label ∈ block.activeLabels ↔
      label = block.first ∨ label = block.second := by
  simp [activeLabels]

/-- When the two active branches lie on opposite sides, each side contains
exactly one of them. -/
theorem card_activeLabels_onSide_of_ne (block : Nd2Block) (pairing : Fin 3)
    (sideValue : Bool)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    ((W4TargetPairings.Pairing.labelsOnSide pairing sideValue).filter
      fun label ↦ label ∈ block.activeLabels).card = 1 := by
  rcases block with ⟨first, second, distinct⟩
  revert first second
  fin_cases pairing <;> cases sideValue <;> decide +kernel

/-- If the two active nd2 branches lie on the same side of a `2+2` pairing,
either remaining star label lies on the opposite side. -/
theorem labelRight_ne_of_same_of_other (block : Nd2Block) (pairing : Fin 3)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second)
    (other : Fin 4) (hFirst : other ≠ block.first)
    (hSecond : other ≠ block.second) :
    W4TargetPairings.Pairing.labelRight pairing other ≠
      W4TargetPairings.Pairing.labelRight pairing block.first := by
  rcases block with ⟨first, second, distinct⟩
  revert first second other
  fin_cases pairing <;> decide +kernel

end Nd2Block

namespace Nd3Block

/-- The three non-dangling branch labels of an nd3 source block. -/
def activeLabels (block : Nd3Block) : Finset (Fin 4) :=
  {block.first, block.second, block.third}

@[simp] theorem mem_activeLabels (block : Nd3Block) (label : Fin 4) :
    label ∈ block.activeLabels ↔
      label = block.first ∨ label = block.second ∨ label = block.third := by
  simp [activeLabels]

/-- A label is the singleton among the block's three external branches for a
fixed `2+2` target pairing. -/
def IsSingleton (block : Nd3Block) (pairing : Fin 3) (label : Fin 4) : Prop :=
  (label = block.first ∧
      W4TargetPairings.Pairing.labelRight pairing block.first ≠
        W4TargetPairings.Pairing.labelRight pairing block.second ∧
      W4TargetPairings.Pairing.labelRight pairing block.second =
        W4TargetPairings.Pairing.labelRight pairing block.third) ∨
    (label = block.second ∧
      W4TargetPairings.Pairing.labelRight pairing block.second ≠
        W4TargetPairings.Pairing.labelRight pairing block.first ∧
      W4TargetPairings.Pairing.labelRight pairing block.first =
        W4TargetPairings.Pairing.labelRight pairing block.third) ∨
    (label = block.third ∧
      W4TargetPairings.Pairing.labelRight pairing block.third ≠
        W4TargetPairings.Pairing.labelRight pairing block.first ∧
      W4TargetPairings.Pairing.labelRight pairing block.first =
        W4TargetPairings.Pairing.labelRight pairing block.second)

/-- The branch isolated by a target pairing. -/
def singletonLabel (block : Nd3Block) (pairing : Fin 3) : Fin 4 :=
  if W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second ∧
    W4TargetPairings.Pairing.labelRight pairing block.second =
      W4TargetPairings.Pairing.labelRight pairing block.third then
    block.first
  else if W4TargetPairings.Pairing.labelRight pairing block.second ≠
      W4TargetPairings.Pairing.labelRight pairing block.first ∧
    W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.third then
    block.second
  else
    block.third

/-- The selected label really is the unique side among the three branches. -/
theorem singletonLabel_isSingleton (block : Nd3Block) (pairing : Fin 3) :
    block.IsSingleton pairing (block.singletonLabel pairing) := by
  unfold singletonLabel IsSingleton
  split_ifs with hFirst hSecond
  · exact Or.inl ⟨rfl, hFirst⟩
  · exact Or.inr (Or.inl ⟨rfl, hSecond⟩)
  · have hCases :=
      W4TargetPairings.Pairing.three_distinct_one_against_two pairing
        block.first block.second block.third block.first_ne_second
        block.first_ne_third block.second_ne_third
    rcases hCases with hFirst' | hSecond' | hThird
    · exact (hFirst hFirst').elim
    · exact (hSecond hSecond').elim
    · exact Or.inr (Or.inr ⟨rfl, hThird⟩)

/-- The selected singleton label is one of the block's three active labels. -/
theorem singletonLabel_mem_activeLabels (block : Nd3Block) (pairing : Fin 3) :
    block.singletonLabel pairing ∈ block.activeLabels := by
  rcases block.singletonLabel_isSingleton pairing with
    hFirst | hSecond | hThird
  · simp [hFirst.1]
  · simp [hSecond.1]
  · simp [hThird.1]

/-- The same singleton statement for the actual target-edge occurrences. -/
theorem singletonLabel_isSingleton_actual
    (block : Nd3Block) (star : W4TargetPairings.FourStar target wall)
    (pairing : Fin 3) :
    (block.singletonLabel pairing = block.first ∧
        star.right pairing (star.edge block.first) ≠
          star.right pairing (star.edge block.second) ∧
        star.right pairing (star.edge block.second) =
          star.right pairing (star.edge block.third)) ∨
      (block.singletonLabel pairing = block.second ∧
        star.right pairing (star.edge block.second) ≠
          star.right pairing (star.edge block.first) ∧
        star.right pairing (star.edge block.first) =
          star.right pairing (star.edge block.third)) ∨
      (block.singletonLabel pairing = block.third ∧
        star.right pairing (star.edge block.third) ≠
          star.right pairing (star.edge block.first) ∧
        star.right pairing (star.edge block.first) =
          star.right pairing (star.edge block.second)) := by
  simpa only [IsSingleton, W4TargetPairings.FourStar.right_edge] using
    block.singletonLabel_isSingleton pairing

/-- Among the three active nd3 branches, the only label on the singleton
side is `singletonLabel`. -/
theorem eq_singletonLabel_of_active_of_same_side
    (block : Nd3Block) (pairing : Fin 3) (label : Fin 4)
    (hActive : label = block.first ∨ label = block.second ∨
      label = block.third)
    (hSide : W4TargetPairings.Pairing.labelRight pairing label =
      W4TargetPairings.Pairing.labelRight pairing
        (block.singletonLabel pairing)) :
    label = block.singletonLabel pairing := by
  rcases block with
    ⟨first, second, third, first_ne_second, first_ne_third,
      second_ne_third⟩
  revert first second third label
  fin_cases pairing <;> decide +kernel

/-- The singleton side contains exactly one of the three active labels. -/
theorem card_activeLabels_on_singletonSide (block : Nd3Block)
    (pairing : Fin 3) :
    ((W4TargetPairings.Pairing.labelsOnSide pairing
      (W4TargetPairings.Pairing.labelRight pairing
        (block.singletonLabel pairing))).filter
      fun label ↦ label ∈ block.activeLabels).card = 1 := by
  have hFilter :
      (W4TargetPairings.Pairing.labelsOnSide pairing
        (W4TargetPairings.Pairing.labelRight pairing
          (block.singletonLabel pairing))).filter
          (fun label ↦ label ∈ block.activeLabels) =
        {block.singletonLabel pairing} := by
    ext label
    constructor
    · intro hLabel
      have hMem := Finset.mem_filter.mp hLabel
      have hEq := block.eq_singletonLabel_of_active_of_same_side pairing label
        ((block.mem_activeLabels label).mp hMem.2)
        ((W4TargetPairings.Pairing.mem_labelsOnSide _ _ _).mp hMem.1)
      simp [hEq]
    · intro hLabel
      have hEq : label = block.singletonLabel pairing := by simpa using hLabel
      subst label
      exact Finset.mem_filter.mpr ⟨by simp,
        block.singletonLabel_mem_activeLabels pairing⟩
  rw [hFilter]
  simp

end Nd3Block

/-- The source classification of one wall block. -/
inductive BlockPattern where
  | nd2 (block : Nd2Block)
  | nd3 (block : Nd3Block)

/-- Canonical representatives of the actual source blocks above the W4 wall
vertex.  Determinant contributions must be indexed by these blocks rather
than by every sheet, since nonrepresentative sheets name no separate block. -/
abbrev WallBlock (data : GluingDatum target degree) (wall : target.V) :=
  (data.vertexPartition wall).Blocks

namespace WallBlock

/-- The old wall block containing a chosen sheet. -/
def ofSheet (data : GluingDatum target degree) (wall : target.V)
    (sheet : Fin degree) : WallBlock data wall :=
  (data.vertexPartition wall).toBlock sheet

@[simp] theorem ofSheet_val (data : GluingDatum target degree)
    (wall : target.V) (sheet : Fin degree) :
    (ofSheet data wall sheet).1 = (data.vertexPartition wall).repr sheet := rfl

/-- A canonical representative maps to itself as a wall block. -/
@[simp] theorem ofSheet_anchor (data : GluingDatum target degree)
    (wall : target.V) (block : WallBlock data wall) :
    ofSheet data wall block.1 = block := by
  apply Subtype.ext
  exact block.2

/-- Classify any source-edge occurrence, in any datum of the same degree, by
the old W4 wall block containing its sheet representative. -/
def ofSourceEdge (data : GluingDatum target degree) (wall : target.V)
    {otherTarget : CFGraph} (otherData : GluingDatum otherTarget degree)
    (edge : otherData.SourceEdge) : WallBlock data wall :=
  ofSheet data wall edge.1.2

end WallBlock

/-- Resolve one classified wall block for one of the three target pairings. -/
noncomputable def resolutionAt (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (pairing : Fin 3)
    (anchor : Fin degree) : BlockPattern → LocalResolution degree
  | .nd2 block =>
      nd2ResolutionForPairing star pairing (data.vertexPartition wall) anchor
        block.first block.second
  | .nd3 block =>
      nd3ResolutionForPairing star pairing (data.vertexPartition wall)
        (data.edgePartition (star.edge (block.singletonLabel pairing)))
        (star.edgePartition_refines_wall data (block.singletonLabel pairing))
        (block.singletonLabel pairing)

/-- Every classified block resolution contracts to the same wall partition. -/
theorem resolutionAt_contracts (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (pairing : Fin 3)
    (anchor : Fin degree) (pattern : BlockPattern) :
    (resolutionAt data star pairing anchor pattern).ContractsTo
      (data.vertexPartition wall) := by
  cases pattern with
  | nd2 block =>
      exact nd2ResolutionForPairing_contracts star pairing
        (data.vertexPartition wall) anchor block.first block.second
  | nd3 block =>
      exact nd3ResolutionForPairing_contracts star pairing
        (data.vertexPartition wall)
        (data.edgePartition (star.edge (block.singletonLabel pairing)))
        (star.edgePartition_refines_wall data (block.singletonLabel pairing))
        (block.singletonLabel pairing)

/-- On an nd3 block, the new edge is exactly the selected singleton branch's
old edge partition. -/
theorem resolutionAt_nd3_newEdge (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) (pairing : Fin 3)
    (anchor : Fin degree) (block : Nd3Block) :
    (resolutionAt data star pairing anchor (.nd3 block)).newEdge =
      data.edgePartition (star.edge (block.singletonLabel pairing)) := by
  exact nd3Resolution_newEdge (data.vertexPartition wall)
    (data.edgePartition (star.edge (block.singletonLabel pairing)))
    (star.edgePartition_refines_wall data (block.singletonLabel pairing)) _

/-- The blockwise resolution function for one target pairing. -/
noncomputable def blockwiseResolution (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) : LocalResolution degree :=
  resolutionAt data star pairing anchor (pattern anchor)

theorem blockwiseResolution_contracts (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) :
    ∀ anchor, (blockwiseResolution data star pattern pairing anchor).ContractsTo
      (data.vertexPartition wall) :=
  fun anchor ↦ resolutionAt_contracts data star pairing anchor (pattern anchor)

/-- The endpoint partition on one Boolean side of a blockwise resolution. -/
noncomputable def endpointAtSide (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (anchor : Fin degree) (sideValue : Bool) : SheetPartition degree :=
  if sideValue then
    (blockwiseResolution data star pattern pairing anchor).right
  else
    (blockwiseResolution data star pattern pairing anchor).left

/-- The two old target-edge occurrences assigned to one Boolean side. -/
noncomputable def oldEdgesAtSide
    (star : W4TargetPairings.FourStar target wall) (pairing : Fin 3)
    (sideValue : Bool) : List target.edges :=
  if sideValue then star.rightEdges pairing else star.leftEdges pairing

/-- Summing the canonical old occurrence list agrees with the corresponding
label-side sum. -/
theorem sum_oldEdgesAtSide_eq_sideSum
    (star : W4TargetPairings.FourStar target wall) (pairing : Fin 3)
    (sideValue : Bool) (value : target.edges → ℤ) :
    ((oldEdgesAtSide star pairing sideValue).map value).sum =
      W4TargetPairings.Pairing.sideSum pairing sideValue
        (fun label ↦ value (star.edge label)) := by
  cases sideValue
  · exact star.sum_leftEdges_eq_sideSum pairing value
  · exact star.sum_rightEdges_eq_sideSum pairing value

/-- Paste every classified block into a whole-sheet resolution for one target
pairing. -/
noncomputable def wholeResolution (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) :
    LocalResolution degree :=
  LocalResolution.paste (data.vertexPartition wall)
    (blockwiseResolution data star pattern pairing)
    (blockwiseResolution_contracts data star pattern pairing)

/-- The assembled resolution contracts back to the original wall partition. -/
theorem wholeResolution_contracts (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3) :
    (wholeResolution data star pattern pairing).ContractsTo
      (data.vertexPartition wall) :=
  LocalResolution.paste_contracts (data.vertexPartition wall)
    (blockwiseResolution data star pattern pairing)
    (blockwiseResolution_contracts data star pattern pairing)

/-- The three source-prescribed whole-wall resolutions. -/
noncomputable def wholeResolutions (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) : Fin 3 → LocalResolution degree :=
  fun pairing ↦ wholeResolution data star pattern pairing

theorem wholeResolutions_contract (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) :
    ∀ pairing,
      (wholeResolutions data star pattern pairing).ContractsTo
      (data.vertexPartition wall) :=
  wholeResolution_contracts data star pattern

/-! ### New-edge indices in the assembled resolutions -/

/-- In an nd2 wall block whose two external branches lie on the same side,
the assembled new-edge occurrence through that block is a singleton.  These
are the dangling new edges which do not enter the stable length paths. -/
theorem wholeResolution_nd2_newEdge_blockCard_of_same
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (sheet : Fin degree) (block : Nd2Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd2 block)
    (hSame : W4TargetPairings.Pairing.labelRight pairing block.first =
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    (wholeResolution data star pattern pairing).newEdge.blockCard sheet = 1 := by
  unfold wholeResolution
  rw [LocalResolution.paste_newEdge_blockCard]
  change
    (resolutionAt data star pairing ((data.vertexPartition wall).repr sheet)
      (pattern ((data.vertexPartition wall).repr sheet))).newEdge.blockCard
        sheet = 1
  rw [hPattern]
  apply nd2Resolution_newEdge_blockCard_of_same
  · simpa only [W4TargetPairings.FourStar.right_edge] using hSame
  · exact (data.vertexPartition wall).rel_repr_left sheet

/-- In an nd2 wall block whose branches lie on opposite sides, the assembled
new edge retains the whole old wall block and therefore its dilation index. -/
theorem wholeResolution_nd2_newEdge_blockCard_of_ne
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (sheet : Fin degree) (block : Nd2Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd2 block)
    (hNe : W4TargetPairings.Pairing.labelRight pairing block.first ≠
      W4TargetPairings.Pairing.labelRight pairing block.second) :
    (wholeResolution data star pattern pairing).newEdge.blockCard sheet =
      (data.vertexPartition wall).blockCard sheet := by
  unfold wholeResolution
  rw [LocalResolution.paste_newEdge_blockCard]
  change
    (resolutionAt data star pairing ((data.vertexPartition wall).repr sheet)
      (pattern ((data.vertexPartition wall).repr sheet))).newEdge.blockCard
        sheet = (data.vertexPartition wall).blockCard sheet
  rw [hPattern]
  apply nd2Resolution_newEdge_blockCard_of_ne
  simpa only [W4TargetPairings.FourStar.right_edge] using hNe

/-- In an nd3 wall block, the assembled new edge has exactly the dilation
index of the old branch isolated by the target pairing. -/
theorem wholeResolution_nd3_newEdge_blockCard
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    (pattern : Fin degree → BlockPattern) (pairing : Fin 3)
    (sheet : Fin degree) (block : Nd3Block)
    (hPattern : pattern ((data.vertexPartition wall).repr sheet) = .nd3 block) :
    (wholeResolution data star pattern pairing).newEdge.blockCard sheet =
      (data.edgePartition
        (star.edge (block.singletonLabel pairing))).blockCard sheet := by
  unfold wholeResolution
  rw [LocalResolution.paste_newEdge_blockCard]
  change
    (resolutionAt data star pairing ((data.vertexPartition wall).repr sheet)
      (pattern ((data.vertexPartition wall).repr sheet))).newEdge.blockCard
        sheet = _
  rw [hPattern, resolutionAt_nd3_newEdge]

end DraismaVargas.LocalCases.W4Assembly
