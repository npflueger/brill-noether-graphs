import DraismaVargas.LocalCases.GlobalW4

/-!
# Source-facing classification of W4 wall blocks

In Draisma--Vargas Part I, Case {w4} (abbreviated W4) goes through the
auxiliary Case {aux-r0}, which first identifies the non-dangling branches of
each source block above the wall.  There are zero, two, or three; an entirely
dangling block contributes zero, while the remaining branches satisfy
dangling-no-glue.

This module makes the finite classification canonical, so that a source
theorem need not choose a `BlockPattern` and repeat the inactive branch
conditions against that choice.  A source theorem
supplies only its actual active-label finset, a proof that its cardinality is
zero, two, or three, and cardinality-one edge blocks on inactive labels.  Lean
constructs the dangling, `Nd2Block`, or `Nd3Block` classification, defines a
pattern constant on every old wall block, and derives
`DanglingSingletonProfile`.  The stable-path
classification is the genuine source input that remains.
-/

namespace DraismaVargas.LocalCases.W4SourceClassification

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4Assembly
open DraismaVargas.LocalCases.GlobalW4
open DraismaVargas.LocalCases.BalancedGlobal

variable {target : CFGraph} {degree : ℕ} {wall : target.V}

/-- The exhaustive zero/two/three-way classification of one active branch
finset, retaining the equality needed to transport inactive labels. -/
inductive ActiveBlockClassification (active : Finset (Fin 4)) : Type where
  | dangling (active_eq : ∅ = active)
  | nd2 (block : Nd2Block) (active_eq : block.activeLabels = active)
  | nd3 (block : Nd3Block) (active_eq : block.activeLabels = active)

namespace ActiveBlockClassification

/-- A fixed harmless W4 resolution pattern for an entirely dangling wall
block.  Its stable-source determinant contribution is handled separately as
zero, so no branch is declared active by this choice. -/
def danglingBlock : Nd2Block where
  first := 0
  second := 1
  distinct := by decide

/-- Classification kind before forgetting an entirely dangling block to the
harmless nd2 resolution pattern used by the candidate construction.  Keeping
this tag separate is essential: a dangling block and a genuine nd2 block can
have the same `BlockPattern`, but have different stable-source receipts. -/
inductive Kind where
  | dangling
  | nd2 (block : Nd2Block)
  | nd3 (block : Nd3Block)

/-- Retain whether a block is genuinely dangling, nd2, or nd3. -/
def kind {active : Finset (Fin 4)} :
    ActiveBlockClassification active → Kind
  | .dangling _ => .dangling
  | .nd2 block _ => .nd2 block
  | .nd3 block _ => .nd3 block

/-- Forget a classification kind to the resolution pattern used downstream. -/
def Kind.pattern : Kind → BlockPattern
  | .dangling => .nd2 danglingBlock
  | .nd2 block => .nd2 block
  | .nd3 block => .nd3 block

/-- Forget the active-label equality to the W4 resolution pattern. -/
def pattern {active : Finset (Fin 4)} :
    ActiveBlockClassification active → BlockPattern
  | classification => classification.kind.pattern

/-- Any zero-, two-, or three-element set of four star labels has the source
classification used by W4.  The zero case records a dangling block; no
ordering is imposed in the two non-dangling cases. -/
noncomputable def of_card_zero_two_or_three (active : Finset (Fin 4))
    (hCard : active.card = 0 ∨ active.card = 2 ∨ active.card = 3) :
    ActiveBlockClassification active :=
  Classical.choice (show Nonempty (ActiveBlockClassification active) from by
    rcases hCard with hZero | hTwo | hThree
    · exact ⟨.dangling (Finset.card_eq_zero.mp hZero).symm⟩
    · obtain ⟨first, second, hne, hActive⟩ := Finset.card_eq_two.mp hTwo
      exact ⟨.nd2 ⟨first, second, hne⟩ (by
        simp [Nd2Block.activeLabels, hActive])⟩
    · obtain ⟨first, second, third, hFirstSecond, hFirstThird, hSecondThird,
        hActive⟩ := Finset.card_eq_three.mp hThree
      exact ⟨.nd3
        ⟨first, second, third, hFirstSecond, hFirstThird, hSecondThird⟩ (by
          simp [Nd3Block.activeLabels, hActive])⟩)

end ActiveBlockClassification

/-- Literal source data for all blocks above a four-valent wall.  `active`
records the target branches containing the zero, two, or three non-dangling source
edges.  Every other branch is stated in dangling-no-glue's cardinality-one
form. -/
structure ActiveBranchProfile (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall) where
  active : WallBlock data wall → Finset (Fin 4)
  active_card : ∀ sourceBlock, (active sourceBlock).card = 0 ∨
    (active sourceBlock).card = 2 ∨ (active sourceBlock).card = 3
  inactive_singleton : ∀ sourceBlock label,
    label ∉ active sourceBlock →
    ∀ sheet, (data.vertexPartition wall).Rel sourceBlock.1 sheet →
      (data.edgePartition (star.edge label)).blockCard sheet = 1

namespace ActiveBranchProfile

/-- Canonically choose the nd2/nd3 representative of one source block. -/
noncomputable def classification
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
  (profile : ActiveBranchProfile data star)
    (sourceBlock : WallBlock data wall) :
    ActiveBlockClassification (profile.active sourceBlock) :=
  ActiveBlockClassification.of_card_zero_two_or_three
    (profile.active sourceBlock) (profile.active_card sourceBlock)

/-- The canonical pattern is constant on the whole old wall block because it
is indexed through the block representative. -/
noncomputable def blockPattern
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    (profile : ActiveBranchProfile data star) (sheet : Fin degree) :
    BlockPattern :=
  (profile.classification (WallBlock.ofSheet data wall sheet)).pattern

/-- Classifying a canonical block representative returns that block's chosen
active classification. -/
theorem blockPattern_anchor
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    (profile : ActiveBranchProfile data star)
    (sourceBlock : WallBlock data wall) :
    profile.blockPattern sourceBlock.1 =
      (profile.classification sourceBlock).pattern := by
  unfold blockPattern
  rw [WallBlock.ofSheet_anchor]

/-- The active-branch census and inactive cardinality-one facts imply the
literal dangling profile consumed by `GlobalW4`. -/
theorem danglingSingletonProfile
    {data : GluingDatum target degree}
    {star : W4TargetPairings.FourStar target wall}
    (profile : ActiveBranchProfile data star) :
    DanglingSingletonProfile data star profile.blockPattern where
  nd2_dangling := by
    intro anchor block hPattern label hFirst hSecond sheet hSheet
    let sourceBlock : WallBlock data wall := WallBlock.ofSheet data wall anchor
    have hAtBlock :
        (profile.classification sourceBlock).pattern = .nd2 block := by
      simpa only [blockPattern, sourceBlock] using hPattern
    cases hClassification : profile.classification sourceBlock with
    | dangling hActive =>
        apply profile.inactive_singleton sourceBlock label
        · rw [← hActive]
          simp
        · exact (data.vertexPartition wall).rel_repr_left anchor |>.trans
            hSheet
    | nd2 actual hActive =>
        rw [hClassification] at hAtBlock
        simp only [ActiveBlockClassification.pattern] at hAtBlock
        have hActual : actual = block := BlockPattern.nd2.inj hAtBlock
        subst actual
        apply profile.inactive_singleton sourceBlock label
        · rw [← hActive]
          simp [Nd2Block.activeLabels, hFirst, hSecond]
        · exact (data.vertexPartition wall).rel_repr_left anchor |>.trans hSheet
    | nd3 actual hActive =>
        rw [hClassification] at hAtBlock
        exact BlockPattern.noConfusion hAtBlock
  nd3_dangling := by
    intro anchor block hPattern label hFirst hSecond hThird sheet hSheet
    let sourceBlock : WallBlock data wall := WallBlock.ofSheet data wall anchor
    have hAtBlock :
        (profile.classification sourceBlock).pattern = .nd3 block := by
      simpa only [blockPattern, sourceBlock] using hPattern
    cases hClassification : profile.classification sourceBlock with
    | dangling hActive =>
        rw [hClassification] at hAtBlock
        exact BlockPattern.noConfusion hAtBlock
    | nd2 actual hActive =>
        rw [hClassification] at hAtBlock
        exact BlockPattern.noConfusion hAtBlock
    | nd3 actual hActive =>
        rw [hClassification] at hAtBlock
        simp only [ActiveBlockClassification.pattern] at hAtBlock
        have hActual : actual = block := BlockPattern.nd3.inj hAtBlock
        subst actual
        apply profile.inactive_singleton sourceBlock label
        · rw [← hActive]
          simp [Nd3Block.activeLabels, hFirst, hSecond, hThird]
        · exact (data.vertexPartition wall).rel_repr_left anchor |>.trans hSheet

end ActiveBranchProfile

/-- W4 semantic family from the source's active-branch census, the global
change-zero equation, and the remaining stable-path classification.  The
nd2/nd3 pattern and every dangling exterior refinement are constructed here. -/
noncomputable def presentedFamilyOfActiveBranches
    (data : GluingDatum target degree)
    (star : W4TargetPairings.FourStar target wall)
    [DecidableEq target.edges]
    (hValid : data.Valid)
    (active : ActiveBranchProfile data star)
    (hChangeZero :
      ∑ sourceBlock : WallBlock data wall,
        AuxR0Profile.wallBlockRamification data star sourceBlock = 0)
    (oldPath : Option target.edges → List data.SourceEdge)
    (newSheets : Fin 3 → Option target.edges → List (Fin degree))
    (classified : ∀ sourceBlock : WallBlock data wall,
      CanonicalBlockClassification data star active.blockPattern oldPath
        newSheets sourceBlock) :
    PresentedFamily (coordinate := Option target.edges) 3 data wall :=
  presentedFamilyOfDanglingChangeZeroClassification data star
    active.blockPattern hValid active.danglingSingletonProfile hChangeZero
    oldPath newSheets classified

end DraismaVargas.LocalCases.W4SourceClassification
