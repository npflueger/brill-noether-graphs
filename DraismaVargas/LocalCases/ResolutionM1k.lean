module

public import DraismaVargas.LocalCases.ResolutionM11

@[expose] public section

/-!
# The local resolutions in case `w2-r2-nd3-M-1k`

This file formalizes the partition geometry of the three candidates in Figure
33 of Draisma--Vargas Part I, starting with the first.  In a wall block of size `k + 1`, choose the
singleton sheet and one sheet of the complementary `k`-block.  The new leaf
retains exactly that pair, the trivalent endpoint detaches the singleton, and
the new edge has singleton lifts throughout the wall block.

The join of the two endpoint partitions contracts back to the original wall
partition.  Both new endpoints satisfy their blockwise Riemann--Hurwitz
inequalities; at the trivalent endpoint this follows because the new edge
fully splits every endpoint block.  Candidates 2 and 3 follow, and the last
section packages all three with Equation (7); their exterior compatibility
with the rest of the gluing datum is handled in `GlobalM1k`.
-/

namespace DraismaVargas.LocalCases.ResolutionM1k

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.BalancingValencyTwo
open DraismaVargas.LocalCases.ResolutionM11

/-- Figure 33, candidate 1, inside an arbitrary ambient sheet set. -/
def firstResolution (wall : SheetPartition d) (first second : Fin d)
    (hne : first ≠ second) (hTogether : wall.Rel first second) :
    LocalResolution d where
  left := wall.pairBlock first second hne
  right := wall.detachSheet first second hne hTogether
  newEdge := wall.splitBlock first
  edge_refines_left := wall.splitBlock_refines_pairBlock first second hne
  edge_refines_right :=
    wall.splitBlock_refines_detachSheet first second hne hTogether

/-- Contracting candidate 1 rejoins the retained pair and complementary
detachment to recover the original wall partition. -/
theorem firstResolution_contracts (wall : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : wall.Rel first second) :
    (firstResolution wall first second hne hTogether).ContractsTo wall :=
  wall.isJoin_pairBlock_detachSheet first second hne hTogether

/-- The selected pair has index two at the new leaf. -/
theorem firstResolution_left_blockCard_first (wall : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : wall.Rel first second) :
    (firstResolution wall first second hne hTogether).left.blockCard first = 2 :=
  wall.pairBlock_blockCard_first first second hne hTogether

/-- The distinguished sheet becomes a singleton at the trivalent endpoint. -/
theorem firstResolution_right_blockCard_first (wall : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : wall.Rel first second) :
    (firstResolution wall first second hne hTogether).right.blockCard first = 1 :=
  wall.detachSheet_blockCard_single first second hne hTogether

/-- If the wall block has size `k + 1`, its complementary endpoint block has
size `k`. -/
theorem firstResolution_right_blockCard_second (wall : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : wall.Rel first second) (k : ℕ)
    (hCard : wall.blockCard first = k + 1) :
    (firstResolution wall first second hne hTogether).right.blockCard second = k := by
  rw [firstResolution, wall.detachSheet_blockCard_remainder first second hne
    hTogether, hCard]
  omega

/-- Every sheet in the selected wall block has unit index on the new edge. -/
theorem firstResolution_newEdge_blockCard (wall : SheetPartition d)
    (first second sheet : Fin d) (hne : first ≠ second)
    (hTogether : wall.Rel first second) (hSheet : wall.Rel first sheet) :
    (firstResolution wall first second hne hTogether).newEdge.blockCard sheet = 1 :=
  wall.splitBlock_blockCard_of_rel first sheet hSheet

/-- Candidate 1 satisfies Riemann--Hurwitz at its new leaf. -/
theorem firstResolution_left_riemannHurwitzAtBlock
    (wall : SheetPartition d) (first second : Fin d)
    (hne : first ≠ second) (hTogether : wall.Rel first second) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (firstResolution wall first second hne hTogether).left
      [(firstResolution wall first second hne hTogether).newEdge] first :=
  LocalResolution.riemannHurwitzAtBlock_leaf _ _ _ _

/-- At the trivalent endpoint, the singleton new edge contributes the full
endpoint block cardinality.  The two exterior edges each contribute at least
one block, so Riemann--Hurwitz follows without any further cardinality case
split. -/
theorem firstResolution_right_riemannHurwitzAtBlock
    (wall firstExternal secondExternal : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : wall.Rel first second) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (firstResolution wall first second hne hTogether).right
      [(firstResolution wall first second hne hTogether).newEdge,
        firstExternal, secondExternal] first := by
  intro sheet hSheet
  have hEndpointRefines :
      (wall.detachSheet first second hne hTogether).Refines wall :=
    wall.detachSheet_refines first second hne hTogether
  have hNew : (wall.splitBlock first).blockCountWithin
        (wall.detachSheet first second hne hTogether) sheet =
      (wall.detachSheet first second hne hTogether).blockCard sheet :=
    wall.splitBlock_blockCountWithin_of_refines
      (wall.detachSheet first second hne hTogether) first sheet
      hEndpointRefines hSheet
  have hFirst := firstExternal.blockCountWithin_pos
    (wall.detachSheet first second hne hTogether) sheet
  have hSecond := secondExternal.blockCountWithin_pos
    (wall.detachSheet first second hne hTogether) sheet
  simp only [firstResolution, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil]
  rw [hNew]
  norm_num
  omega

/-- The trivalent-endpoint check with an arbitrary representative of the
selected wall block, as required by blockwise global assembly. -/
theorem firstResolution_right_riemannHurwitzAtBlock_of_rel
    (wall firstExternal secondExternal : SheetPartition d)
    (first second anchor : Fin d) (hne : first ≠ second)
    (hTogether : wall.Rel first second) (hAnchor : wall.Rel first anchor) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (firstResolution wall first second hne hTogether).right
      [(firstResolution wall first second hne hTogether).newEdge,
        firstExternal, secondExternal] anchor := by
  intro sheet hSheet
  have hSelected : wall.Rel first sheet := hAnchor.trans hSheet
  have hEndpointRefines :
      (wall.detachSheet first second hne hTogether).Refines wall :=
    wall.detachSheet_refines first second hne hTogether
  have hNew : (wall.splitBlock first).blockCountWithin
        (wall.detachSheet first second hne hTogether) sheet =
      (wall.detachSheet first second hne hTogether).blockCard sheet :=
    wall.splitBlock_blockCountWithin_of_refines
      (wall.detachSheet first second hne hTogether) first sheet
      hEndpointRefines hSelected
  have hFirst := firstExternal.blockCountWithin_pos
    (wall.detachSheet first second hne hTogether) sheet
  have hSecond := secondExternal.blockCountWithin_pos
    (wall.detachSheet first second hne hTogether) sheet
  simp only [firstResolution, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, List.length_cons, List.length_nil]
  rw [hNew]
  norm_num
  omega

/-- The partition-theoretic receipt for Figure 33, candidate 1. -/
theorem firstResolution_receipt
    (wall firstExternal secondExternal : SheetPartition d)
    (first second : Fin d) (hne : first ≠ second)
    (hTogether : wall.Rel first second) (k : ℕ)
    (hCard : wall.blockCard first = k + 1)
    (hFirstRefines : firstExternal.Refines
      (firstResolution wall first second hne hTogether).right)
    (hSecondRefines : secondExternal.Refines
      (firstResolution wall first second hne hTogether).right) :
    (firstResolution wall first second hne hTogether).ContractsTo wall ∧
      firstExternal.Refines
        (firstResolution wall first second hne hTogether).right ∧
      secondExternal.Refines
        (firstResolution wall first second hne hTogether).right ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (firstResolution wall first second hne hTogether).left
        [(firstResolution wall first second hne hTogether).newEdge] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (firstResolution wall first second hne hTogether).right
        [(firstResolution wall first second hne hTogether).newEdge,
          firstExternal, secondExternal] first ∧
      (firstResolution wall first second hne hTogether).left.blockCard first = 2 ∧
      (firstResolution wall first second hne hTogether).right.blockCard first = 1 ∧
      (firstResolution wall first second hne hTogether).right.blockCard second = k ∧
      (∀ sheet, wall.Rel first sheet →
        (firstResolution wall first second hne hTogether).newEdge.blockCard sheet = 1) := by
  exact ⟨firstResolution_contracts wall first second hne hTogether,
    hFirstRefines, hSecondRefines,
    firstResolution_left_riemannHurwitzAtBlock wall first second hne hTogether,
    firstResolution_right_riemannHurwitzAtBlock wall firstExternal secondExternal
      first second hne hTogether,
    firstResolution_left_blockCard_first wall first second hne hTogether,
    firstResolution_right_blockCard_first wall first second hne hTogether,
    firstResolution_right_blockCard_second wall first second hne hTogether k hCard,
    fun sheet hSheet => firstResolution_newEdge_blockCard wall first second sheet
      hne hTogether hSheet⟩

/-! ## Candidate 2: opposite detachment at divalent endpoints -/

/-- After detaching `first`, the sheets `second` and `third` remain together
in the complementary block. -/
theorem detachFirst_rel_second_third (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third) :
    (wall.detachSheet first second hneFirstSecond hFirstSecond).Rel
      second third := by
  unfold SheetPartition.Rel
  rw [wall.detachSheet_repr_of_rel_of_ne first second second hneFirstSecond
      hFirstSecond hneFirstSecond.symm hFirstSecond,
    wall.detachSheet_repr_of_rel_of_ne first second third hneFirstSecond
      hFirstSecond hneFirstThird.symm hFirstThird]

/-- The new edge of Figure 33, candidate 2: `first` and `second` are
singletons, while the rest of their original wall block remains joined. -/
def secondNewEdge (wall : SheetPartition d) (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) : SheetPartition d :=
  (wall.detachSheet first second hneFirstSecond hFirstSecond).detachSheet
    second third hneSecondThird
    (detachFirst_rel_second_third wall first second third hFirstSecond
      hFirstThird hneFirstSecond hneFirstThird)

theorem secondNewEdge_refines_left (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    (secondNewEdge wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird).Refines
        (wall.detachSheet first second hneFirstSecond hFirstSecond) := by
  unfold secondNewEdge
  exact SheetPartition.detachSheet_refines _ _ _ _ _

theorem secondNewEdge_block_first (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    (secondNewEdge wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird).block first = {first} := by
  apply SheetPartition.block_eq_singleton_of_refines
    (secondNewEdge_refines_left wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird)
  exact wall.detachSheet_block_single first second hneFirstSecond hFirstSecond

@[simp] theorem secondNewEdge_blockCard_first (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    (secondNewEdge wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird).blockCard first = 1 := by
  simp [SheetPartition.blockCard,
    secondNewEdge_block_first wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird]

@[simp] theorem secondNewEdge_blockCard_second (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    (secondNewEdge wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird).blockCard second = 1 := by
  unfold secondNewEdge
  exact SheetPartition.detachSheet_blockCard_single _ _ _ _ _

/-- On a wall block of size `k + 1`, candidate 2's residual new-edge block
has size `k - 1`. -/
theorem secondNewEdge_blockCard_third (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) (k : ℕ)
    (hCard : wall.blockCard first = k + 1) :
    (secondNewEdge wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird).blockCard third = k - 1 := by
  unfold secondNewEdge
  rw [SheetPartition.detachSheet_blockCard_remainder,
    wall.detachSheet_blockCard_remainder first second hneFirstSecond
      hFirstSecond, hCard]
  omega

theorem secondNewEdge_refines_wall (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    (secondNewEdge wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird).Refines wall :=
  (secondNewEdge_refines_left wall first second third hFirstSecond hFirstThird
    hneFirstSecond hneFirstThird hneSecondThird).trans
      (wall.detachSheet_refines first second hneFirstSecond hFirstSecond)

theorem secondNewEdge_refines_right (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    (secondNewEdge wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird).Refines
        (wall.detachSheet second first hneFirstSecond.symm
          hFirstSecond.symm) := by
  apply SheetPartition.refines_detachSheet_of_block_singleton
    _ wall second first hneFirstSecond.symm hFirstSecond.symm
    (secondNewEdge_refines_wall wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird)
  unfold secondNewEdge
  exact SheetPartition.detachSheet_block_single _ _ _ _ _

/-- Opposite singleton detachments at the two endpoints join back to the wall.
The third sheet, which exists because `k > 1`, bridges the two detached
singletons in the generated equivalence relation. -/
theorem isJoin_oppositeDetachments (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    SheetPartition.IsJoin
      (wall.detachSheet first second hneFirstSecond hFirstSecond)
      (wall.detachSheet second first hneFirstSecond.symm hFirstSecond.symm)
      wall := by
  let left := wall.detachSheet first second hneFirstSecond hFirstSecond
  let right := wall.detachSheet second first hneFirstSecond.symm
    hFirstSecond.symm
  have hLeftRefines : left.Refines wall :=
    wall.detachSheet_refines first second hneFirstSecond hFirstSecond
  have hRightRefines : right.Refines wall :=
    wall.detachSheet_refines second first hneFirstSecond.symm hFirstSecond.symm
  have hSecondThird : wall.Rel second third :=
    hFirstSecond.symm.trans hFirstThird
  have hRightFirstThird : right.Rel first third := by
    unfold right SheetPartition.Rel
    rw [wall.detachSheet_repr_of_rel_of_ne second first first
        hneFirstSecond.symm hFirstSecond.symm hneFirstSecond
        hFirstSecond.symm,
      wall.detachSheet_repr_of_rel_of_ne second first third
        hneFirstSecond.symm hFirstSecond.symm hneSecondThird.symm
        hSecondThird]
  have connect : ∀ i, wall.Rel first i →
      Relation.EqvGen (fun a b ↦ left.Rel a b ∨ right.Rel a b) i third := by
    intro i hi
    by_cases hiFirst : i = first
    · subst i
      exact Relation.EqvGen.rel first third (Or.inr hRightFirstThird)
    · apply Relation.EqvGen.rel i third
      apply Or.inl
      unfold left SheetPartition.Rel
      rw [wall.detachSheet_repr_of_rel_of_ne first second i
          hneFirstSecond hFirstSecond hiFirst hi,
        wall.detachSheet_repr_of_rel_of_ne first second third
          hneFirstSecond hFirstSecond hneFirstThird.symm hFirstThird]
  intro i j
  constructor
  · intro hij
    by_cases hiBlock : wall.Rel first i
    · have hjBlock : wall.Rel first j := hiBlock.trans hij
      exact Relation.EqvGen.trans i third j (connect i hiBlock)
        (Relation.EqvGen.symm _ _ (connect j hjBlock))
    · have hjBlock : ¬wall.Rel first j := by
        intro hj
        exact hiBlock (hj.trans hij.symm)
      apply Relation.EqvGen.rel i j
      apply Or.inl
      unfold SheetPartition.Rel
      rw [wall.detachSheet_repr_of_not_rel first second i hneFirstSecond
          hFirstSecond hiBlock,
        wall.detachSheet_repr_of_not_rel first second j hneFirstSecond
          hFirstSecond hjBlock]
      exact hij
  · intro hij
    induction hij with
    | rel x y hxy => exact hxy.elim hLeftRefines.rel hRightRefines.rel
    | refl => exact rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Figure 33, candidate 2, at arbitrary ambient degree. -/
def secondResolution (wall : SheetPartition d) (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) : LocalResolution d where
  left := wall.detachSheet first second hneFirstSecond hFirstSecond
  right := wall.detachSheet second first hneFirstSecond.symm hFirstSecond.symm
  newEdge := secondNewEdge wall first second third hFirstSecond hFirstThird
    hneFirstSecond hneFirstThird hneSecondThird
  edge_refines_left := secondNewEdge_refines_left wall first second third
    hFirstSecond hFirstThird hneFirstSecond hneFirstThird hneSecondThird
  edge_refines_right := secondNewEdge_refines_right wall first second third
    hFirstSecond hFirstThird hneFirstSecond hneFirstThird hneSecondThird

theorem secondResolution_contracts (wall : SheetPartition d)
    (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    (secondResolution wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird).ContractsTo wall :=
  isJoin_oppositeDetachments wall first second third hFirstSecond hFirstThird
    hneFirstSecond hneFirstThird hneSecondThird

/-! ## Divalent endpoints and candidate 3 -/

/-- Every divalent endpoint satisfies the blockwise Riemann--Hurwitz
inequality, independently of the two incident partitions. -/
theorem riemannHurwitzAtBlock_divalent
    (wall endpoint firstEdge secondEdge : SheetPartition d) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall endpoint
      [firstEdge, secondEdge] anchor := by
  intro sheet _
  have hFirst := firstEdge.blockCountWithin_pos endpoint sheet
  have hSecond := secondEdge.blockCountWithin_pos endpoint sheet
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil]
  norm_num
  omega

theorem secondResolution_left_riemannHurwitzAtBlock
    (wall external : SheetPartition d) (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (secondResolution wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).left
      [(secondResolution wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).newEdge, external] first :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem secondResolution_right_riemannHurwitzAtBlock
    (wall external : SheetPartition d) (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third) :
    LocalResolution.RiemannHurwitzAtBlock wall
      (secondResolution wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).right
      [(secondResolution wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).newEdge, external] first :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

/-- Figure 33, candidate 3, retains the whole wall block at both endpoints
and along the new edge. -/
abbrev thirdResolution (wall : SheetPartition d) : LocalResolution d :=
  joinedResolutionAt wall

theorem thirdResolution_contracts (wall : SheetPartition d) :
    (thirdResolution wall).ContractsTo wall :=
  joinedResolutionAt_contracts wall

theorem thirdResolution_left_riemannHurwitzAtBlock
    (wall external : SheetPartition d) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).left
      [(thirdResolution wall).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

theorem thirdResolution_right_riemannHurwitzAtBlock
    (wall external : SheetPartition d) (anchor : Fin d) :
    LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).right
      [(thirdResolution wall).newEdge, external] anchor :=
  riemannHurwitzAtBlock_divalent _ _ _ _ _

/-- Candidate 3's new edge retains the full selected wall-block index. -/
theorem thirdResolution_newEdge_blockCard
    (wall : SheetPartition d) (first sheet : Fin d) (k : ℕ)
    (hCard : wall.blockCard first = k + 1)
    (hSheet : wall.Rel first sheet) :
    (thirdResolution wall).newEdge.blockCard sheet = k + 1 := by
  change wall.blockCard sheet = k + 1
  unfold SheetPartition.blockCard at hCard ⊢
  rw [← wall.block_eq_of_rel hSheet]
  exact hCard

/-! ## The complete local M-1k receipt -/

/-- The three Figure 33 partition resolutions, their endpoint validity on the
selected wall block, their displayed indices, and Equation (7), all at
arbitrary ambient degree.  The chosen `third` sheet witnesses the nonempty
`k - 1` residual block required by candidate 2. -/
theorem m1k_block_resolution
    {d : ℕ} (wall : SheetPartition d) (first second third : Fin d)
    (hFirstSecond : wall.Rel first second)
    (hFirstThird : wall.Rel first third)
    (hneFirstSecond : first ≠ second)
    (hneFirstThird : first ≠ third)
    (hneSecondThird : second ≠ third)
    (k : ℕ) (hk : 1 < k) (hCard : wall.blockCard first = k + 1)
    (firstExternal₁ firstExternal₂ secondExternalLeft secondExternalRight
      thirdExternalLeft thirdExternalRight : SheetPartition d)
    (hFirstExternal₁ : firstExternal₁.Refines
      (firstResolution wall first second hneFirstSecond hFirstSecond).right)
    (hFirstExternal₂ : firstExternal₂.Refines
      (firstResolution wall first second hneFirstSecond hFirstSecond).right)
    (hSecondExternalLeft : secondExternalLeft.Refines
      (secondResolution wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).left)
    (hSecondExternalRight : secondExternalRight.Refines
      (secondResolution wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).right)
    (hThirdExternalLeft : thirdExternalLeft.Refines
      (thirdResolution wall).left)
    (hThirdExternalRight : thirdExternalRight.Refines
      (thirdResolution wall).right)
    {c₁ c₂ c₃ s : ℚ}
    (hleft : c₁ + c₂ / (k : ℚ) + s = 0)
    (hright : c₃ / (k : ℚ) + s = 0) :
    (firstResolution wall first second hneFirstSecond hFirstSecond).ContractsTo
        wall ∧
      (secondResolution wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).ContractsTo wall ∧
      (thirdResolution wall).ContractsTo wall ∧
      firstExternal₁.Refines
        (firstResolution wall first second hneFirstSecond hFirstSecond).right ∧
      firstExternal₂.Refines
        (firstResolution wall first second hneFirstSecond hFirstSecond).right ∧
      secondExternalLeft.Refines
        (secondResolution wall first second third hFirstSecond hFirstThird
          hneFirstSecond hneFirstThird hneSecondThird).left ∧
      secondExternalRight.Refines
        (secondResolution wall first second third hFirstSecond hFirstThird
          hneFirstSecond hneFirstThird hneSecondThird).right ∧
      thirdExternalLeft.Refines (thirdResolution wall).left ∧
      thirdExternalRight.Refines (thirdResolution wall).right ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (firstResolution wall first second hneFirstSecond hFirstSecond).left
        [(firstResolution wall first second hneFirstSecond
          hFirstSecond).newEdge] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (firstResolution wall first second hneFirstSecond hFirstSecond).right
        [(firstResolution wall first second hneFirstSecond hFirstSecond).newEdge,
          firstExternal₁, firstExternal₂] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (secondResolution wall first second third hFirstSecond hFirstThird
          hneFirstSecond hneFirstThird hneSecondThird).left
        [(secondResolution wall first second third hFirstSecond hFirstThird
          hneFirstSecond hneFirstThird hneSecondThird).newEdge,
          secondExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall
        (secondResolution wall first second third hFirstSecond hFirstThird
          hneFirstSecond hneFirstThird hneSecondThird).right
        [(secondResolution wall first second third hFirstSecond hFirstThird
          hneFirstSecond hneFirstThird hneSecondThird).newEdge,
          secondExternalRight] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).left
        [(thirdResolution wall).newEdge, thirdExternalLeft] first ∧
      LocalResolution.RiemannHurwitzAtBlock wall (thirdResolution wall).right
        [(thirdResolution wall).newEdge, thirdExternalRight] first ∧
      (firstResolution wall first second hneFirstSecond
        hFirstSecond).left.blockCard first = 2 ∧
      (∀ sheet, wall.Rel first sheet →
        (firstResolution wall first second hneFirstSecond
          hFirstSecond).newEdge.blockCard sheet = 1) ∧
      (secondNewEdge wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).blockCard first = 1 ∧
      (secondNewEdge wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).blockCard second = 1 ∧
      (secondNewEdge wall first second third hFirstSecond hFirstThird
        hneFirstSecond hneFirstThird hneSecondThird).blockCard third = k - 1 ∧
      (∀ sheet, wall.Rel first sheet →
        (thirdResolution wall).newEdge.blockCard sheet = k + 1) ∧
      PositiveBalanceThree ![1, 2 * ((k : ℚ) - 1), 2 * ((k : ℚ) + 1)]
        ![2 * c₁, c₁ + c₂ / ((k : ℚ) - 1) + s,
          c₃ / ((k : ℚ) + 1) + s] := by
  have hkQ : (1 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  refine ⟨firstResolution_contracts wall first second hneFirstSecond
      hFirstSecond,
    secondResolution_contracts wall first second third hFirstSecond hFirstThird
      hneFirstSecond hneFirstThird hneSecondThird,
    thirdResolution_contracts wall,
    hFirstExternal₁, hFirstExternal₂, hSecondExternalLeft,
    hSecondExternalRight, hThirdExternalLeft, hThirdExternalRight,
    firstResolution_left_riemannHurwitzAtBlock wall first second
      hneFirstSecond hFirstSecond,
    firstResolution_right_riemannHurwitzAtBlock wall firstExternal₁
      firstExternal₂ first second hneFirstSecond hFirstSecond,
    secondResolution_left_riemannHurwitzAtBlock wall secondExternalLeft first
      second third hFirstSecond hFirstThird hneFirstSecond hneFirstThird
      hneSecondThird,
    secondResolution_right_riemannHurwitzAtBlock wall secondExternalRight first
      second third hFirstSecond hFirstThird hneFirstSecond hneFirstThird
      hneSecondThird,
    thirdResolution_left_riemannHurwitzAtBlock wall thirdExternalLeft first,
    thirdResolution_right_riemannHurwitzAtBlock wall thirdExternalRight first,
    firstResolution_left_blockCard_first wall first second hneFirstSecond
      hFirstSecond,
    fun sheet hSheet => firstResolution_newEdge_blockCard wall first second sheet
      hneFirstSecond hFirstSecond hSheet,
    secondNewEdge_blockCard_first wall first second third hFirstSecond
      hFirstThird hneFirstSecond hneFirstThird hneSecondThird,
    secondNewEdge_blockCard_second wall first second third hFirstSecond
      hFirstThird hneFirstSecond hneFirstThird hneSecondThird,
    secondNewEdge_blockCard_third wall first second third hFirstSecond
      hFirstThird hneFirstSecond hneFirstThird hneSecondThird k hCard,
    fun sheet hSheet =>
      thirdResolution_newEdge_blockCard wall first sheet k hCard hSheet,
    balance_M_1k hkQ hleft hright⟩

end DraismaVargas.LocalCases.ResolutionM1k
