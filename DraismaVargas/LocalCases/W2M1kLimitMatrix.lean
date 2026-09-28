import DraismaVargas.LocalCases.W2M1kRowDescent

/-!
# Figure 33's limit matrices

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7).

The retained columns, the split of the regrown column into its selected half
and Figure 33's `s`, and the readers of the selected half are the core's
(`LimitChainCore.SelectedData.matrix_retained`, `matrix_new_split`,
`new_mem_iff_of_survives`, `new_not_mem_of_dangling`), read on
`W2M1kStableLift`'s `dividedSelectedData` and `joinedSelectedData`.  On top of
them this module evaluates **two of Figure 33's three boxes**:

* `dividedMember_regrown` -- `c⁽²⁾ = c(e₁) + c(e₂)/(k-1) + s`, with
  `|e'| = 1` and `|e''| = k - 1`
  (`ResolutionM1k.secondNewEdge_blockCard_first` / `_third`);
* `joinedMember_regrown` -- `c⁽³⁾ = c(e₃)/(k+1) + s`, with `|e'| = k + 1`
  (`ResolutionM1k.thirdResolution_newEdge_blockCard`).

`s` is the core's own `LimitChainCore.backgroundColumn data wall anchor path
(star.edge 0)`, at the member's own anchor; `backgroundColumn_congr` moves the
anchor freely inside `A₀`, so the receipt in `W2M1kCommonBalance` may read it
at whichever sheet of `A₀` it names.

## `M⁽¹⁾` is absent, and why

Figure 33's first member is Base I.a, whose retained endpoint is a **target
leaf** carrying no wall direction: `W2M1kLeaves.leaf_right` says its side
assignment is constantly `true`.  `LimitChainCore.WallCandidate` asks for a
retained direction, so `M⁽¹⁾` has no `WallCandidate` and therefore no
`BackgroundShape`, `LiftData` or `SelectedData` -- see
`W2M1kStableLift.leaf_not_wallCandidate`, which proves exactly that, and note
that the obstruction is the field `left`, not any census field and not the
background block identities.  A leaf chain redoes `LimitChainCore` §3--§5 for
the leaf shape (`W2M1kLeafStableLift`, `W2M1kLeafRowDescent`,
`W2M1kLeafLimitMatrix`), as the M11 family does in `M11SplitStableLift`,
`M11SplitRowDescent` and `M11SplitLimitMatrix`; the
essential difference is that at a background wall block the leaf member's
regrown occurrence is **pruned** (`W2M1kLeaves.leaf_new_background_dangling`),
so the surviving star at a background endpoint is the literal image of the
incoming one under `oldSourceEdge` rather than the core's replacement
bijection `LimitChainCore.Background.replace`.  Figure 33's own box for that
member, `σ¹(J₀,1) = σ¹(J₁,1) = 0` and `c⁽¹⁾ = 2c(e₁)`, is already fixed at the
occurrence level by `W2M1kStableGraph.leaf_new_pin_stablePath_eq` and
`leaf_new_second_stablePath_eq`; its passage through a limit matrix is the leaf
chain's.

## Two extensions of the core's selected-set readers

`LimitChainCore.SelectedData.selected_set` covers two regrown classes above the
distinguished block and `selected_set_of_dangling` covers two of which the
second is pruned.  `M⁽²⁾` has **three** classes above `A₀` -- the two pinned
singletons and the residual `k - 1` class -- of which exactly the singleton
over `e₄`'s sheet is pruned (`W2M1kStableGraph.divided_new_deleted_dangling`),
and `M⁽³⁾` has **one**.  Both readers are stated below for an arbitrary
`LimitChainCore.SelectedData` from its public API alone; they are verbatim
`W2MkkLimitMatrix.selected_set_of_dangling_third` and `selected_set_single`,
restated rather than imported so that the M-1k chain does not depend on the
M-kk one.  They would sit naturally in `LimitChainCore` §5, beside
`selected_set_of_dangling`.

## What is not here

Equation (7) itself (with the factor two on both brackets, as
`BalancingValencyTwo.balance_M_1k` states it; `W2M1kCommonBalance` compares
this with Part I's display) and the common-balance receipt belong to
`W2M1kCommonBalance`, which this module deliberately does not import.
-/

namespace DraismaVargas.LocalCases.W2M1kLimitMatrix

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open StableSourceMatrix
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2M1kSourceCandidates W2M1kLeaves
open W2M1kStableGraph
open W2M1kStableLift W2M1kRowDescent

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-! ## §0  Two more readers of the selected half of a regrown column

Both would sit naturally in `LimitChainCore` beside `selected_set_of_dangling`;
they are stated here for an arbitrary `SelectedData` and use only its public
API. -/

/-- **Three regrown classes above the distinguished block, the third pruned.**
This is what `M⁽²⁾` needs: `{p}`, the residual `k - 1` class, and the singleton
`{q}` whose regrown occurrence dies with `e₄`. -/
theorem selected_set_of_dangling_third (rd : LimitChainCore.SelectedData data wall)
    (first second third : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel rd.selected first)
    (hSecond : (data.vertexPartition wall).Rel rd.selected second)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel rd.selected sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first ∨
        rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge second ∨
          rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge third)
    (hDangling : IsDangling rd.candidate.datum (rd.candidate.newSourceEdge third))
    (path : StablePath data) :
    (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel rd.selected edge.1.2) =
      ({rd.candidate.newSourceEdge first, rd.candidate.newSourceEdge second} :
        Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hMem, hRel⟩
    refine ⟨?_, hMem⟩
    have hEdgeNew := rd.eq_newSourceEdge_of_mem path edge hMem
    rcases hCover edge.1.2 hRel with h | h | h
    · exact Or.inl (hEdgeNew.trans h)
    · exact Or.inr (hEdgeNew.trans h)
    · exact absurd (rd.new_not_mem_of_dangling third hDangling path)
        (fun hNot ↦ hNot (by rwa [← h, ← hEdgeNew]))
  · rintro ⟨hEq, hMem⟩
    refine ⟨hMem, ?_⟩
    rcases hEq with rfl | rfl
    · exact (rd.newSourceEdge_sheet_rel_iff first).mpr hFirst
    · exact (rd.newSourceEdge_sheet_rel_iff second).mpr hSecond

/-- **One regrown class above the distinguished block.**  This is what `M⁽³⁾`
needs: it keeps the whole wall block along the new edge. -/
theorem selected_set_single (rd : LimitChainCore.SelectedData data wall) (first : Fin degree)
    (hFirst : (data.vertexPartition wall).Rel rd.selected first)
    (hCover : ∀ sheet : Fin degree, (data.vertexPartition wall).Rel rd.selected sheet →
      rd.candidate.newSourceEdge sheet = rd.candidate.newSourceEdge first)
    (path : StablePath data) :
    (rd.newOccurrences path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel rd.selected edge.1.2) =
      ({rd.candidate.newSourceEdge first} :
        Finset rd.candidate.datum.SourceEdge).filter
        (fun edge ↦ edge ∈ rd.newOccurrences path) := by
  classical
  ext edge
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hMem, hRel⟩
    exact ⟨(rd.eq_newSourceEdge_of_mem path edge hMem).trans (hCover edge.1.2 hRel), hMem⟩
  · rintro ⟨rfl, hMem⟩
    exact ⟨hMem, (rd.newSourceEdge_sheet_rel_iff first).mpr hFirst⟩

/-! ## §1  The background column does not see which sheet of `A₀` anchors it -/

theorem backgroundOccurrences_congr (data : GluingDatum target degree) (wall : target.V)
    {anchor other : Fin degree} (hRel : (data.vertexPartition wall).Rel anchor other)
    (path : StablePath data) (place : target.edges) :
    LimitChainCore.backgroundOccurrences data wall anchor path place =
      LimitChainCore.backgroundOccurrences data wall other path place := by
  classical
  ext edge
  rw [LimitChainCore.mem_backgroundOccurrences, LimitChainCore.mem_backgroundOccurrences]
  exact and_congr_right fun _ ↦
    not_congr ⟨fun h ↦ hRel.symm.trans h, fun h ↦ hRel.trans h⟩

/-- **Figure 33's `s` is a function of the wall block, not of its anchor.**
The receipt in `W2M1kCommonBalance` may therefore read it at whichever sheet of
`A₀` it names. -/
theorem backgroundColumn_congr (data : GluingDatum target degree) (wall : target.V)
    {anchor other : Fin degree} (hRel : (data.vertexPartition wall).Rel anchor other)
    (path : StablePath data) (place : target.edges) :
    LimitChainCore.backgroundColumn data wall anchor path place =
      LimitChainCore.backgroundColumn data wall other path place := by
  unfold LimitChainCore.backgroundColumn
  rw [backgroundOccurrences_congr data wall hRel path place]

/-! ## §2  The three incoming stable rows Figure 33 names -/

/-- The stable row of `e₁`. -/
noncomputable def firstRow (profile : W2R2SourceProfile.SourceProfile data star block) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.first.1, profile.first_survives⟩

/-- The stable row of `e₂`. -/
noncomputable def secondRow (profile : W2R2SourceProfile.SourceProfile data star block) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.second.1, profile.second_survives⟩

/-- The stable row of `e₃`. -/
noncomputable def thirdRow (profile : W2R2SourceProfile.SourceProfile data star block) :
    StablePath data :=
  NonDanglingEdge.stablePath ⟨profile.third.1, profile.third_survives⟩

/-- Every sheet of `A₀` carries the block's own size, `|A₀| = k + 1`. -/
theorem wall_blockCard_of_rel (shape : Shape profile) {sheet : Fin degree}
    (hRel : (data.vertexPartition wall).Rel block.1 sheet) :
    (data.vertexPartition wall).blockCard sheet = shape.k + 1 := by
  unfold SheetPartition.blockCard
  rw [← (data.vertexPartition wall).block_eq_of_rel hRel]
  exact shape.blockCard

/-! ## §3  The retained columns -/

/-- Exact retained-column occurrence dictionary of `M⁽²⁾`, including the actual
old stable class. -/
theorem divided_occurrences_retained (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) (place : target.edges) :
    occurrences (DividedData.candidate shape divided).datum
        (dividedStablePathEquiv input shape divided path)
        (occurrenceEquiv target wall (DividedData.candidate shape divided).right (some place)) =
      (occurrences data path place).image (DividedData.candidate shape divided).oldSourceEdge :=
  (dividedSelectedData input shape divided).occurrences_retained path place

/-- **Every retained column of `M⁽²⁾` is literally the incoming wall column**,
read through the proved geometric row bijection. -/
theorem divided_matrix_retained (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) (place : target.edges) :
    matrix (DividedData.candidate shape divided).datum
        (dividedStablePathEquiv input shape divided path)
        (occurrenceEquiv target wall (DividedData.candidate shape divided).right (some place)) =
      matrix data path place :=
  (dividedSelectedData input shape divided).matrix_retained path place

theorem joined_occurrences_retained (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) (place : target.edges) :
    occurrences (joinedCandidate star geometry).datum
        (joinedStablePathEquiv input shape geometry path)
        (occurrenceEquiv target wall (joinedCandidate star geometry).right (some place)) =
      (occurrences data path place).image (joinedCandidate star geometry).oldSourceEdge :=
  (joinedSelectedData input shape geometry).occurrences_retained path place

/-- **Every retained column of `M⁽³⁾` is literally the incoming wall
column.** -/
theorem joined_matrix_retained (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) (place : target.edges) :
    matrix (joinedCandidate star geometry).datum
        (joinedStablePathEquiv input shape geometry path)
        (occurrenceEquiv target wall (joinedCandidate star geometry).right (some place)) =
      matrix data path place :=
  (joinedSelectedData input shape geometry).matrix_retained path place

/-! ## §4  The regrown column of `M⁽²⁾` -/

/-- The regrown column's occurrence set of `M⁽²⁾`, read in the incoming row. -/
noncomputable def dividedNewOccurrences (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) :
    Finset (DividedData.candidate shape divided).datum.SourceEdge :=
  (dividedSelectedData input shape divided).newOccurrences path

/-- The regrown singleton over `e₁`'s sheet sits in the regrown column exactly
in `e₁`'s row. -/
theorem divided_new_double_mem_iff (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) :
    (DividedData.candidate shape divided).newSourceEdge
          (pinSheet profile profile.doubleLabel) ∈
        dividedNewOccurrences input shape divided path ↔
      path = firstRow profile :=
  ((dividedSelectedData input shape divided).new_mem_iff_of_survives
      (pinSheet profile profile.doubleLabel) rfl
      (divided_new_unit_survives input shape divided) path).trans
    ⟨fun h ↦ h.trans (congrArg NonDanglingEdge.stablePath
        (Subtype.ext (dividedRep_pin profile))),
      fun h ↦ h.trans (congrArg NonDanglingEdge.stablePath
        (Subtype.ext (dividedRep_pin profile))).symm⟩

/-- The residual regrown occurrence sits in the regrown column exactly in
`e₂`'s row. -/
theorem divided_new_third_mem_iff (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) :
    (DividedData.candidate shape divided).newSourceEdge divided.third ∈
        dividedNewOccurrences input shape divided path ↔
      path = secondRow profile :=
  ((dividedSelectedData input shape divided).new_mem_iff_of_survives divided.third
      ((pin_rel_pin profile profile.doubleLabel 0).trans divided.rel_third)
      (divided_new_third_survives input shape divided) path).trans
    ⟨fun h ↦ h.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext
        (dividedRep_of_ne profile (divided_third_ne_pin divided profile.doubleLabel)))),
      fun h ↦ h.trans (congrArg NonDanglingEdge.stablePath (Subtype.ext
        (dividedRep_of_ne profile (divided_third_ne_pin divided profile.doubleLabel)))).symm⟩

/-- **The regrown column of `M⁽²⁾`, split into its two halves**: the occurrences
above `A₀`, and Figure 33's `s`. -/
theorem divided_matrix_new_split (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) :
    matrix (DividedData.candidate shape divided).datum
        (dividedStablePathEquiv input shape divided path)
        (occurrenceEquiv target wall (DividedData.candidate shape divided).right none) =
      (∑ edge ∈ (dividedNewOccurrences input shape divided path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel
            (pinSheet profile profile.doubleLabel) edge.1.2),
        (1 : ℚ) / (DividedData.candidate shape divided).datum.sourceEdgeIndex edge) +
        LimitChainCore.backgroundColumn data wall (pinSheet profile profile.doubleLabel) path
          (star.edge 0) :=
  (dividedSelectedData input shape divided).matrix_new_split path

/-- The regrown index of `M⁽²⁾` above `A₀` is its own new-edge class size. -/
theorem divided_newSourceEdge_index (shape : Shape profile) (divided : DividedData profile)
    (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    (DividedData.candidate shape divided).datum.sourceEdgeIndex
        ((DividedData.candidate shape divided).newSourceEdge sheet) =
      (dividedNewEdge divided).blockCard sheet := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge,
    LocalResolution.paste_newEdge_blockCard, divided_resolution shape divided _
      (hWall.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  rfl

/-- `|e'| = 1`: the regrown class over `e₁`'s sheet is a singleton. -/
theorem dividedNewEdge_blockCard_double (divided : DividedData profile) :
    (dividedNewEdge divided).blockCard (pinSheet profile profile.doubleLabel) = 1 := by
  have hBlock := dividedNewEdge_block_pin divided (sideOf profile.doubleLabel)
  rw [sideLabel_sideOf] at hBlock
  unfold SheetPartition.blockCard
  rw [hBlock, Finset.card_singleton]

/-- `|e''| = k - 1`: the residual regrown class on a wall block of size
`k + 1`. -/
theorem dividedNewEdge_blockCard_third (shape : Shape profile) (divided : DividedData profile) :
    (dividedNewEdge divided).blockCard divided.third = shape.k - 1 :=
  secondNewEdge_blockCard_third (data.vertexPartition wall) (pinSheet profile 0)
    (pinSheet profile 1) divided.third (pin_rel_pin profile 0 1) divided.rel_third
    divided.pins_ne divided.ne_first divided.ne_second shape.k
    (pinSheet_blockCard_wall shape 0)

theorem divided_index_double (shape : Shape profile) (divided : DividedData profile) :
    (((DividedData.candidate shape divided).datum.sourceEdgeIndex
        ((DividedData.candidate shape divided).newSourceEdge
          (pinSheet profile profile.doubleLabel)) : ℕ) : ℚ) = 1 := by
  rw [divided_newSourceEdge_index shape divided _ (pin_rel_pin profile 0 profile.doubleLabel),
    dividedNewEdge_blockCard_double divided, Nat.cast_one]

theorem divided_index_third (shape : Shape profile) (divided : DividedData profile) :
    (((DividedData.candidate shape divided).datum.sourceEdgeIndex
        ((DividedData.candidate shape divided).newSourceEdge divided.third) : ℕ) : ℚ) =
      (shape.k : ℚ) - 1 := by
  rw [divided_newSourceEdge_index shape divided divided.third divided.rel_third,
    dividedNewEdge_blockCard_third shape divided, Nat.cast_sub shape.one_lt_k.le, Nat.cast_one]

/-- **The three regrown classes of `M⁽²⁾` above `A₀`**: the two pinned
singletons and the residual `k - 1` class. -/
theorem divided_newSourceEdge_cover (shape : Shape profile) (divided : DividedData profile)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    (DividedData.candidate shape divided).newSourceEdge sheet =
          (DividedData.candidate shape divided).newSourceEdge
            (pinSheet profile profile.doubleLabel) ∨
        (DividedData.candidate shape divided).newSourceEdge sheet =
          (DividedData.candidate shape divided).newSourceEdge divided.third ∨
      (DividedData.candidate shape divided).newSourceEdge sheet =
        (DividedData.candidate shape divided).newSourceEdge
          (pinSheet profile profile.singleLabel) := by
  by_cases hDouble : sheet = pinSheet profile profile.doubleLabel
  · exact Or.inl (by rw [hDouble])
  · by_cases hSingle : sheet = pinSheet profile profile.singleLabel
    · exact Or.inr (Or.inr (by rw [hSingle]))
    · exact Or.inr (Or.inl (divided_newSourceEdge_eq_third shape divided sheet hSheet
        (ne_pinSheet_of_ne profile 0 hDouble hSingle)
        (ne_pinSheet_of_ne profile 1 hDouble hSingle)))

/-- The two surviving regrown occurrences of `M⁽²⁾` above `A₀`, named by their
anchors.  The third class, over `e₄`'s sheet, contributes nothing. -/
theorem divided_selected_set (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) :
    (dividedNewOccurrences input shape divided path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel
          (pinSheet profile profile.doubleLabel) edge.1.2) =
      ({(DividedData.candidate shape divided).newSourceEdge
          (pinSheet profile profile.doubleLabel),
        (DividedData.candidate shape divided).newSourceEdge divided.third} :
        Finset (DividedData.candidate shape divided).datum.SourceEdge).filter
        (fun edge ↦ edge ∈ dividedNewOccurrences input shape divided path) :=
  selected_set_of_dangling_third (dividedSelectedData input shape divided)
    (pinSheet profile profile.doubleLabel) divided.third (pinSheet profile profile.singleLabel)
    rfl ((pin_rel_pin profile profile.doubleLabel 0).trans divided.rel_third)
    (fun sheet hSheet ↦ divided_newSourceEdge_cover shape divided sheet
      ((pin_rel_pin profile 0 profile.doubleLabel).trans hSheet))
    (divided_new_deleted_dangling input shape divided) path

/-- **`c⁽²⁾ = c(e₁) + c(e₂)/(k-1) + s`** (Figure 33, `M⁽²⁾`'s box).  Base II.2.2.M: the two
surviving regrown occurrences are the singleton over `e₁`'s sheet, which joins
`e₁`'s row, and the residual class of index `k - 1`, which joins `e₂`'s.  The
third regrown class, over `e₄`'s sheet, is pruned and does not appear -- which
is why Figure 33's box lists two blocks where `secondNewEdge` has three. -/
theorem dividedMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (divided : DividedData profile) (path : StablePath data) :
    matrix (DividedData.candidate shape divided).datum
        (dividedStablePathEquiv input shape divided path)
        (occurrenceEquiv target wall (DividedData.candidate shape divided).right none) =
      (if path = firstRow profile then (1 : ℚ) else 0) +
        (if path = secondRow profile then (1 : ℚ) else 0) / ((shape.k : ℚ) - 1) +
        LimitChainCore.backgroundColumn data wall (pinSheet profile profile.doubleLabel) path
          (star.edge 0) := by
  classical
  have hNe : (DividedData.candidate shape divided).newSourceEdge
      (pinSheet profile profile.doubleLabel) ≠
      (DividedData.candidate shape divided).newSourceEdge divided.third :=
    divided_newSourceEdge_pin_ne shape divided profile.doubleLabel divided.third
      (divided_third_ne_pin divided profile.doubleLabel)
  rw [divided_matrix_new_split input shape divided path,
    divided_selected_set input shape divided path, Finset.sum_filter, Finset.sum_pair hNe,
    divided_index_double shape divided, divided_index_third shape divided]
  simp only [divided_new_double_mem_iff input shape divided path,
    divided_new_third_mem_iff input shape divided path]
  split_ifs <;> ring

/-! ## §5  The regrown column of `M⁽³⁾` -/

noncomputable def joinedNewOccurrences (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) :
    Finset (joinedCandidate star geometry).datum.SourceEdge :=
  (joinedSelectedData input shape geometry).newOccurrences path

theorem joined_new_mem_iff_of_survives (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (sheet : Fin degree)
    (hRel : (data.vertexPartition wall).Rel block.1 sheet)
    (hSurvives : ¬ IsDangling (joinedCandidate star geometry).datum
      ((joinedCandidate star geometry).newSourceEdge sheet))
    (path : StablePath data) :
    (joinedCandidate star geometry).newSourceEdge sheet ∈
        joinedNewOccurrences input shape geometry path ↔
      path = thirdRow profile :=
  (joinedSelectedData input shape geometry).new_mem_iff_of_survives sheet hRel hSurvives path

/-- **The regrown column of `M⁽³⁾`, split into its two halves.** -/
theorem joined_matrix_new_split (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) :
    matrix (joinedCandidate star geometry).datum
        (joinedStablePathEquiv input shape geometry path)
        (occurrenceEquiv target wall (joinedCandidate star geometry).right none) =
      (∑ edge ∈ (joinedNewOccurrences input shape geometry path).filter
          (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2),
        (1 : ℚ) / (joinedCandidate star geometry).datum.sourceEdgeIndex edge) +
        LimitChainCore.backgroundColumn data wall block.1 path (star.edge 0) :=
  (joinedSelectedData input shape geometry).matrix_new_split path

/-- `M⁽³⁾` keeps the whole wall block along the new edge, so its regrown index
is the block's own size. -/
theorem joined_newSourceEdge_index (geometry : GlobalM1k.Geometry data wall)
    (sheet : Fin degree) :
    (joinedCandidate star geometry).datum.sourceEdgeIndex
        ((joinedCandidate star geometry).newSourceEdge sheet) =
      (data.vertexPartition wall).blockCard sheet := by
  rw [BalancedGlobal.Candidate.sourceEdgeIndex_newSourceEdge]
  exact congrArg (fun partition : SheetPartition degree ↦ partition.blockCard sheet)
    (joined_pasted_newEdge geometry)

/-- **`M⁽³⁾` has one regrown class above `A₀`.** -/
theorem joined_newSourceEdge_cover (geometry : GlobalM1k.Geometry data wall)
    (sheet : Fin degree) (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (joinedCandidate star geometry).newSourceEdge sheet =
      (joinedCandidate star geometry).newSourceEdge block.1 := by
  refine (LimitChainCore.newSourceEdge_eq_iff_rel sheet block.1).mpr ?_
  rw [joined_pasted_newEdge geometry]
  exact hSheet.symm

theorem joined_selected_set (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) :
    (joinedNewOccurrences input shape geometry path).filter
        (fun edge ↦ (data.vertexPartition wall).Rel block.1 edge.1.2) =
      ({(joinedCandidate star geometry).newSourceEdge block.1} :
        Finset (joinedCandidate star geometry).datum.SourceEdge).filter
        (fun edge ↦ edge ∈ joinedNewOccurrences input shape geometry path) :=
  selected_set_single (joinedSelectedData input shape geometry) block.1 rfl
    (fun sheet hSheet ↦ joined_newSourceEdge_cover geometry sheet hSheet) path

/-- **`c⁽³⁾ = c(e₃)/(k+1) + s`** (Figure 33, `M⁽³⁾`'s box).  Base II.1.M: the whole block is
retained along the new edge, so the one regrown occurrence has index
`|A₀| = k + 1`, and it lies in `e₃`'s row. -/
theorem joinedMember_regrown (input : W2SourceInput data star) (shape : Shape profile)
    (geometry : GlobalM1k.Geometry data wall) (path : StablePath data) :
    matrix (joinedCandidate star geometry).datum
        (joinedStablePathEquiv input shape geometry path)
        (occurrenceEquiv target wall (joinedCandidate star geometry).right none) =
      (if path = thirdRow profile then (1 : ℚ) else 0) / ((shape.k : ℚ) + 1) +
        LimitChainCore.backgroundColumn data wall block.1 path (star.edge 0) := by
  classical
  have hAnchor : (data.vertexPartition wall).Rel block.1 block.1 := rfl
  have hSurvives := joined_new_survives input shape geometry block.1 hAnchor
  rw [joined_matrix_new_split input shape geometry path,
    joined_selected_set input shape geometry path, Finset.sum_filter, Finset.sum_singleton,
    joined_newSourceEdge_index geometry block.1, wall_blockCard_of_rel shape hAnchor]
  simp only [joined_new_mem_iff_of_survives input shape geometry block.1 hAnchor hSurvives path]
  split_ifs <;> push_cast <;> ring

end DraismaVargas.LocalCases.W2M1kLimitMatrix
