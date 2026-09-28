import DraismaVargas.LocalCases.W3FourSourceCandidates

/-!
# Source-derived W3 shift geometry (Figure 29, Equation (3))

Source: Draisma--Vargas Part I, case `{w3-r1-nd3-t2-(a>k₄)}` (within cases
`{w3-r1-nd3}` and `{w3-r1-nd3-t2}`, with their Positions I, II.a, II.b),
Figure 29 and Equation (3).  This is the `w3Shift` tag of
`ClassifiedContinuation.SourceCase`, selected by
`W3IncomingClassification.Classification.shift`: an actual `Nd3Profile` at the
unique ramified wall block whose three survivors lie above three distinct
target directions and whose largest index is *strictly* below the complete
block cardinality `|A₀|`, so that all three indices are at least two and all
three are strictly below `|A₀|`.

## What is constructed

**Figure 29's three grow members** (Position II.a, new-edge index `k + 1`),
one for each of the three actual surviving directions.  In the source the new
divalent endpoint `u` carries exactly one of the three directions, its class
`A'` is literally the new edge class `e'`, and `|A'| = |e'| = k + 1` where `k`
is that survivor's actual source index; the trivalent endpoint `v` keeps the
whole wall block `A₀ = A⁽ᵠ⁾` and the remaining two actual directions.  The
classes of `A₀` above the chosen direction other than its survivor are
dangling, hence singletons by `dangling_no_glue`, so the divalent partition is
`eₐ ∪ {x}` together with singletons.  These members need only the case
hypothesis `k < |A₀|`, which the shift case gives for all three directions.
They are `largestGrowCandidate`, `firstGrowCandidate`, `secondGrowCandidate`,
certified by `grow_members_valid_genus_index`.

**Figure 29's shrink member** (Position II.b, new-edge index `k - 1`), for the
moving direction of any `ShiftProfile`, on the extra hypothesis `ShrinkData`.
The divalent endpoint keeps `A' = eₐ` unchanged, the new edge is `eₐ` with one
sheet `x` detached, and the trivalent endpoint is `A⁽ᵠ⁾ = A₀ \ {x}` -- the
source's own cycle argument in Position II.b forces the second detachment,
and it is exactly what keeps the genus.  Together with the grow member on the
same direction this is Equation (3)'s displayed `(k-1, k+1)` pair; see
`shift_pair_valid_genus_index` and `exists_shift_pair_of_shrinkSheet`.

The three exact induced-block counts on `A₀` are what close the trivalent
Riemann--Hurwitz inequality, with equality, in both members.  For the grow
member they are `|A₀| - k`, `|A₀| + 1 - k'`, `|A₀| + 1 - k''`, summing to
`|A₀| + 2`; for the shrink member, on the class `A⁽ᵠ⁾` of size `|A₀| - 1`,
they are `|A₀| + 1 - k`, `|A₀| - k'`, `|A₀| - k''`, summing to `|A₀| + 1`.
Both use the source's `nd. r` identity `k + k' + k'' = 2|A₀|`, not a
caller-supplied diagram.

Everything is derived from a literal `ThirdEquation.W3SourceInput` and
`W3R1SourceProfile.Nd3Profile`; no numerical diagram, refinement or induced
count is supplied by the caller.  Every member is certified valid, genus
preserving, and carrying its displayed new-edge index.

The shrink member's selected block is not a star, so
`M11SourceGenus.candidate_sourceGenus_of_stars` does not apply to it.  Its
genus preservation instead goes through
`M11SourceGenus.candidate_sourceGenus_of_blockwise_euler` and the general
blockwise Euler-counting lemmas it depends on --
`SheetPartition.card_blocks_eq_sum_blockCountWithin` (in
`Infrastructure.Change`), `LocalResolution.pasteLeft_blockCountWithin`,
`LocalResolution.pasteRight_blockCountWithin` and
`LocalResolution.pasteNewEdge_blockCountWithin` (in `ResolutionAssembly`), and
`M11SourceGenus.paste_block_euler_of_counts` (in `M11SourceGenus`) -- since
`ResolutionAssembly`'s own import
closure reaches neither `Infrastructure.Change` nor `BalancedGlobal`, while
`M11SourceGenus` reaches both with no import change.

## Which datum this is about

`W3SourceInput` carries `equation_c : data.targetExcess wall = 1`, so its wall
vertex is *not* change-minimal.  This module therefore lives on the limit/wall
side of the bridge recorded in
`FullDimensionalSource.false_of_changeMinimal_auxR0SourceInput`: the same side
as `AuxR0SourceInput`, and never a `FullDimensionalSourcePresentation` datum.
The hypotheses are jointly satisfiable exactly when that interface is: every
field of `ShiftProfile` is produced from an arbitrary `Nd3Profile` plus the two
arithmetic conditions of `Classification.shift` by `shiftProfileLargest`,
`shiftProfileFirst` and `shiftProfileSecond`, which are total functions, and
`ShrinkData` is produced from `HasShrinkSheet` plus the profile's own
`two_le_moving` by `exists_shrinkData`.  `HasShrinkSheet` is not always false:
`shift_arithmetic_admits_shrinkSheet` exhibits a configuration meeting all of
the shift case's numerical constraints which carries the sheet.

## What is not constructed

Equation (3)'s determinant balance, the honest stable presentations, the
common retained columns and the stable-graph incidence transport.  Also: the
shrink members' existence at a *fixed* datum value, which this case's
arithmetic does not decide -- see `exists_shrinkSheet_iff`,
`shift_arithmetic_does_not_force_shrinkSheet` and
`shift_arithmetic_admits_shrinkSheet` below.  Position II.b needs a sheet of
the moving survivor's class lying outside *both* other survivors' classes, and
at a fixed datum value the arithmetic of this case neither supplies nor
forbids one; it can fail for all three directions at once.  On a
branch-swapped copy of the wall datum the sheet is always available
(`W3ShiftShrinkExistence.exists_branchGauge_shrinkSheet`).
-/

namespace DraismaVargas.LocalCases.W3ShiftSourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties ThirdEquation
open W3R1SourceProfile ResolutionCoarseFine GlobalCoarseFine
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary M11SourceGenus
open W3Nd2SourceCandidates (OrientedStar rightOf wallEdgesAssigned_false
  wallEdgesAssigned_true external_count_eq)
open W3FourSourceCandidates (blockCountWithin_of_singletons_off_block
  blockCard_eq_one_of_not_rel incident_anchor_wall_rel incident_target_mem)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : ThreeStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _
noncomputable local instance (data : GluingDatum target degree)
    (vertex : data.SourceVertex) : DecidableEq (IncidentSourceEdge data vertex) :=
  Classical.decEq _

variable {input : W3SourceInput data star}

/-! ## The literal `w3Shift` source profile -/

/-- **Figure 29's transferred sheet, before any profile exists.**  Position II.a
moves one sheet of the distinguished wall block lying outside a survivor's own
class into the new divalent block.  The only input is the occurrence itself and
the case hypothesis `k < |A₀|`, so the sheet is available *before* a
`ShiftProfile` is built -- which is what lets `ShiftProfile` carry it as data
rather than choose it. -/
theorem exists_transferSheet (input : W3SourceInput data star)
    (edge : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hLt : data.sourceEdgeIndex edge.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    ∃ sheet, (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet ∧
      ¬(data.edgePartition edge.1.1.1).Rel edge.1.1.2 sheet := by
  classical
  have hRefines := refines_of_mem_incidentEdges data
    (incident_target_mem input.distinguishedBlock edge)
  have hAnchor := incident_anchor_wall_rel input.distinguishedBlock edge
  have hSub : (data.edgePartition edge.1.1.1).block edge.1.1.2 ⊆
      (data.vertexPartition wall).block input.distinguishedBlock.1 := by
    intro sheet hSheet
    exact ((data.vertexPartition wall).mem_block_iff _ _).mpr
      (hAnchor.trans (hRefines.rel
        (((data.edgePartition edge.1.1.1).mem_block_iff _ _).mp hSheet)))
  have hCard : (data.edgePartition edge.1.1.1).blockCard edge.1.1.2 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 := hLt
  unfold SheetPartition.blockCard at hCard
  have hNe : (data.edgePartition edge.1.1.1).block edge.1.1.2 ≠
      (data.vertexPartition wall).block input.distinguishedBlock.1 := by
    intro hEq
    rw [hEq] at hCard
    omega
  have hSsub := Finset.ssubset_iff_subset_ne.mpr ⟨hSub, hNe⟩
  obtain ⟨sheet, hMem, hNotMem⟩ := (Finset.ssubset_iff_of_subset hSub).mp hSsub
  exact ⟨sheet, ((data.vertexPartition wall).mem_block_iff _ _).mp hMem,
    fun hRel ↦ hNotMem
      (((data.edgePartition edge.1.1.1).mem_block_iff _ _).mpr hRel)⟩

/-- Figure 29's actual source profile at the unique ramified wall block,
presented with one of the three survivors singled out as the *moving*
direction whose index shifts.  `moving` is the occurrence whose direction
Figure 29 places alone at the new divalent endpoint; `firstRest` and
`secondRest` stay at the trivalent endpoint.  Equation (3) runs over all three
choices, which is what `shiftProfileLargest`, `shiftProfileFirst` and
`shiftProfileSecond` supply.

The last three fields are the shift case's own arithmetic: the source's
`nd. r` identity `k₂ + k₃ + k₄ = 2|A₀|`, the case hypothesis `k < |A₀|` in the
moving direction, and the source's `min(k₂,k₃,k₄) ≥ 2`. -/
structure ShiftProfile (input : W3SourceInput data star) where
  moving : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall input.distinguishedBlock)
  firstRest : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall input.distinguishedBlock)
  secondRest : IncidentSourceEdge data
    (WallBlock.sourceVertex data wall input.distinguishedBlock)
  moving_ne_first : moving ≠ firstRest
  moving_ne_second : moving ≠ secondRest
  first_ne_second : firstRest ≠ secondRest
  surviving : survivors data input.distinguishedBlock =
    {moving, firstRest, secondRest}
  moving_target_ne_first : moving.1.1.1 ≠ firstRest.1.1.1
  moving_target_ne_second : moving.1.1.1 ≠ secondRest.1.1.1
  first_target_ne_second : firstRest.1.1.1 ≠ secondRest.1.1.1
  index_sum : data.sourceEdgeIndex moving.1 + data.sourceEdgeIndex firstRest.1 +
      data.sourceEdgeIndex secondRest.1 =
    2 * (data.vertexPartition wall).blockCard input.distinguishedBlock.1
  moving_lt : data.sourceEdgeIndex moving.1 <
    (data.vertexPartition wall).blockCard input.distinguishedBlock.1
  two_le_moving : 2 ≤ data.sourceEdgeIndex moving.1
  /-- Position II.a's transferred sheet, carried as **data**: a sheet of the
  distinguished wall block outside the moving survivor's own class.  It exists
  for every orientation by `exists_transferSheet`, but which one it is has to be
  a field, exactly as `ShrinkData.transfer` is, so that an incoming Position
  II.a cover's own sheet can be installed (`withExtra`). -/
  extra : Fin degree
  /-- The transferred sheet lies in the distinguished wall block. -/
  extra_wall_rel : (data.vertexPartition wall).Rel input.distinguishedBlock.1 extra
  /-- ... and outside the moving survivor's class. -/
  extra_separate : ¬(data.edgePartition moving.1.1.1).Rel moving.1.1.2 extra

/-- Figure 29's `α = 4` orientation: the profile's largest survivor moves. -/
noncomputable def shiftProfileLargest (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    ShiftProfile input where
  moving := profile.largest
  firstRest := profile.first
  secondRest := profile.second
  moving_ne_first := fun h ↦ profile.first_ne_largest h.symm
  moving_ne_second := fun h ↦ profile.second_ne_largest h.symm
  first_ne_second := profile.first_ne_second
  surviving := by
    rw [profile.surviving]
    ext edge
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  moving_target_ne_first := profile.first_target_ne.symm
  moving_target_ne_second := profile.second_target_ne.symm
  first_target_ne_second := directions
  index_sum := by
    have h := profile.index_sum
    omega
  moving_lt := largest_lt
  two_le_moving := (profile.indices_two_le_of_largest_lt largest_lt).2.2
  extra := (exists_transferSheet input profile.largest (largest_lt)).choose
  extra_wall_rel := (exists_transferSheet input profile.largest (largest_lt)).choose_spec.1
  extra_separate := (exists_transferSheet input profile.largest (largest_lt)).choose_spec.2

/-- Figure 29's `α = 2` orientation: the profile's `first` survivor moves. -/
noncomputable def shiftProfileFirst (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    ShiftProfile input where
  moving := profile.first
  firstRest := profile.second
  secondRest := profile.largest
  moving_ne_first := profile.first_ne_second
  moving_ne_second := profile.first_ne_largest
  first_ne_second := profile.second_ne_largest
  surviving := profile.surviving
  moving_target_ne_first := directions
  moving_target_ne_second := profile.first_target_ne
  first_target_ne_second := profile.second_target_ne
  index_sum := profile.index_sum
  moving_lt := lt_of_le_of_lt profile.first_le largest_lt
  two_le_moving := (profile.indices_two_le_of_largest_lt largest_lt).1
  extra := (exists_transferSheet input profile.first (lt_of_le_of_lt profile.first_le largest_lt)).choose
  extra_wall_rel := (exists_transferSheet input profile.first (lt_of_le_of_lt profile.first_le largest_lt)).choose_spec.1
  extra_separate := (exists_transferSheet input profile.first (lt_of_le_of_lt profile.first_le largest_lt)).choose_spec.2

/-- Figure 29's `α = 3` orientation: the profile's `second` survivor moves. -/
noncomputable def shiftProfileSecond (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    ShiftProfile input where
  moving := profile.second
  firstRest := profile.first
  secondRest := profile.largest
  moving_ne_first := fun h ↦ profile.first_ne_second h.symm
  moving_ne_second := profile.second_ne_largest
  first_ne_second := profile.first_ne_largest
  surviving := by
    rw [profile.surviving]
    ext edge
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  moving_target_ne_first := fun h ↦ directions h.symm
  moving_target_ne_second := profile.second_target_ne
  first_target_ne_second := profile.first_target_ne
  index_sum := by
    have h := profile.index_sum
    omega
  moving_lt := lt_of_le_of_lt profile.second_le largest_lt
  two_le_moving := (profile.indices_two_le_of_largest_lt largest_lt).2.1
  extra := (exists_transferSheet input profile.second (lt_of_le_of_lt profile.second_le largest_lt)).choose
  extra_wall_rel := (exists_transferSheet input profile.second (lt_of_le_of_lt profile.second_le largest_lt)).choose_spec.1
  extra_separate := (exists_transferSheet input profile.second (lt_of_le_of_lt profile.second_le largest_lt)).choose_spec.2

/-! ## Each actual direction is represented by a single survivor -/

/-- The moving direction is represented by a single survivor. -/
theorem moving_unique (shift : ShiftProfile input)
    (candidate : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hCandidate : candidate ∈ survivors data input.distinguishedBlock)
    (hTarget : candidate.1.1.1 = shift.moving.1.1.1) :
    candidate = shift.moving := by
  rw [shift.surviving] at hCandidate
  simp only [Finset.mem_insert, Finset.mem_singleton] at hCandidate
  rcases hCandidate with hMoving | hFirst | hSecond
  · exact hMoving
  · exact (shift.moving_target_ne_first ((hFirst ▸ hTarget)).symm).elim
  · exact (shift.moving_target_ne_second ((hSecond ▸ hTarget)).symm).elim

/-- The first retained direction is represented by a single survivor. -/
theorem firstRest_unique (shift : ShiftProfile input)
    (candidate : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hCandidate : candidate ∈ survivors data input.distinguishedBlock)
    (hTarget : candidate.1.1.1 = shift.firstRest.1.1.1) :
    candidate = shift.firstRest := by
  rw [shift.surviving] at hCandidate
  simp only [Finset.mem_insert, Finset.mem_singleton] at hCandidate
  rcases hCandidate with hMoving | hFirst | hSecond
  · exact (shift.moving_target_ne_first (hMoving ▸ hTarget)).elim
  · exact hFirst
  · exact (shift.first_target_ne_second ((hSecond ▸ hTarget)).symm).elim

/-- The second retained direction is represented by a single survivor. -/
theorem secondRest_unique (shift : ShiftProfile input)
    (candidate : IncidentSourceEdge data
      (WallBlock.sourceVertex data wall input.distinguishedBlock))
    (hCandidate : candidate ∈ survivors data input.distinguishedBlock)
    (hTarget : candidate.1.1.1 = shift.secondRest.1.1.1) :
    candidate = shift.secondRest := by
  rw [shift.surviving] at hCandidate
  simp only [Finset.mem_insert, Finset.mem_singleton] at hCandidate
  rcases hCandidate with hMoving | hFirst | hSecond
  · exact (shift.moving_target_ne_second (hMoving ▸ hTarget)).elim
  · exact (shift.first_target_ne_second (hFirst ▸ hTarget)).elim
  · exact hSecond

namespace ShiftProfile

/-! ## The three actual target directions -/

/-- The direction Figure 29 places alone at the new divalent endpoint. -/
abbrev movingTarget (shift : ShiftProfile input) : target.edges :=
  shift.moving.1.1.1

/-- The canonical sheet of the moving survivor. -/
abbrev movingAnchor (shift : ShiftProfile input) : Fin degree :=
  shift.moving.1.1.2

/-- The first retained direction, at the trivalent endpoint. -/
abbrev firstTarget (shift : ShiftProfile input) : target.edges :=
  shift.firstRest.1.1.1

/-- The canonical sheet of the first retained survivor. -/
abbrev firstAnchor (shift : ShiftProfile input) : Fin degree :=
  shift.firstRest.1.1.2

/-- The second retained direction, at the trivalent endpoint. -/
abbrev secondTarget (shift : ShiftProfile input) : target.edges :=
  shift.secondRest.1.1.1

/-- The canonical sheet of the second retained survivor. -/
abbrev secondAnchor (shift : ShiftProfile input) : Fin degree :=
  shift.secondRest.1.1.2

theorem movingTarget_mem (shift : ShiftProfile input) :
    shift.movingTarget ∈ GluingDatum.incidentEdges wall :=
  incident_target_mem input.distinguishedBlock shift.moving

theorem firstTarget_mem (shift : ShiftProfile input) :
    shift.firstTarget ∈ GluingDatum.incidentEdges wall :=
  incident_target_mem input.distinguishedBlock shift.firstRest

theorem secondTarget_mem (shift : ShiftProfile input) :
    shift.secondTarget ∈ GluingDatum.incidentEdges wall :=
  incident_target_mem input.distinguishedBlock shift.secondRest

theorem movingAnchor_wall_rel (shift : ShiftProfile input) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 shift.movingAnchor :=
  incident_anchor_wall_rel input.distinguishedBlock shift.moving

theorem firstAnchor_wall_rel (shift : ShiftProfile input) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 shift.firstAnchor :=
  incident_anchor_wall_rel input.distinguishedBlock shift.firstRest

theorem secondAnchor_wall_rel (shift : ShiftProfile input) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 shift.secondAnchor :=
  incident_anchor_wall_rel input.distinguishedBlock shift.secondRest

theorem movingTarget_refines (shift : ShiftProfile input) :
    (data.edgePartition shift.movingTarget).Refines (data.vertexPartition wall) :=
  refines_of_mem_incidentEdges data shift.movingTarget_mem

/-- The trivalent star is exactly the three actual surviving directions. -/
theorem incidentEdges_eq (shift : ShiftProfile input) :
    GluingDatum.incidentEdges wall =
      {shift.movingTarget, shift.firstTarget, shift.secondTarget} := by
  classical
  have hSubset : ({shift.movingTarget, shift.firstTarget, shift.secondTarget} :
      Finset target.edges) ⊆ GluingDatum.incidentEdges wall := by
    intro edge hEdge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hEdge
    rcases hEdge with rfl | rfl | rfl
    · exact shift.movingTarget_mem
    · exact shift.firstTarget_mem
    · exact shift.secondTarget_mem
  have hCard : ({shift.movingTarget, shift.firstTarget, shift.secondTarget} :
      Finset target.edges).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨shift.moving_target_ne_first, shift.moving_target_ne_second⟩),
      Finset.card_insert_of_notMem (by
        simpa using shift.first_target_ne_second), Finset.card_singleton]
  exact (Finset.eq_of_subset_of_card_le hSubset
    (by rw [hCard, star.card_incidentEdges])).symm

/-- Figure 29's orientation for a grow member: the moving direction alone at
the divalent endpoint, the other two at the trivalent endpoint. -/
noncomputable def orientation (shift : ShiftProfile input) :
    OrientedStar target wall shift.movingTarget where
  rightFirst := shift.firstTarget
  rightSecond := shift.secondTarget
  left_mem := shift.movingTarget_mem
  rightFirst_ne_left := shift.moving_target_ne_first.symm
  rightSecond_ne_left := shift.moving_target_ne_second.symm
  right_ne := shift.first_target_ne_second
  incidentEdges_eq := shift.incidentEdges_eq

end ShiftProfile

/-! ## The dangling complement of each surviving direction -/

/-- Every occurrence above the moving direction other than its survivor is a
singleton class. -/
theorem moving_blockCard_eq_one (shift : ShiftProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition shift.movingTarget).Rel shift.movingAnchor sheet) :
    (data.edgePartition shift.movingTarget).blockCard sheet = 1 :=
  blockCard_eq_one_of_not_rel shift.moving (moving_unique shift) sheet hSheet hNe

/-- Every occurrence above the first retained direction other than its
survivor is a singleton class. -/
theorem firstRest_blockCard_eq_one (shift : ShiftProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition shift.firstTarget).Rel shift.firstAnchor sheet) :
    (data.edgePartition shift.firstTarget).blockCard sheet = 1 :=
  blockCard_eq_one_of_not_rel shift.firstRest (firstRest_unique shift) sheet hSheet hNe

/-- Every occurrence above the second retained direction other than its
survivor is a singleton class. -/
theorem secondRest_blockCard_eq_one (shift : ShiftProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬(data.edgePartition shift.secondTarget).Rel shift.secondAnchor sheet) :
    (data.edgePartition shift.secondTarget).blockCard sheet = 1 :=
  blockCard_eq_one_of_not_rel shift.secondRest (secondRest_unique shift) sheet hSheet hNe

namespace ShiftProfile

/-! ## The transferred sheet and the grow partition -/

/-- The moving survivor does not fill the distinguished wall block.  In the
shift case this is the case hypothesis `k < |A₀|` itself, and it holds for all
three directions because the largest index is already below `|A₀|`. -/
theorem movingCard_lt (shift : ShiftProfile input) :
    (data.edgePartition shift.movingTarget).blockCard shift.movingAnchor <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
  shift.moving_lt

/-- Figure 29's Position II.a transfers one sheet of the distinguished wall
block outside the moving survivor's own class into the new divalent block.
The sheet is a **field** of `ShiftProfile`, so this is the field read back;
`exists_transferSheet`, the profile-free form, is what *builds* profiles. -/
theorem exists_extraSheet (shift : ShiftProfile input) :
    ∃ sheet, (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet ∧
      ¬(data.edgePartition shift.movingTarget).Rel shift.movingAnchor sheet :=
  ⟨shift.extra, shift.extra_wall_rel, shift.extra_separate⟩

/-- The transferred sheet: the profile's own `extra` field, not a choice. -/
def extraSheet (shift : ShiftProfile input) : Fin degree :=
  shift.extra

theorem extraSheet_wall_rel (shift : ShiftProfile input) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 shift.extraSheet :=
  shift.extra_wall_rel

theorem extraSheet_separate (shift : ShiftProfile input) :
    ¬(data.edgePartition shift.movingTarget).Rel shift.movingAnchor shift.extraSheet :=
  shift.extra_separate

/-- **Installing a prescribed transferred sheet.**  Every other field is
untouched, so the three surviving occurrences, their directions, their anchors
and all of the case's arithmetic are literally the same; only `growPartition`
and the objects built from it move.  This is what lets an incoming Position II.a
cover's own sheet `y ∈ A₀ \ e_α` be the one Figure 29's grow member transfers. -/
def withExtra (shift : ShiftProfile input) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSep : ¬(data.edgePartition shift.movingTarget).Rel shift.movingAnchor sheet) :
    ShiftProfile input :=
  { shift with extra := sheet, extra_wall_rel := hWall, extra_separate := hSep }

@[simp] theorem withExtra_extraSheet (shift : ShiftProfile input) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hSep : ¬(data.edgePartition shift.movingTarget).Rel shift.movingAnchor sheet) :
    (shift.withExtra sheet hWall hSep).extraSheet = sheet := rfl

/-- The new divalent endpoint's partition: the moving direction's actual edge
partition with the transferred sheet joined to the moving survivor's class.
Only two classes inside the distinguished wall block are touched, so this is
already local: away from that block it is literally the edge partition. -/
noncomputable def growPartition (shift : ShiftProfile input) :
    SheetPartition degree :=
  (data.edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor
    shift.extraSheet shift.extraSheet_separate

theorem growPartition_rel_movingAnchor_iff (shift : ShiftProfile input)
    (sheet : Fin degree) :
    shift.growPartition.Rel shift.movingAnchor sheet ↔
      (data.edgePartition shift.movingTarget).Rel shift.movingAnchor sheet ∨
        (data.edgePartition shift.movingTarget).Rel shift.extraSheet sheet :=
  SheetPartition.mergeBlocks_rel_first_iff _ _ _ _ _

theorem movingTarget_refines_growPartition (shift : ShiftProfile input) :
    (data.edgePartition shift.movingTarget).Refines shift.growPartition :=
  SheetPartition.refines_mergeBlocks _ _ _ _

theorem growPartition_refines (shift : ShiftProfile input) :
    shift.growPartition.Refines (data.vertexPartition wall) :=
  SheetPartition.mergeBlocks_refines_coarse _ _ _ _ _ shift.movingTarget_refines
    (shift.movingAnchor_wall_rel.symm.trans shift.extraSheet_wall_rel)

theorem growPartition_blockCard_movingAnchor (shift : ShiftProfile input) :
    shift.growPartition.blockCard shift.movingAnchor =
      data.sourceEdgeIndex shift.moving.1 + 1 := by
  have hSingleton : (data.edgePartition shift.movingTarget).block shift.extraSheet =
      {shift.extraSheet} :=
    SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
      (moving_blockCard_eq_one shift shift.extraSheet shift.extraSheet_wall_rel
        shift.extraSheet_separate)
  exact SheetPartition.mergeBlocks_blockCard_first_of_singleton _ _ _ _ hSingleton

theorem growPartition_blockCard_of_not_rel (shift : ShiftProfile input)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬shift.growPartition.Rel shift.movingAnchor sheet) :
    shift.growPartition.blockCard sheet = 1 := by
  rw [shift.growPartition_rel_movingAnchor_iff sheet, not_or] at hNe
  obtain ⟨hMoving, hExtra⟩ := hNe
  have hBlock := SheetPartition.mergeBlocks_block_of_separate
    (data.edgePartition shift.movingTarget) shift.movingAnchor shift.extraSheet sheet
    shift.extraSheet_separate (fun h ↦ hMoving h.symm) (fun h ↦ hExtra h.symm)
  change ((data.edgePartition shift.movingTarget).mergeBlocks shift.movingAnchor
    shift.extraSheet shift.extraSheet_separate).blockCard sheet = 1
  unfold SheetPartition.blockCard
  rw [hBlock]
  exact moving_blockCard_eq_one shift sheet hSheet hMoving

/-! ## The three exact induced-block counts on the distinguished block -/

theorem growPartition_blockCountWithin (shift : ShiftProfile input)
    (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    shift.growPartition.blockCountWithin (data.vertexPartition wall) sheet +
        (data.sourceEdgeIndex shift.moving.1 + 1) =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 + 1 := by
  have hCount := blockCountWithin_of_singletons_off_block shift.growPartition
    (data.vertexPartition wall) shift.growPartition_refines sheet shift.movingAnchor
    (hSheet.symm.trans shift.movingAnchor_wall_rel)
    (fun other hOther hNe ↦ shift.growPartition_blockCard_of_not_rel other
      (hSheet.trans hOther) hNe)
  rw [shift.growPartition_blockCard_movingAnchor,
    ← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet] at hCount
  exact hCount

theorem firstRest_blockCountWithin (shift : ShiftProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition shift.firstTarget).blockCountWithin
          (data.vertexPartition wall) sheet +
        data.sourceEdgeIndex shift.firstRest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 + 1 := by
  have hCount := blockCountWithin_of_singletons_off_block
    (data.edgePartition shift.firstTarget) (data.vertexPartition wall)
    (refines_of_mem_incidentEdges data shift.firstTarget_mem) sheet
    shift.firstAnchor (hSheet.symm.trans shift.firstAnchor_wall_rel)
    (fun other hOther hNe ↦ firstRest_blockCard_eq_one shift other
      (hSheet.trans hOther) hNe)
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet] at hCount
  exact hCount

theorem secondRest_blockCountWithin (shift : ShiftProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition shift.secondTarget).blockCountWithin
          (data.vertexPartition wall) sheet +
        data.sourceEdgeIndex shift.secondRest.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 + 1 := by
  have hCount := blockCountWithin_of_singletons_off_block
    (data.edgePartition shift.secondTarget) (data.vertexPartition wall)
    (refines_of_mem_incidentEdges data shift.secondTarget_mem) sheet
    shift.secondAnchor (hSheet.symm.trans shift.secondAnchor_wall_rel)
    (fun other hOther hNe ↦ secondRest_blockCard_eq_one shift other
      (hSheet.trans hOther) hNe)
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet] at hCount
  exact hCount

/-- The selected trivalent endpoint's Riemann--Hurwitz count.  The moving
direction contributes `|A₀| - k` induced blocks and the two retained
directions `|A₀| + 1 - k'` and `|A₀| + 1 - k''`, so the source's identity
`k + k' + k'' = 2|A₀|` makes the three exact counts add to `|A₀| + 2` and the
inequality below is an equality. -/
theorem selected_rightCounts (shift : ShiftProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    shift.growPartition.blockCountWithin (data.vertexPartition wall) sheet +
        (data.edgePartition shift.firstTarget).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition shift.secondTarget).blockCountWithin
          (data.vertexPartition wall) sheet ≥
      (data.vertexPartition wall).blockCard sheet + 2 := by
  have hMoving := shift.growPartition_blockCountWithin sheet hSheet
  have hFirst := shift.firstRest_blockCountWithin sheet hSheet
  have hSecond := shift.secondRest_blockCountWithin sheet hSheet
  have hSum := shift.index_sum
  have hCard : (data.vertexPartition wall).blockCard sheet =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
    (SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet).symm
  omega

/-! ## The arbitrary-degree background and the grow member -/

/-- Every unramified wall block is resolved with the moving direction's own
edge partition on the new edge and at the divalent endpoint.  The original
`r = 0` ramification equation is exactly the trivalent endpoint count there,
so no background receipt is assumed. -/
noncomputable def background (shift : ShiftProfile input) :
    Background data wall shift.movingAnchor := by
  let orientation := shift.orientation
  let fine := data.edgePartition shift.movingTarget
  have hFine := shift.movingTarget_refines
  let localResolution : LocalResolution degree :=
    fineResolution (data.vertexPartition wall) fine hFine
  refine {
    right := rightOf shift.movingTarget
    resolution := fun _ ↦ localResolution
    contracts := ?_
    exterior := ?_
    leftEdges := [shift.movingTarget]
    rightEdges := [orientation.rightFirst, orientation.rightSecond]
    leftEdges_eq := ?_
    rightEdges_eq := ?_
    left_riemannHurwitz := ?_
    right_riemannHurwitz := ?_ }
  · intro _ _
    exact fineResolution_contracts _ fine hFine
  · intro edge hIncident _ _
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hEq : edge = shift.movingTarget
    · subst edge
      change fine.Refines
        (if rightOf shift.movingTarget shift.movingTarget then
          localResolution.right else localResolution.left)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false,
        localResolution, fineResolution]
      exact SheetPartition.Refines.refl fine
    · have hRight : rightOf shift.movingTarget edge = true := by
        simp [rightOf, hEq]
      rw [hRight, if_pos rfl]
      change (data.edgePartition edge).Refines (data.vertexPartition wall)
      exact refines_of_mem_incidentEdges data hAt
  · rw [wallEdgesAssigned_false orientation]
    rfl
  · rw [wallEdgesAssigned_true orientation]
    rw [Finset.insert_val_of_notMem (by simpa using orientation.right_ne)]
    rfl
  · intro anchor _ _
    exact fineResolution_left_riemannHurwitzAtBlock
      (data.vertexPartition wall) fine (data.edgePartition shift.movingTarget)
      hFine anchor
  · intro anchor _ hOther
    apply riemannHurwitzAtBlock_trivalent_of_counts
      (data.vertexPartition wall) (data.vertexPartition wall) fine
      (data.edgePartition orientation.rightFirst)
      (data.edgePartition orientation.rightSecond) anchor
    intro sheet hSheet
    have hSheetOther : ¬(data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet := fun h ↦ hOther
      (shift.movingAnchor_wall_rel.symm.trans h |>.trans hSheet.symm)
    have hBlockNe : (data.vertexPartition wall).toBlock sheet ≠
        input.distinguishedBlock := by
      intro hEq
      apply hSheetOther
      have hValue := congrArg Subtype.val hEq
      change (data.vertexPartition wall).repr sheet =
        input.distinguishedBlock.1 at hValue
      change (data.vertexPartition wall).repr input.distinguishedBlock.1 =
        (data.vertexPartition wall).repr sheet
      rw [input.distinguishedBlock.2, hValue]
    have hZero := input.localRamification_eq_zero_of_ne hBlockNe
    have hTotal := external_count_eq (data := data) star orientation sheet
    rw [hZero] at hTotal
    have hTotalNat' :
        (data.edgePartition shift.movingTarget).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          0 + 2 + (data.vertexPartition wall).blockCard sheet := by
      exact_mod_cast hTotal
    have hTotalNat :
        fine.blockCountWithin (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightFirst).blockCountWithin
              (data.vertexPartition wall) sheet +
            (data.edgePartition orientation.rightSecond).blockCountWithin
              (data.vertexPartition wall) sheet =
          (data.vertexPartition wall).blockCard sheet + 2 := by
      simpa [fine, Nat.add_comm] using hTotalNat'
    change fine.blockCountWithin (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightFirst).blockCountWithin
          (data.vertexPartition wall) sheet +
        (data.edgePartition orientation.rightSecond).blockCountWithin
          (data.vertexPartition wall) sheet ≥
      (data.vertexPartition wall).blockCard sheet + 2
    exact hTotalNat.ge

/-- Figure 29's grow member: the moving direction's class absorbs one further
sheet of the distinguished wall block at the new divalent endpoint, and the
other two actual directions stay at the trivalent endpoint. -/
noncomputable def growPattern (shift : ShiftProfile input) :
    TrivalentPattern (data := data) (wall := wall) shift.movingAnchor
      (fineResolution (data.vertexPartition wall) shift.growPartition
        shift.growPartition_refines) := by
  refine {
    background := shift.background
    leftExternal := shift.movingTarget
    rightExternalFirst := shift.orientation.rightFirst
    rightExternalSecond := shift.orientation.rightSecond
    leftEdges := rfl
    rightEdges := rfl
    exterior := ?_
    rightCounts := ?_ }
  · intro edge hIncident
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hEq : edge = shift.movingTarget
    · subst edge
      change (data.edgePartition shift.movingTarget).Refines
        (if rightOf shift.movingTarget shift.movingTarget then
          (data.vertexPartition wall) else shift.growPartition)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false]
      exact shift.movingTarget_refines_growPartition
    · have hRight : rightOf shift.movingTarget edge = true := by
        simp [rightOf, hEq]
      change (data.edgePartition edge).Refines
        (if rightOf shift.movingTarget edge then
          (data.vertexPartition wall) else shift.growPartition)
      rw [hRight, if_pos rfl]
      exact refines_of_mem_incidentEdges data hAt
  · intro anchor hAnchor sheet hSheet
    have hDistSheet : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet :=
      shift.movingAnchor_wall_rel.trans hAnchor |>.trans hSheet
    exact shift.selected_rightCounts sheet hDistSheet

/-- The actual globally assembled Figure 29 grow member. -/
noncomputable def growCandidate (shift : ShiftProfile input) :
    BalancedGlobal.Candidate target degree data wall :=
  shift.growPattern.candidate
    (fineResolution_contracts (data.vertexPartition wall) shift.growPartition
      shift.growPartition_refines)

/-- The source-derived grow member is valid whenever the incoming datum is. -/
theorem growCandidate_valid (shift : ShiftProfile input) :
    shift.growCandidate.datum.Valid :=
  shift.growCandidate.datum_valid input.valid

/-- The grow member preserves the complete quotient-source genus.  Selected
and background blocks are both pasted stars, so the Euler identity is
pointwise and does not assume a separate genus receipt. -/
theorem growCandidate_sourceGenus (shift : ShiftProfile input) :
    genus shift.growCandidate.datum.sourceGraph = genus data.sourceGraph := by
  apply candidate_sourceGenus_of_stars
  intro anchor
  have hResolution : shift.growCandidate.resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        (fineResolution (data.vertexPartition wall) shift.growPartition
          shift.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
        anchor := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel shift.movingAnchor anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    exact Or.inr ⟨rfl, rfl⟩

/-- The displayed Figure 29 index of a grow member: over the distinguished
wall block the new edge carries one class of cardinality `k + 1`, where `k` is
the moving survivor's actual source index. -/
theorem growCandidate_newEdge_blockCard (shift : ShiftProfile input) :
    (shift.growCandidate.resolution shift.movingAnchor).newEdge.blockCard
        shift.movingAnchor = data.sourceEdgeIndex shift.moving.1 + 1 := by
  have hResolution : shift.growCandidate.resolution shift.movingAnchor =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        (fineResolution (data.vertexPartition wall) shift.growPartition
          shift.growPartition_refines)
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
        shift.movingAnchor := rfl
  rw [hResolution, LocalResolution.onBlock_of_rel _ _ _ _ _
    (show (data.vertexPartition wall).Rel shift.movingAnchor shift.movingAnchor
      from rfl)]
  exact shift.growPartition_blockCard_movingAnchor

end ShiftProfile

/-! ## Figure 29's three grow members on the actual source profile -/

/-- Figure 29's `M⁽²⁾`: the largest survivor's direction grows to `k₄ + 1`. -/
noncomputable def largestGrowCandidate
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    BalancedGlobal.Candidate target degree data wall :=
  (shiftProfileLargest profile directions largest_lt).growCandidate

/-- Figure 29's `M⁽⁴⁾`: the `first` survivor's direction grows to `k₂ + 1`. -/
noncomputable def firstGrowCandidate
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    BalancedGlobal.Candidate target degree data wall :=
  (shiftProfileFirst profile directions largest_lt).growCandidate

/-- Figure 29's `M⁽⁶⁾`: the `second` survivor's direction grows to `k₃ + 1`. -/
noncomputable def secondGrowCandidate
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    BalancedGlobal.Candidate target degree data wall :=
  (shiftProfileSecond profile directions largest_lt).growCandidate

/-- **The three Figure 29 grow members of the actual `w3Shift` source profile
are valid, preserve the source genus, and carry the displayed new-edge
indices `k₄ + 1`, `k₂ + 1` and `k₃ + 1`.**  The hypotheses are exactly the
payload of `W3IncomingClassification.Classification.shift`, so this applies to
every literal trivalent-wall source input routed to Equation (3). -/
theorem grow_members_valid_genus_index
    (profile : Nd3Profile data input.distinguishedBlock)
    (directions : profile.first.1.1.1 ≠ profile.second.1.1.1)
    (largest_lt : data.sourceEdgeIndex profile.largest.1 <
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1) :
    (largestGrowCandidate profile directions largest_lt).datum.Valid ∧
      genus (largestGrowCandidate profile directions largest_lt).datum.sourceGraph =
        genus data.sourceGraph ∧
      ((largestGrowCandidate profile directions largest_lt).resolution
          profile.largest.1.1.2).newEdge.blockCard profile.largest.1.1.2 =
        data.sourceEdgeIndex profile.largest.1 + 1 ∧
      (firstGrowCandidate profile directions largest_lt).datum.Valid ∧
      genus (firstGrowCandidate profile directions largest_lt).datum.sourceGraph =
        genus data.sourceGraph ∧
      ((firstGrowCandidate profile directions largest_lt).resolution
          profile.first.1.1.2).newEdge.blockCard profile.first.1.1.2 =
        data.sourceEdgeIndex profile.first.1 + 1 ∧
      (secondGrowCandidate profile directions largest_lt).datum.Valid ∧
      genus (secondGrowCandidate profile directions largest_lt).datum.sourceGraph =
        genus data.sourceGraph ∧
      ((secondGrowCandidate profile directions largest_lt).resolution
          profile.second.1.1.2).newEdge.blockCard profile.second.1.1.2 =
        data.sourceEdgeIndex profile.second.1 + 1 :=
  ⟨(shiftProfileLargest profile directions largest_lt).growCandidate_valid,
    (shiftProfileLargest profile directions largest_lt).growCandidate_sourceGenus,
    (shiftProfileLargest profile directions largest_lt).growCandidate_newEdge_blockCard,
    (shiftProfileFirst profile directions largest_lt).growCandidate_valid,
    (shiftProfileFirst profile directions largest_lt).growCandidate_sourceGenus,
    (shiftProfileFirst profile directions largest_lt).growCandidate_newEdge_blockCard,
    (shiftProfileSecond profile directions largest_lt).growCandidate_valid,
    (shiftProfileSecond profile directions largest_lt).growCandidate_sourceGenus,
    (shiftProfileSecond profile directions largest_lt).growCandidate_newEdge_blockCard⟩

/-! ## Figure 29's shrink members need a sheet the arithmetic does not supply -/

/-- The Position II.b sheet of the source, stated on literal source classes:
a sheet of the moving survivor's class lying outside both other survivors'
classes.  Position II.b sets `A' = e_α`, `e' = A' ∩ A⁽ᵠ⁾` with
`|e'| = k_α - 1` and `A⁽ᵠ⁾ = A₀ \ {x}` for the single sheet `x` of
`A' \ A⁽ᵠ⁾`; since `e_β` and `e_γ` have their ends at `A⁽ᵠ⁾`, both avoid `x`.
So Figure 29's `k - 1` member in the moving direction exists only if the
moving class is not covered by the other two. -/
def HasShrinkSheet (shift : ShiftProfile input) : Prop :=
  ∃ sheet, (data.edgePartition shift.movingTarget).Rel shift.movingAnchor sheet ∧
    ¬(data.edgePartition shift.firstTarget).Rel shift.firstAnchor sheet ∧
    ¬(data.edgePartition shift.secondTarget).Rel shift.secondAnchor sheet

/-- **The exact content of the Position II.b requirement.**  The transferred
sheet exists precisely when the moving survivor's class is not contained in
the union of the two retained survivors' classes.  Nothing in the shift case's
arithmetic decides this; see `shift_arithmetic_does_not_force_shrinkSheet`. -/
theorem exists_shrinkSheet_iff (shift : ShiftProfile input) :
    HasShrinkSheet shift ↔
      ¬((data.edgePartition shift.movingTarget).block shift.movingAnchor ⊆
        (data.edgePartition shift.firstTarget).block shift.firstAnchor ∪
          (data.edgePartition shift.secondTarget).block shift.secondAnchor) := by
  classical
  constructor
  · rintro ⟨sheet, hMoving, hFirst, hSecond⟩ hSubset
    have hMem : sheet ∈ (data.edgePartition shift.movingTarget).block
        shift.movingAnchor :=
      ((data.edgePartition shift.movingTarget).mem_block_iff _ _).mpr hMoving
    rcases Finset.mem_union.mp (hSubset hMem) with hIn | hIn
    · exact hFirst
        (((data.edgePartition shift.firstTarget).mem_block_iff _ _).mp hIn)
    · exact hSecond
        (((data.edgePartition shift.secondTarget).mem_block_iff _ _).mp hIn)
  · intro hNotSubset
    obtain ⟨sheet, hMem, hNotMem⟩ := Finset.not_subset.mp hNotSubset
    simp only [Finset.mem_union, not_or] at hNotMem
    exact ⟨sheet,
      ((data.edgePartition shift.movingTarget).mem_block_iff _ _).mp hMem,
      fun h ↦ hNotMem.1
        (((data.edgePartition shift.firstTarget).mem_block_iff _ _).mpr h),
      fun h ↦ hNotMem.2
        (((data.edgePartition shift.secondTarget).mem_block_iff _ _).mpr h)⟩

/-- **At a fixed datum value, the shift arithmetic does not supply Position
II.b's sheet.**  Part I justifies both Position II members for every one of the
three directions by the observation that `min(k₂,k₃,k₄) ≥ 2` (case
`{w3-r1-nd3-t2-(a>k₄)}`).  At a fixed gluing-datum value that suffices for
Position II.a -- the grow members above need only `k < |A₀|`, which the case
hypothesis gives for all three directions -- but not for Position II.b.

This is the arithmetic witness.  Three classes inside a block of three sheets,
each of size two, satisfy every numerical constraint the shift case imposes:
their sizes sum to `2|A₀|`, each is at least two, and each is strictly below
`|A₀|`.  Yet every sheet of every class lies in one of the other two classes,
so no direction has a Position II.b sheet on this datum value.
`W3ShiftShrinkExistence.exists_branchGauge_shrinkSheet` shows that this is a
gauge phenomenon: on a branch-swapped copy of the same wall datum the sheet is
available on any prescribed direction, so Figure 29's family is recovered over
isomorphism classes.

Compare `W3FourSourceCandidates.exists_sheet_outside_iff_not_disjoint`, where
the `(a = k₄)` case's two smaller indices sum to exactly `|A₀|` and the
corresponding dichotomy is forced.  Here nothing forces it in either direction:
the same arithmetic also admits configurations with the sheet, so at a fixed
datum value the shrink members are neither always available nor always
absent. -/
theorem shift_arithmetic_does_not_force_shrinkSheet :
    ∃ classes : Fin 3 → Finset (Fin 3),
      (∑ index, (classes index).card) = 2 * (Finset.univ : Finset (Fin 3)).card ∧
      (∀ index, 2 ≤ (classes index).card) ∧
      (∀ index, (classes index).card < (Finset.univ : Finset (Fin 3)).card) ∧
      (∀ index sheet, sheet ∈ classes index →
        ∃ other, other ≠ index ∧ sheet ∈ classes other) := by
  refine ⟨![{0, 1}, {1, 2}, {0, 2}], ?_, ?_, ?_, ?_⟩ <;> decide

/-- The companion witness: the same arithmetic also admits configurations that
*do* carry Position II.b's sheet, so the fixed-datum statement above is a
genuine two-sided underdetermination rather than a proof that the shrink
members never exist.
Sizes `3, 2, 3` in a block of four sheets satisfy every shift-case constraint,
and the fourth sheet lies in the first class alone.  Together with
`exists_shrinkData` this is why `ShrinkData` is not a vacuous hypothesis. -/
theorem shift_arithmetic_admits_shrinkSheet :
    ∃ classes : Fin 3 → Finset (Fin 4),
      (∑ index, (classes index).card) = 2 * (Finset.univ : Finset (Fin 4)).card ∧
      (∀ index, 2 ≤ (classes index).card) ∧
      (∀ index, (classes index).card < (Finset.univ : Finset (Fin 4)).card) ∧
      ∃ sheet ∈ classes 0, sheet ∉ classes 1 ∧ sheet ∉ classes 2 := by
  refine ⟨![{1, 2, 3}, {0, 1}, {0, 1, 2}], ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## Blockwise Euler counting for a non-star resolution

Position II.b's local resolution is not a star: its new edge is strictly finer
than both endpoints, so `M11SourceGenus.candidate_sourceGenus_of_stars` does
not apply.  Its genus preservation instead uses
`M11SourceGenus.candidate_sourceGenus_of_blockwise_euler`, the blockwise
weakening of `M11SourceGenus.paste_block_euler`, together with
`SheetPartition.card_blocks_eq_sum_blockCountWithin` (in
`Infrastructure.Change`) and `LocalResolution.pasteLeft_blockCountWithin`
/ `pasteRight_blockCountWithin` / `pasteNewEdge_blockCountWithin` (in
`ResolutionAssembly`).  These are general statements about `SheetPartition`
and `LocalResolution.paste`, and they live in `Infrastructure.Change`,
`ResolutionAssembly` and `M11SourceGenus` -- `ResolutionAssembly` itself cannot
host the last two, since its import closure reaches neither
`Infrastructure.Change` nor `BalancedGlobal`, while `M11SourceGenus` reaches
both. -/

/-! ## The Position II.b local resolution -/

/-- Position II.b's local resolution: the divalent endpoint keeps the moving
survivor's own class `A' = eₐ`, the new edge is that class with one sheet
detached (`|e'| = k - 1`), and the trivalent endpoint detaches the same sheet
from the whole wall block (`|A⁽ᵠ⁾| = |A₀| - 1`).  Detaching on *both* sides is
what the source's own cycle argument in Position II.b forces, and it is what
keeps the source genus: leaving the trivalent endpoint at the whole wall block
would put two edges above `t₁` between the same pair of ends.

This is literally `ResolutionMkk.bothDetachedResolution`, whose companions
include `_left`, `_right`, `_newEdge`, `_card_blocks` and both
Riemann--Hurwitz lemmas (and, in `W3ShiftShrinkExistence`,
`bothDetached_sourceGenus_eq`); `ResolutionMkk` explains why the one-sided
`detachedResolution` does not preserve the source genus. -/
def shrinkResolution (wallPartition endpoint : SheetPartition degree)
    (transfer remainder : Fin degree) (hNe : transfer ≠ remainder)
    (hWallTogether : wallPartition.Rel transfer remainder)
    (hEndpointTogether : endpoint.Rel transfer remainder)
    (hRefines : endpoint.Refines wallPartition) : LocalResolution degree :=
  ResolutionMkk.bothDetachedResolution wallPartition endpoint transfer remainder
    hNe hWallTogether hEndpointTogether hRefines

/-- The two Position II.b endpoints join back to the wall block.  This is the
only place the source's `min(k₂,k₃,k₄) ≥ 2` is used: the moving class must
still meet the residual wall block after its transferred sheet leaves. -/
theorem shrinkResolution_contracts (wallPartition endpoint : SheetPartition degree)
    (transfer remainder : Fin degree) (hNe : transfer ≠ remainder)
    (hWallTogether : wallPartition.Rel transfer remainder)
    (hEndpointTogether : endpoint.Rel transfer remainder)
    (hRefines : endpoint.Refines wallPartition) :
    (shrinkResolution wallPartition endpoint transfer remainder hNe hWallTogether
      hEndpointTogether hRefines).ContractsTo wallPartition :=
  ResolutionMkk.bothDetachedResolution_contracts wallPartition endpoint transfer
    remainder hNe hWallTogether hEndpointTogether hRefines

/-- Erasing the detached sheet removes exactly one induced block, provided the
counted partition already makes that sheet a singleton. -/
theorem blockCountWithin_detachSheet_of_singleton
    (fine wallPartition : SheetPartition degree)
    (transfer remainder sheet : Fin degree) (hNe : transfer ≠ remainder)
    (hWallTogether : wallPartition.Rel transfer remainder)
    (hSingleton : fine.block transfer = {transfer})
    (hSheet : wallPartition.Rel transfer sheet) (hSheetNe : sheet ≠ transfer) :
    fine.blockCountWithin
        (wallPartition.detachSheet transfer remainder hNe hWallTogether) sheet + 1 =
      fine.blockCountWithin wallPartition sheet := by
  classical
  have hReprTransfer : fine.repr transfer = transfer := by
    have hMem : fine.repr transfer ∈ fine.block transfer :=
      (fine.mem_block_iff transfer (fine.repr transfer)).mpr
        (fine.rel_repr_right transfer)
    rw [hSingleton] at hMem
    simpa using hMem
  have hUnique : ∀ source, fine.repr source = transfer → source = transfer := by
    intro source hSource
    have hRel : fine.Rel transfer source := by
      show fine.repr transfer = fine.repr source
      rw [hReprTransfer, hSource]
    have hMem : source ∈ fine.block transfer :=
      (fine.mem_block_iff transfer source).mpr hRel
    rw [hSingleton] at hMem
    simpa using hMem
  have hRelDetached :
      (wallPartition.detachSheet transfer remainder hNe hWallTogether).Rel sheet
        remainder := by
    show (wallPartition.detachSheet transfer remainder hNe hWallTogether).repr sheet =
      (wallPartition.detachSheet transfer remainder hNe hWallTogether).repr remainder
    rw [wallPartition.detachSheet_repr_of_rel_of_ne transfer remainder sheet hNe
        hWallTogether hSheetNe hSheet,
      wallPartition.detachSheet_repr_of_rel_of_ne transfer remainder remainder
        hNe hWallTogether hNe.symm hWallTogether]
  have hBlock :
      (wallPartition.detachSheet transfer remainder hNe hWallTogether).block sheet =
        (wallPartition.block sheet).erase transfer := by
    rw [SheetPartition.block_eq_of_rel _ hRelDetached,
      wallPartition.detachSheet_block_remainder transfer remainder hNe hWallTogether,
      SheetPartition.block_eq_of_rel wallPartition hSheet]
  have hTransferMem : transfer ∈ wallPartition.block sheet :=
    (wallPartition.mem_block_iff sheet transfer).mpr hSheet.symm
  have hImage : ((wallPartition.block sheet).erase transfer).image fine.repr =
      ((wallPartition.block sheet).image fine.repr).erase transfer := by
    ext value
    simp only [Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨source, ⟨hSourceNe, hSourceMem⟩, rfl⟩
      exact ⟨fun hValue ↦ hSourceNe (hUnique source hValue), source, hSourceMem, rfl⟩
    · rintro ⟨hValue, source, hSource, rfl⟩
      exact ⟨source, ⟨fun hEq ↦ hValue (by rw [hEq, hReprTransfer]), hSource⟩, rfl⟩
  have hMemImage : transfer ∈ (wallPartition.block sheet).image fine.repr :=
    Finset.mem_image.mpr ⟨transfer, hTransferMem, hReprTransfer⟩
  unfold SheetPartition.blockCountWithin
  rw [hBlock, hImage, Finset.card_erase_of_mem hMemImage]
  have hPos : 0 < ((wallPartition.block sheet).image fine.repr).card :=
    Finset.card_pos.mpr ⟨transfer, hMemImage⟩
  omega

/-- Detaching one sheet leaves exactly two induced blocks in its wall block. -/
theorem detachSheet_blockCountWithin_self (wallPartition : SheetPartition degree)
    (transfer remainder sheet : Fin degree) (hNe : transfer ≠ remainder)
    (hWallTogether : wallPartition.Rel transfer remainder)
    (hSheet : wallPartition.Rel transfer sheet) :
    (wallPartition.detachSheet transfer remainder hNe hWallTogether).blockCountWithin
      wallPartition sheet = 2 := by
  classical
  have hImage : (wallPartition.block sheet).image
      (wallPartition.detachSheet transfer remainder hNe hWallTogether).repr =
        {transfer, remainder} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      have hRel : wallPartition.Rel transfer source :=
        hSheet.trans ((wallPartition.mem_block_iff sheet source).mp hSource)
      by_cases hTransfer : source = transfer
      · subst source
        left
        exact wallPartition.detachSheet_repr_single transfer remainder hNe hWallTogether
      · right
        exact wallPartition.detachSheet_repr_of_rel_of_ne transfer remainder source
          hNe hWallTogether hTransfer hRel
    · rintro (rfl | rfl)
      · exact ⟨value, (wallPartition.mem_block_iff sheet value).mpr hSheet.symm,
          wallPartition.detachSheet_repr_single _ _ hNe hWallTogether⟩
      · exact ⟨value, (wallPartition.mem_block_iff sheet value).mpr
          (hSheet.symm.trans hWallTogether),
          wallPartition.detachSheet_repr_of_rel_of_ne _ _ value hNe
            hWallTogether hNe.symm hWallTogether⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by simpa using hNe), Finset.card_singleton]

/-! ## Position II.b's member on the actual source profile -/

namespace ShiftProfile

/-- The moving direction's own induced-block count on the distinguished wall
block: the source's `A₀` splits into `eₐ` and `|A₀| - k` dangling singletons. -/
theorem movingRest_blockCountWithin (shift : ShiftProfile input) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    (data.edgePartition shift.movingTarget).blockCountWithin
          (data.vertexPartition wall) sheet +
        data.sourceEdgeIndex shift.moving.1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 + 1 := by
  have hCount := blockCountWithin_of_singletons_off_block
    (data.edgePartition shift.movingTarget) (data.vertexPartition wall)
    shift.movingTarget_refines sheet shift.movingAnchor
    (hSheet.symm.trans shift.movingAnchor_wall_rel)
    (fun other hOther hNe ↦ moving_blockCard_eq_one shift other
      (hSheet.trans hOther) hNe)
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet] at hCount
  exact hCount

end ShiftProfile

/-- All the data Position II.b needs beyond the shift profile: the source's
transferred sheet `x`, the single element of `A' \ A⁽ᵠ⁾`, together with a
second sheet of the moving class naming the residual new-edge block.  The
three `transfer_*` fields are the source's own conditions: `x` lies in `eₐ`
and, because `e_β` and `e_γ` have their ends at `A⁽ᵠ⁾ = A₀ \ {x}`, outside
both of them. -/
structure ShrinkData (shift : ShiftProfile input) where
  transfer : Fin degree
  remainder : Fin degree
  transfer_moving : (data.edgePartition shift.movingTarget).Rel
    shift.movingAnchor transfer
  transfer_not_first : ¬(data.edgePartition shift.firstTarget).Rel
    shift.firstAnchor transfer
  transfer_not_second : ¬(data.edgePartition shift.secondTarget).Rel
    shift.secondAnchor transfer
  transfer_ne_remainder : transfer ≠ remainder
  remainder_moving : (data.edgePartition shift.movingTarget).Rel transfer remainder

/-- Position II.b's data exists exactly when the source's transferred sheet
does.  The second sheet costs nothing: it is supplied by the shift case's own
`2 ≤ k`, which is where `min(k₂,k₃,k₄) ≥ 2` is actually used. -/
theorem exists_shrinkData (shift : ShiftProfile input) (hSheet : HasShrinkSheet shift) :
    Nonempty (ShrinkData shift) := by
  classical
  obtain ⟨transfer, hMoving, hFirst, hSecond⟩ := hSheet
  have hCard : 2 ≤ (data.edgePartition shift.movingTarget).blockCard transfer := by
    rw [← SheetPartition.blockCard_congr (data.edgePartition shift.movingTarget) hMoving]
    exact shift.two_le_moving
  have hMemSelf : transfer ∈ (data.edgePartition shift.movingTarget).block transfer :=
    (data.edgePartition shift.movingTarget).self_mem_block transfer
  have hCardBlock : 2 ≤ ((data.edgePartition shift.movingTarget).block transfer).card :=
    hCard
  have hErase : 0 <
      (((data.edgePartition shift.movingTarget).block transfer).erase transfer).card := by
    rw [Finset.card_erase_of_mem hMemSelf]
    omega
  obtain ⟨remainder, hMemErase⟩ := Finset.card_pos.mp hErase
  obtain ⟨hNe, hMem⟩ := Finset.mem_erase.mp hMemErase
  exact ⟨⟨transfer, remainder, hMoving, hFirst, hSecond, fun h ↦ hNe h.symm,
    ((data.edgePartition shift.movingTarget).mem_block_iff transfer remainder).mp hMem⟩⟩

namespace ShrinkData

variable {shift : ShiftProfile input}

/-- The transferred sheet lies in the distinguished wall block. -/
theorem transfer_wall_rel (shrink : ShrinkData shift) :
    (data.vertexPartition wall).Rel input.distinguishedBlock.1 shrink.transfer :=
  shift.movingAnchor_wall_rel.trans
    (shift.movingTarget_refines.rel shrink.transfer_moving)

theorem remainder_wall_rel (shrink : ShrinkData shift) :
    (data.vertexPartition wall).Rel shrink.transfer shrink.remainder :=
  shift.movingTarget_refines.rel shrink.remainder_moving

/-- Position II.b's local resolution on the distinguished wall block. -/
noncomputable def selected (shrink : ShrinkData shift) : LocalResolution degree :=
  shrinkResolution (data.vertexPartition wall)
    (data.edgePartition shift.movingTarget) shrink.transfer shrink.remainder
    shrink.transfer_ne_remainder shrink.remainder_wall_rel shrink.remainder_moving
    shift.movingTarget_refines

theorem selected_contracts (shrink : ShrinkData shift) :
    shrink.selected.ContractsTo (data.vertexPartition wall) :=
  shrinkResolution_contracts _ _ _ _ _ _ _ _

/-- The trivalent endpoint of Position II.b. -/
theorem selected_right (shrink : ShrinkData shift) :
    shrink.selected.right =
      (data.vertexPartition wall).detachSheet shrink.transfer shrink.remainder
        shrink.transfer_ne_remainder shrink.remainder_wall_rel := rfl

/-- The divalent endpoint of Position II.b is the moving direction's own
edge partition: `A' = eₐ`, unchanged. -/
theorem selected_left (shrink : ShrinkData shift) :
    shrink.selected.left = data.edgePartition shift.movingTarget := rfl

theorem selected_newEdge (shrink : ShrinkData shift) :
    shrink.selected.newEdge =
      (data.edgePartition shift.movingTarget).detachSheet shrink.transfer
        shrink.remainder shrink.transfer_ne_remainder shrink.remainder_moving := rfl

/-- The displayed Figure 29 index: `|e'| = k - 1`. -/
theorem newEdge_blockCard_remainder (shrink : ShrinkData shift) :
    shrink.selected.newEdge.blockCard shrink.remainder + 1 =
      data.sourceEdgeIndex shift.moving.1 := by
  have hCard : (data.edgePartition shift.movingTarget).blockCard shrink.transfer =
      data.sourceEdgeIndex shift.moving.1 := by
    rw [← SheetPartition.blockCard_congr (data.edgePartition shift.movingTarget)
      shrink.transfer_moving]
    rfl
  have hDetach := (data.edgePartition shift.movingTarget).detachSheet_blockCard_remainder
    shrink.transfer shrink.remainder shrink.transfer_ne_remainder shrink.remainder_moving
  have hTwo : 2 ≤ (data.edgePartition shift.movingTarget).blockCard shrink.transfer := by
    rw [hCard]; exact shift.two_le_moving
  rw [selected_newEdge, hDetach, hCard] at *
  omega

/-- Off the residual new-edge block every class inside `A₀` is a singleton:
the transferred sheet itself, and the dangling classes of the moving
direction. -/
theorem newEdge_blockCard_of_not_rel (shrink : ShrinkData shift) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : ¬shrink.selected.newEdge.Rel shrink.remainder sheet) :
    shrink.selected.newEdge.blockCard sheet = 1 := by
  by_cases hTransfer : sheet = shrink.transfer
  · subst sheet
    rw [selected_newEdge]
    exact (data.edgePartition shift.movingTarget).detachSheet_blockCard_single
      shrink.transfer shrink.remainder shrink.transfer_ne_remainder
      shrink.remainder_moving
  · have hNotMoving : ¬(data.edgePartition shift.movingTarget).Rel shrink.transfer sheet := by
      intro hRel
      apply hNe
      rw [selected_newEdge]
      show ((data.edgePartition shift.movingTarget).detachSheet shrink.transfer
          shrink.remainder shrink.transfer_ne_remainder shrink.remainder_moving).repr
            shrink.remainder = _
      rw [(data.edgePartition shift.movingTarget).detachSheet_repr_of_rel_of_ne
          shrink.transfer shrink.remainder shrink.remainder
          shrink.transfer_ne_remainder shrink.remainder_moving
          shrink.transfer_ne_remainder.symm shrink.remainder_moving,
        (data.edgePartition shift.movingTarget).detachSheet_repr_of_rel_of_ne
          shrink.transfer shrink.remainder sheet shrink.transfer_ne_remainder
          shrink.remainder_moving hTransfer hRel]
    have hNotAnchor : ¬(data.edgePartition shift.movingTarget).Rel
        shift.movingAnchor sheet := fun hRel ↦
      hNotMoving (shrink.transfer_moving.symm.trans hRel)
    rw [selected_newEdge,
      (data.edgePartition shift.movingTarget).detachSheet_blockCard_of_not_rel
        shrink.transfer shrink.remainder sheet shrink.transfer_ne_remainder
        shrink.remainder_moving hNotMoving]
    exact moving_blockCard_eq_one shift sheet hSheet hNotAnchor

/-- The new edge's exact induced-block count on `A₀`: one residual block of
size `k - 1`, the transferred singleton, and `|A₀| - k` dangling singletons. -/
theorem newEdge_blockCountWithin (shrink : ShrinkData shift) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet) :
    shrink.selected.newEdge.blockCountWithin (data.vertexPartition wall) sheet +
        shrink.selected.newEdge.blockCard shrink.remainder =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 + 1 := by
  have hRefines : shrink.selected.newEdge.Refines (data.vertexPartition wall) :=
    shrink.selected.edge_refines_left.trans
      (shrink.selected_contracts).left_refines
  have hCount := blockCountWithin_of_singletons_off_block shrink.selected.newEdge
    (data.vertexPartition wall) hRefines sheet shrink.remainder
    (hSheet.symm.trans (shrink.transfer_wall_rel.trans shrink.remainder_wall_rel))
    (fun other hOther hNe ↦ shrink.newEdge_blockCard_of_not_rel other
      (hSheet.trans hOther) hNe)
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hSheet] at hCount
  exact hCount

end ShrinkData

/-- Every sheet of the residual wall block is related to the chosen residual
representative. -/
theorem detachSheet_rel_remainder (wallPartition : SheetPartition degree)
    (transfer remainder sheet : Fin degree) (hNe : transfer ≠ remainder)
    (hWallTogether : wallPartition.Rel transfer remainder)
    (hSheet : wallPartition.Rel transfer sheet) (hSheetNe : sheet ≠ transfer) :
    (wallPartition.detachSheet transfer remainder hNe hWallTogether).Rel sheet
      remainder := by
  show (wallPartition.detachSheet transfer remainder hNe hWallTogether).repr sheet =
    (wallPartition.detachSheet transfer remainder hNe hWallTogether).repr remainder
  rw [wallPartition.detachSheet_repr_of_rel_of_ne transfer remainder sheet hNe
      hWallTogether hSheetNe hSheet,
    wallPartition.detachSheet_repr_of_rel_of_ne transfer remainder remainder hNe
      hWallTogether hNe.symm hWallTogether]

namespace ShrinkData

variable {shift : ShiftProfile input}

/-- The transferred sheet is a singleton of the new edge. -/
theorem newEdge_block_transfer (shrink : ShrinkData shift) :
    shrink.selected.newEdge.block shrink.transfer = {shrink.transfer} :=
  (data.edgePartition shift.movingTarget).detachSheet_block_single shrink.transfer
    shrink.remainder shrink.transfer_ne_remainder shrink.remainder_moving

/-- The transferred sheet is a singleton of the first retained direction: this
is the source's condition that `e_β` has its end at `A⁽ᵠ⁾ = A₀ \ {x}`. -/
theorem firstTarget_block_transfer (shrink : ShrinkData shift) :
    (data.edgePartition shift.firstTarget).block shrink.transfer = {shrink.transfer} :=
  SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
    (firstRest_blockCard_eq_one shift shrink.transfer shrink.transfer_wall_rel
      shrink.transfer_not_first)

/-- The same for the second retained direction. -/
theorem secondTarget_block_transfer (shrink : ShrinkData shift) :
    (data.edgePartition shift.secondTarget).block shrink.transfer = {shrink.transfer} :=
  SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
    (secondRest_blockCard_eq_one shift shrink.transfer shrink.transfer_wall_rel
      shrink.transfer_not_second)

/-- The trivalent endpoint's class is the source's `A⁽ᵠ⁾`, of size `|A₀| - 1`. -/
theorem right_blockCard (shrink : ShrinkData shift) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : sheet ≠ shrink.transfer) :
    shrink.selected.right.blockCard sheet + 1 =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 := by
  have hTransferSheet : (data.vertexPartition wall).Rel shrink.transfer sheet :=
    shrink.transfer_wall_rel.symm.trans hSheet
  have hRel := detachSheet_rel_remainder (data.vertexPartition wall) shrink.transfer
    shrink.remainder sheet shrink.transfer_ne_remainder shrink.remainder_wall_rel
    hTransferSheet hNe
  have hCongr : shrink.selected.right.blockCard sheet =
      shrink.selected.right.blockCard shrink.remainder :=
    SheetPartition.blockCard_congr shrink.selected.right hRel
  have hDetach := (data.vertexPartition wall).detachSheet_blockCard_remainder
    shrink.transfer shrink.remainder shrink.transfer_ne_remainder
    shrink.remainder_wall_rel
  have hBlockCard : (data.vertexPartition wall).blockCard shrink.transfer =
      (data.vertexPartition wall).blockCard input.distinguishedBlock.1 :=
    (SheetPartition.blockCard_congr (data.vertexPartition wall)
      shrink.transfer_wall_rel).symm
  have hTwo : 2 ≤ (data.vertexPartition wall).blockCard shrink.transfer := by
    rw [hBlockCard]
    have := shift.two_le_moving
    have := shift.moving_lt
    omega
  rw [hCongr, selected_right, hDetach, hBlockCard] at *
  omega

/-- The three exact induced-block counts at the trivalent endpoint of
Position II.b, on the residual class `A⁽ᵠ⁾`. -/
theorem right_counts_of_ne (shrink : ShrinkData shift) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel input.distinguishedBlock.1 sheet)
    (hNe : sheet ≠ shrink.transfer) :
    shrink.selected.newEdge.blockCountWithin shrink.selected.right sheet +
        (data.edgePartition shift.firstTarget).blockCountWithin
          shrink.selected.right sheet +
        (data.edgePartition shift.secondTarget).blockCountWithin
          shrink.selected.right sheet ≥
      shrink.selected.right.blockCard sheet + 2 := by
  have hTransferSheet : (data.vertexPartition wall).Rel shrink.transfer sheet :=
    shrink.transfer_wall_rel.symm.trans hSheet
  have hNew := blockCountWithin_detachSheet_of_singleton shrink.selected.newEdge
    (data.vertexPartition wall) shrink.transfer shrink.remainder sheet
    shrink.transfer_ne_remainder shrink.remainder_wall_rel
    shrink.newEdge_block_transfer hTransferSheet hNe
  have hFirst := blockCountWithin_detachSheet_of_singleton
    (data.edgePartition shift.firstTarget) (data.vertexPartition wall)
    shrink.transfer shrink.remainder sheet shrink.transfer_ne_remainder
    shrink.remainder_wall_rel shrink.firstTarget_block_transfer hTransferSheet hNe
  have hSecond := blockCountWithin_detachSheet_of_singleton
    (data.edgePartition shift.secondTarget) (data.vertexPartition wall)
    shrink.transfer shrink.remainder sheet shrink.transfer_ne_remainder
    shrink.remainder_wall_rel shrink.secondTarget_block_transfer hTransferSheet hNe
  have hNewWall := shrink.newEdge_blockCountWithin sheet hSheet
  have hIndex := shrink.newEdge_blockCard_remainder
  have hFirstWall := shift.firstRest_blockCountWithin sheet hSheet
  have hSecondWall := shift.secondRest_blockCountWithin sheet hSheet
  have hCard := shrink.right_blockCard sheet hSheet hNe
  have hSum := shift.index_sum
  rw [selected_right] at *
  omega

/-- The transferred sheet is its own class at every one of the three
directions, so its Riemann--Hurwitz count is the trivial `1 + 1 + 1`. -/
theorem right_counts_of_transfer (shrink : ShrinkData shift) :
    shrink.selected.newEdge.blockCountWithin shrink.selected.right shrink.transfer +
        (data.edgePartition shift.firstTarget).blockCountWithin
          shrink.selected.right shrink.transfer +
        (data.edgePartition shift.secondTarget).blockCountWithin
          shrink.selected.right shrink.transfer ≥
      shrink.selected.right.blockCard shrink.transfer + 2 := by
  have hBlock : shrink.selected.right.block shrink.transfer = {shrink.transfer} :=
    (data.vertexPartition wall).detachSheet_block_single shrink.transfer
      shrink.remainder shrink.transfer_ne_remainder shrink.remainder_wall_rel
  have hNew := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
    shrink.selected.newEdge shrink.selected.right shrink.transfer hBlock
  have hFirst := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
    (data.edgePartition shift.firstTarget) shrink.selected.right shrink.transfer hBlock
  have hSecond := SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton
    (data.edgePartition shift.secondTarget) shrink.selected.right shrink.transfer hBlock
  have hCard : shrink.selected.right.blockCard shrink.transfer = 1 := by
    unfold SheetPartition.blockCard
    rw [hBlock, Finset.card_singleton]
  omega

/-- Figure 29's shrink member: the moving direction keeps its own class at the
new divalent endpoint, the new edge loses the transferred sheet, and the
trivalent endpoint keeps `A₀` minus that sheet. -/
noncomputable def shrinkPattern (shrink : ShrinkData shift) :
    TrivalentPattern (data := data) (wall := wall) shift.movingAnchor
      shrink.selected := by
  refine {
    background := shift.background
    leftExternal := shift.movingTarget
    rightExternalFirst := shift.orientation.rightFirst
    rightExternalSecond := shift.orientation.rightSecond
    leftEdges := rfl
    rightEdges := rfl
    exterior := ?_
    rightCounts := ?_ }
  · intro edge hIncident
    have hAt : edge ∈ GluingDatum.incidentEdges wall := by
      simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ,
        true_and] using hIncident
    by_cases hEq : edge = shift.movingTarget
    · subst edge
      change (data.edgePartition shift.movingTarget).Refines
        (if rightOf shift.movingTarget shift.movingTarget then shrink.selected.right
          else shrink.selected.left)
      simp only [rightOf, ne_eq, not_true_eq_false, decide_false]
      exact SheetPartition.Refines.refl _
    · have hRight : rightOf shift.movingTarget edge = true := by
        simp [rightOf, hEq]
      change (data.edgePartition edge).Refines
        (if rightOf shift.movingTarget edge then shrink.selected.right
          else shrink.selected.left)
      rw [hRight, if_pos rfl, selected_right]
      have hSingleton : (data.edgePartition edge).block shrink.transfer =
          {shrink.transfer} := by
        rw [shift.incidentEdges_eq] at hAt
        simp only [Finset.mem_insert, Finset.mem_singleton] at hAt
        rcases hAt with hMoving | hFirst | hSecond
        · exact (hEq hMoving).elim
        · rw [hFirst]
          exact shrink.firstTarget_block_transfer
        · rw [hSecond]
          exact shrink.secondTarget_block_transfer
      exact SheetPartition.refines_detachSheet_of_block_singleton _
        (data.vertexPartition wall) shrink.transfer shrink.remainder
        shrink.transfer_ne_remainder shrink.remainder_wall_rel
        (refines_of_mem_incidentEdges data hAt) hSingleton
  · intro anchor hAnchor sheet hSheet
    have hDistSheet : (data.vertexPartition wall).Rel
        input.distinguishedBlock.1 sheet :=
      shift.movingAnchor_wall_rel.trans hAnchor |>.trans hSheet
    by_cases hTransfer : sheet = shrink.transfer
    · subst sheet
      exact shrink.right_counts_of_transfer
    · exact shrink.right_counts_of_ne sheet hDistSheet hTransfer

/-- The actual globally assembled Figure 29 shrink member. -/
noncomputable def shrinkCandidate (shrink : ShrinkData shift) :
    BalancedGlobal.Candidate target degree data wall :=
  shrink.shrinkPattern.candidate shrink.selected_contracts

/-- The source-derived shrink member is valid whenever the incoming datum is. -/
theorem shrinkCandidate_valid (shrink : ShrinkData shift) :
    shrink.shrinkCandidate.datum.Valid :=
  shrink.shrinkCandidate.datum_valid input.valid

/-- The shrink member preserves the complete quotient-source genus.  Its
selected block is **not** a star -- the new edge is strictly finer than both
endpoints -- so this goes through the blockwise Euler identity rather than
`M11SourceGenus.candidate_sourceGenus_of_stars`.  The two detachments cancel:
the new edge gains one block over the divalent endpoint and the trivalent
endpoint gains one over the wall. -/
theorem shrinkCandidate_sourceGenus (shrink : ShrinkData shift) :
    genus shrink.shrinkCandidate.datum.sourceGraph = genus data.sourceGraph := by
  apply candidate_sourceGenus_of_blockwise_euler
  intro anchor _
  have hResolution : shrink.shrinkCandidate.resolution anchor =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        shrink.selected
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
        anchor := rfl
  rw [hResolution]
  by_cases hSelected : (data.vertexPartition wall).Rel shift.movingAnchor anchor
  · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hSelected]
    have hDist : (data.vertexPartition wall).Rel input.distinguishedBlock.1 anchor :=
      shift.movingAnchor_wall_rel.trans hSelected
    have hNewWall := shrink.newEdge_blockCountWithin anchor hDist
    have hIndex := shrink.newEdge_blockCard_remainder
    have hLeftWall := shift.movingRest_blockCountWithin anchor hDist
    have hRightWall : shrink.selected.right.blockCountWithin
        (data.vertexPartition wall) anchor = 2 := by
      rw [selected_right]
      exact detachSheet_blockCountWithin_self (data.vertexPartition wall)
        shrink.transfer shrink.remainder anchor shrink.transfer_ne_remainder
        shrink.remainder_wall_rel (shrink.transfer_wall_rel.symm.trans hDist)
    rw [shrink.selected_left]
    omega
  · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSelected]
    show (data.edgePartition shift.movingTarget).blockCountWithin
          (data.vertexPartition wall) anchor + 1 =
        (data.edgePartition shift.movingTarget).blockCountWithin
          (data.vertexPartition wall) anchor +
          (data.vertexPartition wall).blockCountWithin
            (data.vertexPartition wall) anchor
    rw [SheetPartition.blockCountWithin_self]

/-- The displayed Figure 29 index of the shrink member: over the distinguished
wall block the new edge carries one class of cardinality `k - 1`, where `k` is
the moving survivor's actual source index. -/
theorem shrinkCandidate_newEdge_blockCard (shrink : ShrinkData shift) :
    (shrink.shrinkCandidate.resolution shift.movingAnchor).newEdge.blockCard
        shrink.remainder + 1 = data.sourceEdgeIndex shift.moving.1 := by
  have hResolution : shrink.shrinkCandidate.resolution shift.movingAnchor =
      LocalResolution.onBlock (data.vertexPartition wall) shift.movingAnchor
        shrink.selected
        (fun _ ↦ fineResolution (data.vertexPartition wall)
          (data.edgePartition shift.movingTarget) shift.movingTarget_refines)
        shift.movingAnchor := rfl
  rw [hResolution, LocalResolution.onBlock_of_rel _ _ _ _ _
    (show (data.vertexPartition wall).Rel shift.movingAnchor shift.movingAnchor
      from rfl)]
  exact shrink.newEdge_blockCard_remainder

end ShrinkData

/-- **Figure 29's actual `k-1`, `k+1` pair on one direction, conditional on
the Position II.b sheet.**  Both members are valid, preserve the source genus,
and carry the two displayed new-edge indices.  The hypothesis is named, not
assumed away: `HasShrinkSheet` is exactly the source's Position II.b
condition, and `shift_arithmetic_does_not_force_shrinkSheet` shows the shift
case's own arithmetic does not supply it at a fixed datum value
(`W3ShiftShrinkExistence` supplies it on a branch-swapped copy). -/
theorem shift_pair_valid_genus_index (shift : ShiftProfile input)
    (shrink : ShrinkData shift) :
    shrink.shrinkCandidate.datum.Valid ∧
      genus shrink.shrinkCandidate.datum.sourceGraph = genus data.sourceGraph ∧
      (shrink.shrinkCandidate.resolution shift.movingAnchor).newEdge.blockCard
          shrink.remainder + 1 = data.sourceEdgeIndex shift.moving.1 ∧
      shift.growCandidate.datum.Valid ∧
      genus shift.growCandidate.datum.sourceGraph = genus data.sourceGraph ∧
      (shift.growCandidate.resolution shift.movingAnchor).newEdge.blockCard
          shift.movingAnchor = data.sourceEdgeIndex shift.moving.1 + 1 :=
  ⟨shrink.shrinkCandidate_valid, shrink.shrinkCandidate_sourceGenus,
    shrink.shrinkCandidate_newEdge_blockCard, shift.growCandidate_valid,
    shift.growCandidate_sourceGenus, shift.growCandidate_newEdge_blockCard⟩

/-- Existence form of the previous theorem: Position II.b's sheet is the only
thing standing between the shift profile and Figure 29's actual two-member
family in the moving direction. -/
theorem exists_shift_pair_of_shrinkSheet (shift : ShiftProfile input)
    (hSheet : HasShrinkSheet shift) :
    ∃ (minusCandidate : BalancedGlobal.Candidate target degree data wall)
      (remainder : Fin degree),
      minusCandidate.datum.Valid ∧
      genus minusCandidate.datum.sourceGraph = genus data.sourceGraph ∧
      (minusCandidate.resolution shift.movingAnchor).newEdge.blockCard remainder + 1 =
        data.sourceEdgeIndex shift.moving.1 ∧
      shift.growCandidate.datum.Valid ∧
      genus shift.growCandidate.datum.sourceGraph = genus data.sourceGraph ∧
      (shift.growCandidate.resolution shift.movingAnchor).newEdge.blockCard
          shift.movingAnchor = data.sourceEdgeIndex shift.moving.1 + 1 := by
  obtain ⟨shrink⟩ := exists_shrinkData shift hSheet
  exact ⟨shrink.shrinkCandidate, shrink.remainder,
    shift_pair_valid_genus_index shift shrink⟩

end DraismaVargas.LocalCases.W3ShiftSourceCandidates
