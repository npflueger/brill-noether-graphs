import DraismaVargas.LocalCases.W2R1SourceProfile
import DraismaVargas.LocalCases.M11SourceGenus

/-!
# Source-derived two-block `w2-r1` geometry (Figures 37--38, Equation (10))

Source: Draisma--Vargas Part I, Case {w2-r1}, sub-cases {w2-r1-nd3}
(Figure 37) and {w2-r1-nd2} (Figure 38), and the proof of Equation (*) for the
case, whose display is Equation (10).  The ambient hypotheses are those of
Case {w2}, where `val(w₀) = 2`, `ch(w₀) = 2` and the constant `s` are fixed.

Case `{w2-r1}` is `r₀(A₀) = 1`, so `val(A₀) = 3`: two occurrences above one
target direction, one above the other, and `k₁ + k₂ = |A₀| = k₃`.

## Why this case has two blocks

The proof of Equation (*) in this case begins by observing that there is a
second vertex `B₀` above `w₀` with `r₀(B₀) = 1`.  Equation (10) is the sum of
**two** wall vertices' contributions, and `ch u = ch v = 1` forces
`δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)`, which is what makes `δ⁽ᵠ⁾(Ã)` determine the member.
`Pair` below is therefore two blocks from the start -- it is literally the
payload of `IncomingSourceCases.Classification.r1` -- and the coupling is
carried by `other`, so `Pair.candidates` has arity two by construction
(`Pair.positions_opposite`, `Pair.member_determined`).

Everything is derived from two actual `W2R1SourceProfile.SourceProfile`s.  No
diagram, no caller-supplied refinement and no caller-supplied count: the fine
partition on a block is *that block's own doubled direction's occurrence
partition*, `k₁`, `k₂`, `k₃` are the profile's own index fields, and
`k₁ + k₂ = |A₀| = k₃` appears here in its partition form
(`doublePartition_covers`, `singlePartition_covers`).

## The blockwise Euler count

The two constructors used are `ResolutionCoarseFine.fineResolution` (and its
`LocalResolution.reverse`) and `ResolutionM11.joinedResolutionAt`.  Counted
blockwise on an arbitrary wall block, writing `n` for the induced block count
of the direction's occurrence partition:

| shape | `left` | `right` | `newEdge` | `wall` | `newEdge + wall` | `left + right` |
|---|---|---|---|---|---|---|
| `joinedResolutionAt` | `1` | `1` | `1` | `1` | `2` | `2` |
| `sideFine 0` (`fineResolution`) | `n` | `1` | `n` | `1` | `n+1` | `n+1` |
| `sideFine 1` (its `reverse`) | `1` | `n` | `n` | `1` | `n+1` | `n+1` |

Defect `0` in all three rows: `sideFine_euler`, `joinedResolutionAt_euler`,
and `Pair.resolution_euler` for every block of every member.  The reason is
structural and is the contrast with `ResolutionMkk.detachedResolution` (which
sets `right := wall` while refining `newEdge`, and has defect `+1` for *all*
arguments by `W3ShiftShrinkExistence.detachedResolution_sourceGenus_eq_succ`):
here the refined new edge is refined **together with the endpoint it sits on**,
so both shapes are stars in the sense of
`M11SourceGenus.candidate_sourceGenus_of_stars` and the genus proof is that
lemma, not the blockwise-Euler one (`Pair.candidate_sourceGenus`).

## The two blocks share one datum, aligned or not

**They do share one gluing datum.**  The two blocks are *disjoint* sheet sets,
so no choice made on one constrains the other, and the object they share -- a
direction's occurrence partition -- is a **field of the datum**, not a choice.
Nothing is detached: every exterior condition is either `Refines` by
reflexivity or `(edgePartition e).Refines (vertexPartition wall)`, a field of
every `GluingDatum` (`Pair.exterior`, `memberLocal_refines_left`/`_right`).  So
both members exist over one `data`, both are valid
(`Pair.candidate_datum_valid`), both preserve source genus and both expand the
wall into `T₂`.

**But which direction is doubled is a per-block datum.**  Part I gives `B₀`
notation analogous to that of `A₀`, i.e. `B₀` gets *its own* `e₁, e₂, e₃`, and
nothing in the case forces `B₀` to be doubled over the same target direction
as `A₀`.  Two configurations exist:

* **aligned** (`Pair.Aligned`): each member retains one block and resolves the
  other -- `Pair.aligned_counts`, the counts summing to `1 + 2 = 3`;
* **opposite**: one member retains both and the other resolves both, on
  **opposite sides** of the new edge -- `Pair.opposite_counts`, `2` or `4`.

Equation (10) holds in both: it is proved block by block, and each block is
still retained in exactly one member and resolved in the other
(`Pair.first_newEdge_blockCountWithin`, `Pair.second_newEdge_blockCountWithin`).

## A single fine partition does not suffice

Using the single partition `data.edgePartition (star.edge 0)` on whichever
block the position selects is right exactly in the aligned configuration with
the doubled direction labelled `0`.  For a block doubled over `star.edge 1`,
it gives new-edge block count `1` at that block, where Figure 37's resolved
member needs `2` (`pair_newEdge_blockCountWithin_eq_two`).  Re-orienting the
two-star does not help: `opposite_no_common_fine_direction` shows that in the
opposite configuration *each* of the two directions leaves one of the two
blocks whole.  The needed shape is the **reversed** fine resolution
`(fineResolution wall (edgePartition (star.edge 1))).reverse`; `sideFine` is
that shape, indexed by the direction rather than by the wall.

**The distinction is not a matter of gauge.**  The invariant that separates the
two configurations is the induced block count of a direction inside a wall
block, and `doubleLabel` is *characterised* by it
(`doubleLabel_iff_blockCountWithin_eq_two`).  The moves available are the ones
Part I uses to define isomorphism of gluing datums (`definition-gd-iso` and the
discussion before it), and on that count they act as follows:

1. **tree-swap**: one permutation `π` on all relations.  Counts are
   transported along `π` -- `doubleLabel_iff_treeSwap`.  Both blocks move
   together, so the pair `(n₂(A₀), n₂(B₀))` is carried, not changed.
2. **branch-swap**: a transposition `(i j)` with `i ∼_{w₀} j`, applied above
   one component of `T ∖ {w₀}`.  It fixes every wall block setwise, so by
   `SheetPartition.relabel_blockCountWithin_fixed_of_pointwise` **every**
   direction's count on **every** wall block is unchanged --
   `doubleLabel_iff_branchSwap`.
3. **the per-element isomorphism**: a graph isomorphism `τ` of the target plus
   one `π_x` per element, class- and incidence-preserving.
   Incidence-preservation is exactly a bijection between the wall classes and
   each direction's classes respecting containment, so it preserves every
   count; `τ` can only fix or exchange the two edges at `w₀`, and `π_{w₀}` can
   only fix or exchange the two ramification-one blocks.

So the group acts on `(n₂(A₀), n₂(B₀)) ∈ {1,2}²` through at most transposing
the pair and replacing each entry `n` by `3 - n`.  The orbits are
`{(2,2), (1,1)}` and `{(2,1), (1,2)}`: **two** orbits, and alignment is the
invariant that tells them apart.  This is an enumeration of all the moves, not
a sample.

## Figure 38's indices

In Case {w2-r1-nd2} the occurrence `e₁` is dangling and the refinement
identity reads `k₃ = k₂ + 1`; Figure 38 labels the two surviving occurrences
`e₂` (above `t₂`) and `e₃` (above `t₃`), and its gluing boxes read
`|e'| = k₂ + 1` and `|e'| = k₂`.  The limit values used here are accordingly
`σ₀(J_{A₀}, 2) = c_h / k₂` and `σ₀(J_{A₀}, 3) = c_h / (k₂ + 1)`, with which the
displayed identity of the case is exactly
`σ⁽¹⁾ + σ⁽²⁾ = σ₀(J,2) + σ₀(J,3)`.  (Part I writes these two limit values
with `k₁` in place of `k₂`; since `k₁ = 1` in this sub-case, the values used
here are the ones matching the gluing boxes.)  Nothing gauge-sensitive is at
stake: both sides are cardinalities of one block's own local data.
`nd2_displayed_indices` records `k₁ = 1` and `k₃ = k₂ + 1`, taken from the
profile's own `cases` field.

## What is constructed

`Pair.candidate 0` and `Pair.candidate 1` -- Equation (10)'s two globally
coupled members as actual arbitrary-degree outgoing gluing data over **one**
datum and **both** ramification-one blocks -- with validity
(`Pair.candidate_datum_valid`), source genus (`Pair.candidate_sourceGenus`),
both new endpoint valencies (`Pair.candidate_target_valencies`, both `2`), the
Figure 37 new-edge indices (`Pair.first_retained_blockCard` `= k₃`,
`Pair.first_resolved_blockCard` `= k₁, k₂` with `k₁ + k₂ = k₃`, and the `B₀`
mirrors), the Figure 38 nd2 indices (`nd2_displayed_indices`), the induced
block counts on both blocks, the blockwise Euler identities
(`Pair.resolution_euler`) and the distinctness of the two members
(`Pair.resolution_ne_of_ne`).  `pairOfSplit` and `exists_pair_or_concentrated`
inhabit `Pair` from `SecondEquation.W2SourceInput` alone, with the
classifier's `background` field derived (`background_of_split`).

## What is not constructed here

Equation (10) on actual matrices: the length-matrix presentations, the stable
paths displaying `c(h(e))/m(e)`, the census, the incoming member and the
certified positive exit.  Those are in `W2R1LimitMatrix`, `W2R1CommonBalance`,
`W2R1IncomingMatching` and `W2R1ArbitraryIncomingExit`.
-/

namespace DraismaVargas.LocalCases.W2R1SourceCandidates

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k ResolutionCoarseFine

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## 1.  The two occurrence partitions of one ramification-one block -/

section Counts

variable {block : WallBlock data wall}

/-- The occurrence partition of the direction carrying **two** of the block's
three occurrences: `e₁`, `e₂` of Figure 37. -/
abbrev doublePartition (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    SheetPartition degree :=
  data.edgePartition (star.edge profile.doubleLabel)

/-- The occurrence partition of the direction carrying the block's remaining
occurrence `e₃`. -/
abbrev singlePartition (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    SheetPartition degree :=
  data.edgePartition (star.edge profile.singleLabel)

/-- The canonical sheet of `e₁`. -/
def firstSheet (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    Fin degree := profile.first.1.1.2

/-- The canonical sheet of `e₂`. -/
def secondSheet (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    Fin degree := profile.second.1.1.2

/-- The canonical sheet of `e₃`. -/
def thirdSheet (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    Fin degree := profile.third.1.1.2

theorem sheet_rel_of_incident
    (edge : IncidentSourceEdge data (WallBlock.sourceVertex data wall block)) :
    (data.vertexPartition wall).Rel block.1 edge.1.1.2 := by
  have hIncident := (incident_wallBlock_sourceVertex_iff data block edge.1).mp edge.2
  exact (WallBlock.ofSheet_eq_iff_rel data wall block edge.1.1.2).mp hIncident.2

theorem firstSheet_rel (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (firstSheet profile) :=
  sheet_rel_of_incident profile.first

theorem secondSheet_rel (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (secondSheet profile) :=
  sheet_rel_of_incident profile.second

theorem thirdSheet_rel (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (data.vertexPartition wall).Rel block.1 (thirdSheet profile) :=
  sheet_rel_of_incident profile.third

theorem doublePartition_repr_first
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (doublePartition profile).repr (firstSheet profile) = firstSheet profile := by
  have h := profile.first.1.2
  rw [profile.first_target] at h
  exact h

theorem doublePartition_repr_second
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (doublePartition profile).repr (secondSheet profile) = secondSheet profile := by
  have h := profile.second.1.2
  rw [profile.second_target] at h
  exact h

theorem singlePartition_repr_third
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (singlePartition profile).repr (thirdSheet profile) = thirdSheet profile := by
  have h := profile.third.1.2
  rw [profile.third_target] at h
  exact h

/-- `|e₁| = k₁`. -/
theorem doublePartition_blockCard_first
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (doublePartition profile).blockCard (firstSheet profile) =
      data.sourceEdgeIndex profile.first.1 := by
  show (data.edgePartition (star.edge profile.doubleLabel)).blockCard profile.first.1.1.2 =
    (data.edgePartition profile.first.1.1.1).blockCard profile.first.1.1.2
  rw [profile.first_target]

/-- `|e₂| = k₂`. -/
theorem doublePartition_blockCard_second
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (doublePartition profile).blockCard (secondSheet profile) =
      data.sourceEdgeIndex profile.second.1 := by
  show (data.edgePartition (star.edge profile.doubleLabel)).blockCard profile.second.1.1.2 =
    (data.edgePartition profile.second.1.1.1).blockCard profile.second.1.1.2
  rw [profile.second_target]

/-- `|e₃| = k₃`. -/
theorem singlePartition_blockCard_third
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    (singlePartition profile).blockCard (thirdSheet profile) =
      data.sourceEdgeIndex profile.third.1 := by
  show (data.edgePartition (star.edge profile.singleLabel)).blockCard profile.third.1.1.2 =
    (data.edgePartition profile.third.1.1.1).blockCard profile.third.1.1.2
  rw [profile.third_target]

/-- `e₁` and `e₂` are distinct blocks of the doubled direction. -/
theorem doublePartition_separate
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    ¬(doublePartition profile).Rel (firstSheet profile) (secondSheet profile) := by
  intro hRel
  apply profile.first_ne_second
  have hSheet : firstSheet profile = secondSheet profile := by
    have h := hRel
    rw [SheetPartition.rel_iff, doublePartition_repr_first,
      doublePartition_repr_second] at h
    exact h
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (profile.first_target.trans profile.second_target.symm) hSheet

theorem firstSheet_ne_secondSheet
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    firstSheet profile ≠ secondSheet profile := by
  intro hEq
  apply doublePartition_separate profile
  rw [hEq]
  exact ((doublePartition profile).rel_iff _ _).mpr rfl

/-- The canonical occurrence of any sheet of the block over a named direction
is one of the block's three literal occurrences. -/
theorem exhaustive_at_label
    (profile : W2R1SourceProfile.OccurrenceProfile data star block)
    (label : Fin 2) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    data.sourceEdge (star.edge label) sheet = profile.first.1 ∨
      data.sourceEdge (star.edge label) sheet = profile.second.1 ∨
        data.sourceEdge (star.edge label) sheet = profile.third.1 := by
  have hIncident : Incident data (data.sourceEdge (star.edge label) sheet)
      (WallBlock.sourceVertex data wall block) := by
    apply (incident_wallBlock_sourceVertex_iff data block _).mpr
    refine ⟨star.edge_mem_incidentEdges label, ?_⟩
    apply (WallBlock.ofSheet_eq_iff_rel data wall block _).mpr
    exact hSheet.trans ((star.edgePartition_refines_wall data label).rel
      ((data.edgePartition (star.edge label)).rel_repr_right sheet))
  rcases profile.exhaustive ⟨_, hIncident⟩ with hEq | hEq | hEq
  · exact Or.inl (congrArg Subtype.val hEq)
  · exact Or.inr (Or.inl (congrArg Subtype.val hEq))
  · exact Or.inr (Or.inr (congrArg Subtype.val hEq))

/-- **`e₁` and `e₂` tile `A₀`.**  The refinement identity of Case `{w2-r1}`,
`k₁ + k₂ = |A₀|`, in its literal partition form. -/
theorem doublePartition_covers
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (doublePartition profile).Rel (firstSheet profile) sheet ∨
      (doublePartition profile).Rel (secondSheet profile) sheet := by
  rcases exhaustive_at_label profile profile.doubleLabel sheet hSheet with hEq | hEq | hEq
  · left
    have hValue := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEq
    change (doublePartition profile).repr sheet = firstSheet profile at hValue
    rw [SheetPartition.rel_iff, doublePartition_repr_first, hValue]
  · right
    have hValue := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEq
    change (doublePartition profile).repr sheet = secondSheet profile at hValue
    rw [SheetPartition.rel_iff, doublePartition_repr_second, hValue]
  · exact absurd ((congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hEq).trans
      profile.third_target) (star.edge_injective.ne profile.labels_ne)

/-- **`e₃` is all of `A₀`.**  The other half of `k₁ + k₂ = |A₀| = k₃`. -/
theorem singlePartition_covers
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) (sheet : Fin degree)
    (hSheet : (data.vertexPartition wall).Rel block.1 sheet) :
    (singlePartition profile).Rel (thirdSheet profile) sheet := by
  rcases exhaustive_at_label profile profile.singleLabel sheet hSheet with hEq | hEq | hEq
  · exact absurd ((congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hEq).trans
      profile.first_target) (star.edge_injective.ne profile.labels_ne.symm)
  · exact absurd ((congrArg (fun edge : data.SourceEdge ↦ edge.1.1) hEq).trans
      profile.second_target) (star.edge_injective.ne profile.labels_ne.symm)
  · have hValue := congrArg (fun edge : data.SourceEdge ↦ edge.1.2) hEq
    change (singlePartition profile).repr sheet = thirdSheet profile at hValue
    rw [SheetPartition.rel_iff, singlePartition_repr_third, hValue]


/-! ### The two induced block counts on `A₀`

`k₁ + k₂ = |A₀| = k₃` is a *partition* statement here, not an arithmetic one:
the doubled direction cuts `A₀` into exactly two blocks and the single
direction leaves it whole. -/

/-- **The single direction is indiscrete on `A₀`.**  `|e₃| = |A₀|`. -/
theorem singlePartition_blockCountWithin
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (singlePartition profile).blockCountWithin (data.vertexPartition wall) anchor = 1 := by
  classical
  have hImage : ((data.vertexPartition wall).block anchor).image
      (singlePartition profile).repr = {thirdSheet profile} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_singleton, SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      have hRel := singlePartition_covers profile source (hAnchor.trans hSource)
      rw [SheetPartition.rel_iff, singlePartition_repr_third] at hRel
      exact hRel.symm
    · rintro rfl
      exact ⟨thirdSheet profile, hAnchor.symm.trans (thirdSheet_rel profile),
        singlePartition_repr_third profile⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_singleton]

/-- **The doubled direction cuts `A₀` in exactly two.**  `|e'| = k₁`,
`|e''| = k₂` of Figure 37's second member. -/
theorem doublePartition_blockCountWithin
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (doublePartition profile).blockCountWithin (data.vertexPartition wall) anchor = 2 := by
  classical
  have hImage : ((data.vertexPartition wall).block anchor).image
      (doublePartition profile).repr = {firstSheet profile, secondSheet profile} := by
    ext value
    simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
      SheetPartition.mem_block_iff]
    constructor
    · rintro ⟨source, hSource, rfl⟩
      rcases doublePartition_covers profile source (hAnchor.trans hSource) with h | h
      · exact Or.inl (by rw [← doublePartition_repr_first profile, h])
      · exact Or.inr (by rw [← doublePartition_repr_second profile, h])
    · rintro (rfl | rfl)
      · exact ⟨firstSheet profile, hAnchor.symm.trans (firstSheet_rel profile),
          doublePartition_repr_first profile⟩
      · exact ⟨secondSheet profile, hAnchor.symm.trans (secondSheet_rel profile),
          doublePartition_repr_second profile⟩
  unfold SheetPartition.blockCountWithin
  rw [hImage, Finset.card_insert_of_notMem (by
    simpa using firstSheet_ne_secondSheet profile), Finset.card_singleton]

/-- A divalent wall has only two directions, so the complement of the doubled
one is the single one. -/
theorem eq_singleLabel_of_ne_doubleLabel
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) {label : Fin 2}
    (hLabel : label ≠ profile.doubleLabel) : label = profile.singleLabel := by
  have hNe := profile.labels_ne
  omega

/-- **The direction a block is not doubled over sees the block whole.**  This
is the exact obstruction behind the failure of a single fine partition (see the
module docstring): a fine partition taken from the wrong direction does not
resolve this block at all. -/
theorem blockCountWithin_eq_one_of_ne_doubleLabel
    (profile : W2R1SourceProfile.OccurrenceProfile data star block) {label : Fin 2}
    (hLabel : label ≠ profile.doubleLabel) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (data.edgePartition (star.edge label)).blockCountWithin
      (data.vertexPartition wall) anchor = 1 := by
  rw [eq_singleLabel_of_ne_doubleLabel profile hLabel]
  exact singlePartition_blockCountWithin profile anchor hAnchor

/-- `k₁ + k₂ = |A₀| = k₃`, the refinement identity of Case `{w2-r1}`,
read off the profile's own index fields. -/
theorem index_identity (profile : W2R1SourceProfile.OccurrenceProfile data star block) :
    data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 =
        (data.vertexPartition wall).blockCard block.1 ∧
      data.sourceEdgeIndex profile.third.1 =
        (data.vertexPartition wall).blockCard block.1 :=
  ⟨profile.pair_index, profile.single_index⟩

end Counts


/-! ## 2.  The two local shapes of Figure 37, one per direction

Figure 37's two members are read off the position of `Ã`.  With the old edge
`star.edge 0` retained at `u` and `star.edge 1` moved to the fresh `v`:

* `δ⁽ᵠ⁾(Ã)` is the endpoint carrying the block's **doubled** direction: then
  `Ã` already has two old occurrences, so `r⁽ᵠ⁾(Ã) = 1` leaves it a single new
  edge and the whole block is retained everywhere -- `joinedResolutionAt`,
  `|e'| = k₃`;
* `δ⁽ᵠ⁾(Ã)` is the other endpoint: then `Ã` has one old occurrence and two new
  edges, whose blocks are `e₁`, `e₂` -- `sideFine`, `|e'| = k₁`, `|e''| = k₂`.

`sideFine` takes the *direction* as its argument, because which endpoint
carries the fine partition is decided by the block, not by the wall. -/

section Shapes

/-- Equality of local resolutions is equality of their three partitions. -/
theorem localResolution_eq {d : ℕ} {first second : LocalResolution d}
    (hLeft : first.left = second.left) (hRight : first.right = second.right)
    (hNew : first.newEdge = second.newEdge) : first = second := by
  cases first
  cases second
  simp only at hLeft hRight hNew
  subst hLeft
  subst hRight
  subst hNew
  rfl

/-- Figure 37's fine member on the block, **oriented by the direction it
resolves**: the named direction's occurrence partition sits on the new edge
and on the endpoint carrying that direction, the other endpoint keeps the
whole wall block. -/
noncomputable def sideFine (data : GluingDatum target degree)
    (star : TwoStar target wall) (label : Fin 2) : LocalResolution degree :=
  if label = 0 then
    fineResolution (data.vertexPartition wall) (data.edgePartition (star.edge label))
      (star.edgePartition_refines_wall data label)
  else
    (fineResolution (data.vertexPartition wall) (data.edgePartition (star.edge label))
      (star.edgePartition_refines_wall data label)).reverse

variable (data star)

@[simp] theorem sideFine_newEdge (label : Fin 2) :
    (sideFine data star label).newEdge = data.edgePartition (star.edge label) := by
  unfold sideFine
  split <;> rfl

theorem sideFine_left_of_zero {label : Fin 2} (hLabel : label = 0) :
    (sideFine data star label).left = data.edgePartition (star.edge label) := by
  rw [sideFine, if_pos hLabel]
  rfl

theorem sideFine_right_of_zero {label : Fin 2} (hLabel : label = 0) :
    (sideFine data star label).right = data.vertexPartition wall := by
  rw [sideFine, if_pos hLabel]
  rfl

theorem sideFine_left_of_ne_zero {label : Fin 2} (hLabel : label ≠ 0) :
    (sideFine data star label).left = data.vertexPartition wall := by
  rw [sideFine, if_neg hLabel]
  rfl

theorem sideFine_right_of_ne_zero {label : Fin 2} (hLabel : label ≠ 0) :
    (sideFine data star label).right = data.edgePartition (star.edge label) := by
  rw [sideFine, if_neg hLabel]
  rfl

theorem sideFine_contracts (label : Fin 2) :
    (sideFine data star label).ContractsTo (data.vertexPartition wall) := by
  unfold sideFine
  split
  · exact fineResolution_contracts _ _ _
  · exact LocalResolution.reverse_contracts (fineResolution_contracts _ _ _)

/-- Both shapes are stars in the sense of `M11SourceGenus`: one endpoint is
the whole wall block and the new edge equals the other endpoint. -/
theorem sideFine_star (label : Fin 2) :
    ((sideFine data star label).left = data.vertexPartition wall ∧
        (sideFine data star label).newEdge = (sideFine data star label).right) ∨
      ((sideFine data star label).right = data.vertexPartition wall ∧
        (sideFine data star label).newEdge = (sideFine data star label).left) := by
  by_cases hLabel : label = 0
  · exact Or.inr ⟨sideFine_right_of_zero data star hLabel,
      (sideFine_newEdge data star label).trans
        (sideFine_left_of_zero data star hLabel).symm⟩
  · exact Or.inl ⟨sideFine_left_of_ne_zero data star hLabel,
      (sideFine_newEdge data star label).trans
        (sideFine_right_of_ne_zero data star hLabel).symm⟩

theorem joinedResolutionAt_star :
    ((joinedResolutionAt (data.vertexPartition wall)).left = data.vertexPartition wall ∧
        (joinedResolutionAt (data.vertexPartition wall)).newEdge =
          (joinedResolutionAt (data.vertexPartition wall)).right) ∨
      ((joinedResolutionAt (data.vertexPartition wall)).right = data.vertexPartition wall ∧
        (joinedResolutionAt (data.vertexPartition wall)).newEdge =
          (joinedResolutionAt (data.vertexPartition wall)).left) :=
  Or.inl ⟨rfl, rfl⟩

/-- The retained old occurrence is compatible with the retained endpoint, in
both shapes and with no extra premise: either that endpoint *is* the fine
partition, or it is the whole wall partition. -/
theorem sideFine_refines_left (label : Fin 2) :
    (data.edgePartition (star.edge 0)).Refines (sideFine data star label).left := by
  by_cases hLabel : label = 0
  · rw [sideFine_left_of_zero data star hLabel, hLabel]
    exact SheetPartition.Refines.refl _
  · rw [sideFine_left_of_ne_zero data star hLabel]
    exact star.edgePartition_refines_wall data 0

theorem sideFine_refines_right (label : Fin 2) :
    (data.edgePartition (star.edge 1)).Refines (sideFine data star label).right := by
  by_cases hLabel : label = 0
  · rw [sideFine_right_of_zero data star hLabel]
    exact star.edgePartition_refines_wall data 1
  · have hOne : label = 1 := by omega
    rw [sideFine_right_of_ne_zero data star hLabel, hOne]
    exact SheetPartition.Refines.refl _

/-- **The blockwise Euler count for `sideFine`: defect zero.**  The new edge and
the wall contribute `n + 1` induced blocks on any wall block, and so do the
two endpoints: the fine side contributes `n`, the retained side `1`. -/
theorem sideFine_euler (label : Fin 2) (anchor : Fin degree) :
    (sideFine data star label).newEdge.blockCountWithin
          (data.vertexPartition wall) anchor + 1 =
      (sideFine data star label).left.blockCountWithin
          (data.vertexPartition wall) anchor +
        (sideFine data star label).right.blockCountWithin
          (data.vertexPartition wall) anchor := by
  by_cases hLabel : label = 0
  · rw [sideFine_newEdge, sideFine_left_of_zero data star hLabel,
      sideFine_right_of_zero data star hLabel,
      SheetPartition.blockCountWithin_self]
  · rw [sideFine_newEdge, sideFine_left_of_ne_zero data star hLabel,
      sideFine_right_of_ne_zero data star hLabel,
      SheetPartition.blockCountWithin_self, Nat.add_comm]

/-- **The blockwise Euler count for the retained shape: defect zero.**  `1 + 1 = 1 + 1`. -/
theorem joinedResolutionAt_euler (anchor : Fin degree) :
    (joinedResolutionAt (data.vertexPartition wall)).newEdge.blockCountWithin
          (data.vertexPartition wall) anchor + 1 =
      (joinedResolutionAt (data.vertexPartition wall)).left.blockCountWithin
          (data.vertexPartition wall) anchor +
        (joinedResolutionAt (data.vertexPartition wall)).right.blockCountWithin
          (data.vertexPartition wall) anchor := by
  simp only [joinedResolutionAt, SheetPartition.blockCountWithin_self]

/-- Figure 37's member selector for **one** block: the block whose doubled
direction is `double` is left whole when `Ã` sits at that direction's
endpoint (`position = double`), and is resolved otherwise. -/
noncomputable def memberLocal (data : GluingDatum target degree)
    (star : TwoStar target wall) (double position : Fin 2) : LocalResolution degree :=
  if position = double then joinedResolutionAt (data.vertexPartition wall)
  else sideFine data star double

theorem memberLocal_of_eq {double position : Fin 2} (hPosition : position = double) :
    memberLocal data star double position = joinedResolutionAt (data.vertexPartition wall) := by
  rw [memberLocal, if_pos hPosition]

theorem memberLocal_of_ne {double position : Fin 2} (hPosition : position ≠ double) :
    memberLocal data star double position = sideFine data star double := by
  rw [memberLocal, if_neg hPosition]

theorem memberLocal_contracts (double position : Fin 2) :
    (memberLocal data star double position).ContractsTo (data.vertexPartition wall) := by
  unfold memberLocal
  split
  · exact joinedResolutionAt_contracts _
  · exact sideFine_contracts data star double

theorem memberLocal_star (double position : Fin 2) :
    ((memberLocal data star double position).left = data.vertexPartition wall ∧
        (memberLocal data star double position).newEdge =
          (memberLocal data star double position).right) ∨
      ((memberLocal data star double position).right = data.vertexPartition wall ∧
        (memberLocal data star double position).newEdge =
          (memberLocal data star double position).left) := by
  unfold memberLocal
  split
  · exact joinedResolutionAt_star data
  · exact sideFine_star data star double

theorem memberLocal_refines_left (double position : Fin 2) :
    (data.edgePartition (star.edge 0)).Refines
      (memberLocal data star double position).left := by
  unfold memberLocal
  split
  · exact star.edgePartition_refines_wall data 0
  · exact sideFine_refines_left data star double

theorem memberLocal_refines_right (double position : Fin 2) :
    (data.edgePartition (star.edge 1)).Refines
      (memberLocal data star double position).right := by
  unfold memberLocal
  split
  · exact star.edgePartition_refines_wall data 1
  · exact sideFine_refines_right data star double

theorem memberLocal_euler (double position : Fin 2) (anchor : Fin degree) :
    (memberLocal data star double position).newEdge.blockCountWithin
          (data.vertexPartition wall) anchor + 1 =
      (memberLocal data star double position).left.blockCountWithin
          (data.vertexPartition wall) anchor +
        (memberLocal data star double position).right.blockCountWithin
          (data.vertexPartition wall) anchor := by
  unfold memberLocal
  split
  · exact joinedResolutionAt_euler data anchor
  · exact sideFine_euler data star double anchor

end Shapes


/-! ## 3.  The two-block datum and its two coupled candidates

`Pair` is exactly the payload of `IncomingSourceCases.Classification.r1`: two
**distinct** wall blocks of local ramification one, each with its own actual
`W2R1SourceProfile.SourceProfile`, and a background of unramified blocks.

The coupling is the source's own, from the proof of Equation (*) in this case:
`ch u = ch v = 1` forces
`δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)`, so the two blocks always sit at opposite endpoints and
`δ⁽ᵠ⁾(Ã)` alone names the member.  It is carried by `other` below, and it is
what makes the family have arity two. -/

section Pairs

/-- The opposite endpoint. -/
def other (position : Fin 2) : Fin 2 := if position = 0 then 1 else 0

@[simp] theorem other_ne (position : Fin 2) : other position ≠ position := by
  revert position
  decide

@[simp] theorem other_other (position : Fin 2) : other (other position) = position := by
  revert position
  decide

theorem other_injective : Function.Injective other := by
  decide

/-- **The `w2-r1` source datum**: the two distinct ramification-one blocks
above a divalent wall, with their literal occurrence profiles.  This is the
payload of the classifier's `r1` constructor. -/
structure Pair (data : GluingDatum target degree) (star : TwoStar target wall) where
  /-- The block the source calls `A₀`. -/
  first : WallBlock data wall
  /-- The block the source calls `B₀`. -/
  second : WallBlock data wall
  distinct : first ≠ second
  firstProfile : W2R1SourceProfile.SourceProfile data star first
  secondProfile : W2R1SourceProfile.SourceProfile data star second
  background : ∀ block : WallBlock data wall, block ≠ first → block ≠ second →
    data.localRamification wall block = 0

namespace Pair

variable (pair : Pair data star)

/-- Distinct wall blocks are unrelated sheets. -/
theorem separate : ¬(data.vertexPartition wall).Rel pair.first.1 pair.second.1 := by
  intro hRel
  refine pair.distinct (Subtype.ext ?_)
  have hRepr : (data.vertexPartition wall).repr pair.first.1
      = (data.vertexPartition wall).repr pair.second.1 := hRel
  rwa [pair.first.2, pair.second.2] at hRepr

theorem not_rel_first_of_rel_second {anchor : Fin degree}
    (hSecond : (data.vertexPartition wall).Rel pair.second.1 anchor) :
    ¬(data.vertexPartition wall).Rel pair.first.1 anchor := by
  intro hFirst
  exact pair.separate (hFirst.trans hSecond.symm)

/-- **The blockwise resolution of Equation (10)'s member `q`.**  Each of the
two ramification-one blocks receives the Figure 37 member determined by its
own doubled direction and its own endpoint position; every other block keeps
the whole wall partition.  The two positions are opposite by construction. -/
noncomputable def resolution (position : Fin 2) (anchor : Fin degree) :
    LocalResolution degree :=
  LocalResolution.onBlock (data.vertexPartition wall) pair.first.1
    (memberLocal data star pair.firstProfile.doubleLabel position)
    (fun innerAnchor ↦ LocalResolution.onBlock (data.vertexPartition wall) pair.second.1
      (memberLocal data star pair.secondProfile.doubleLabel (other position))
      (fun _ ↦ joinedResolutionAt (data.vertexPartition wall)) innerAnchor)
    anchor

theorem resolution_of_first {anchor : Fin degree} (position : Fin 2)
    (hAnchor : (data.vertexPartition wall).Rel pair.first.1 anchor) :
    pair.resolution position anchor =
      memberLocal data star pair.firstProfile.doubleLabel position := by
  rw [resolution, LocalResolution.onBlock_of_rel _ _ _ _ _ hAnchor]

theorem resolution_of_second {anchor : Fin degree} (position : Fin 2)
    (hAnchor : (data.vertexPartition wall).Rel pair.second.1 anchor) :
    pair.resolution position anchor =
      memberLocal data star pair.secondProfile.doubleLabel (other position) := by
  rw [resolution,
    LocalResolution.onBlock_of_not_rel _ _ _ _ _ (pair.not_rel_first_of_rel_second hAnchor),
    LocalResolution.onBlock_of_rel _ _ _ _ _ hAnchor]

theorem resolution_of_background {anchor : Fin degree} (position : Fin 2)
    (hFirst : ¬(data.vertexPartition wall).Rel pair.first.1 anchor)
    (hSecond : ¬(data.vertexPartition wall).Rel pair.second.1 anchor) :
    pair.resolution position anchor = joinedResolutionAt (data.vertexPartition wall) := by
  rw [resolution, LocalResolution.onBlock_of_not_rel _ _ _ _ _ hFirst,
    LocalResolution.onBlock_of_not_rel _ _ _ _ _ hSecond]

/-- Every block's local shape is one of the two Figure 37 members; the
background is the retained member, read at `position = double`. -/
theorem exists_memberLocal (position : Fin 2) (anchor : Fin degree) :
    ∃ double selected : Fin 2,
      pair.resolution position anchor = memberLocal data star double selected := by
  by_cases hFirst : (data.vertexPartition wall).Rel pair.first.1 anchor
  · exact ⟨pair.firstProfile.doubleLabel, position, pair.resolution_of_first position hFirst⟩
  · by_cases hSecond : (data.vertexPartition wall).Rel pair.second.1 anchor
    · exact ⟨pair.secondProfile.doubleLabel, other position,
        pair.resolution_of_second position hSecond⟩
    · exact ⟨0, 0, (pair.resolution_of_background position hFirst hSecond).trans
        (memberLocal_of_eq data star rfl).symm⟩

theorem resolution_contracts (position : Fin 2) :
    ∀ anchor, (pair.resolution position anchor).ContractsTo (data.vertexPartition wall) := by
  intro anchor
  obtain ⟨double, selected, hEq⟩ := pair.exists_memberLocal position anchor
  rw [hEq]
  exact memberLocal_contracts data star double selected

theorem resolution_refines_left (position : Fin 2) (anchor : Fin degree) :
    (data.edgePartition (star.edge 0)).Refines (pair.resolution position anchor).left := by
  obtain ⟨double, selected, hEq⟩ := pair.exists_memberLocal position anchor
  rw [hEq]
  exact memberLocal_refines_left data star double selected

theorem resolution_refines_right (position : Fin 2) (anchor : Fin degree) :
    (data.edgePartition (star.edge 1)).Refines (pair.resolution position anchor).right := by
  obtain ⟨double, selected, hEq⟩ := pair.exists_memberLocal position anchor
  rw [hEq]
  exact memberLocal_refines_right data star double selected

theorem resolution_star (position : Fin 2) (anchor : Fin degree) :
    ((pair.resolution position anchor).left = data.vertexPartition wall ∧
        (pair.resolution position anchor).newEdge =
          (pair.resolution position anchor).right) ∨
      ((pair.resolution position anchor).right = data.vertexPartition wall ∧
        (pair.resolution position anchor).newEdge =
          (pair.resolution position anchor).left) := by
  obtain ⟨double, selected, hEq⟩ := pair.exists_memberLocal position anchor
  rw [hEq]
  exact memberLocal_star data star double selected

/-- **The blockwise Euler count for every block of every member: defect zero.** -/
theorem resolution_euler (position : Fin 2) (anchor : Fin degree) :
    (pair.resolution position anchor).newEdge.blockCountWithin
          (data.vertexPartition wall) anchor + 1 =
      (pair.resolution position anchor).left.blockCountWithin
          (data.vertexPartition wall) anchor +
        (pair.resolution position anchor).right.blockCountWithin
          (data.vertexPartition wall) anchor := by
  obtain ⟨double, selected, hEq⟩ := pair.exists_memberLocal position anchor
  rw [hEq]
  exact memberLocal_euler data star double selected anchor

/-- Every incident old occurrence is compatible with the endpoint it is
assigned to.  Nothing beyond the gluing datum's own refinement fields is
used. -/
theorem exterior (position : Fin 2) :
    ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨
        (edge : target.V × target.V).2 = wall) →
      ∀ anchor, (data.edgePartition edge).Refines
        (if star.right edge then (pair.resolution position anchor).right
          else (pair.resolution position anchor).left) := by
  intro edge hIncident anchor
  have hMem : edge ∈ GluingDatum.incidentEdges wall := by
    simpa [GluingDatum.incidentEdges] using hIncident
  have hCases : edge = star.edge 0 ∨ edge = star.edge 1 := by
    let label : Fin 2 := star.label.symm ⟨edge, hMem⟩
    have hEdge : star.edge label = edge :=
      congrArg Subtype.val (star.label.apply_symm_apply ⟨edge, hMem⟩)
    have hLabel : label = 0 ∨ label = 1 := by omega
    rcases hLabel with hZero | hOne
    · exact Or.inl (hEdge.symm.trans (congrArg star.edge hZero))
    · exact Or.inr (hEdge.symm.trans (congrArg star.edge hOne))
  rcases hCases with rfl | rfl
  · simpa using pair.resolution_refines_left position anchor
  · simpa using pair.resolution_refines_right position anchor

/-- **Equation (10)'s member `q` as an actual arbitrary-degree outgoing
gluing datum.**  Both expanded endpoints are divalent, so their local
Riemann--Hurwitz inequalities are automatic. -/
noncomputable def candidate (position : Fin 2) :
    BalancedGlobal.Candidate target degree data wall where
  right := star.right
  resolution := pair.resolution position
  contracts := pair.resolution_contracts position
  exterior := fun edge hIncident anchor ↦
    (pair.exterior position edge hIncident anchor).refinesOnBlock anchor
  leftEdges := star.leftEdges
  rightEdges := star.rightEdges
  leftEdges_eq := star.leftEdges_eq
  rightEdges_eq := star.rightEdges_eq
  left_riemannHurwitz := by
    intro anchor _
    obtain ⟨edge, hEdges⟩ := List.length_eq_one_iff.mp star.length_leftEdges
    rw [hEdges]
    exact riemannHurwitzAtBlock_divalent (data.vertexPartition wall)
      (pair.resolution position anchor).left
      (pair.resolution position anchor).newEdge
      (data.edgePartition edge) anchor
  right_riemannHurwitz := by
    intro anchor _
    obtain ⟨edge, hEdges⟩ := List.length_eq_one_iff.mp star.length_rightEdges
    rw [hEdges]
    exact riemannHurwitzAtBlock_divalent (data.vertexPartition wall)
      (pair.resolution position anchor).right
      (pair.resolution position anchor).newEdge
      (data.edgePartition edge) anchor

@[simp] theorem candidate_resolution (position : Fin 2) (anchor : Fin degree) :
    (pair.candidate position).resolution anchor = pair.resolution position anchor := rfl

@[simp] theorem candidate_right (position : Fin 2) :
    (pair.candidate position).right = star.right := rfl

@[simp] theorem candidate_leftEdges (position : Fin 2) :
    (pair.candidate position).leftEdges = star.leftEdges := rfl

@[simp] theorem candidate_rightEdges (position : Fin 2) :
    (pair.candidate position).rightEdges = star.rightEdges := rfl

/-- **The two globally coupled members of Equation (10).** -/
noncomputable def candidates : Fin 2 → BalancedGlobal.Candidate target degree data wall :=
  fun position ↦ pair.candidate position

end Pair

end Pairs


/-! ## 4.  The displayed indices of Figures 37 and 38

Every number in the two figures is read off the profile's own index fields;
none is a parameter and none is a diagram. -/

section Indices

variable {block : WallBlock data wall}
  (profile : W2R1SourceProfile.OccurrenceProfile data star block)

/-- **The induced block count of the new edge on `A₀`.**  One when `Ã` sits at
the doubled direction's endpoint (the whole block is retained), two otherwise
(the block is cut into `e₁`, `e₂`). -/
theorem memberLocal_newEdge_blockCountWithin (position : Fin 2) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (memberLocal data star profile.doubleLabel position).newEdge.blockCountWithin
        (data.vertexPartition wall) anchor =
      if position = profile.doubleLabel then 1 else 2 := by
  by_cases hPosition : position = profile.doubleLabel
  · rw [memberLocal_of_eq data star hPosition, if_pos hPosition]
    exact SheetPartition.blockCountWithin_self _ _
  · rw [memberLocal_of_ne data star hPosition, if_neg hPosition, sideFine_newEdge]
    exact doublePartition_blockCountWithin profile anchor hAnchor

/-- **Figure 37, first member** (`δ⁽ᵠ⁾(Ã)` at the doubled direction):
`|e'| = k₃ = |A₀|`. -/
theorem memberLocal_newEdge_blockCard_retained {position : Fin 2}
    (hPosition : position = profile.doubleLabel) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (memberLocal data star profile.doubleLabel position).newEdge.blockCard anchor =
      data.sourceEdgeIndex profile.third.1 := by
  rw [memberLocal_of_eq data star hPosition]
  show (data.vertexPartition wall).blockCard anchor = data.sourceEdgeIndex profile.third.1
  rw [← SheetPartition.blockCard_congr (data.vertexPartition wall) hAnchor]
  exact profile.single_index.symm

/-- **Figure 37, second member** (`δ⁽ᵠ⁾(Ã)` at the single direction):
`|e'| = k₁`, `|e''| = k₂`, and `k₁ + k₂ = k₃`. -/
theorem memberLocal_newEdge_blockCard_resolved {position : Fin 2}
    (hPosition : position ≠ profile.doubleLabel) :
    (memberLocal data star profile.doubleLabel position).newEdge.blockCard
          (firstSheet profile) = data.sourceEdgeIndex profile.first.1 ∧
      (memberLocal data star profile.doubleLabel position).newEdge.blockCard
          (secondSheet profile) = data.sourceEdgeIndex profile.second.1 ∧
        data.sourceEdgeIndex profile.first.1 + data.sourceEdgeIndex profile.second.1 =
          data.sourceEdgeIndex profile.third.1 := by
  rw [memberLocal_of_ne data star hPosition, sideFine_newEdge]
  exact ⟨doublePartition_blockCard_first profile, doublePartition_blockCard_second profile,
    profile.pair_index.trans profile.single_index.symm⟩

/-- **Figure 38** is Figure 37 with `e₁` dangling.  In the nd2 branch of the
profile the two displayed numbers are `k₃ = k₂ + 1` for the retained member
and `k₂` for the resolved member's surviving block; the resolved member's
other block is the dangling singleton, which the figure does not draw because
`ndG⁽ᵠ⁾` deletes it. -/
theorem nd2_displayed_indices (sourceProfile : W2R1SourceProfile.SourceProfile data star block)
    (hDangling : IsDangling data sourceProfile.first.1) :
    nonDanglingValency data (WallBlock.sourceVertex data wall block) = 2 ∧
      data.sourceEdgeIndex sourceProfile.first.1 = 1 ∧
        data.sourceEdgeIndex sourceProfile.third.1 =
          data.sourceEdgeIndex sourceProfile.second.1 + 1 := by
  rcases sourceProfile.cases with ⟨_, hSurvives⟩ | ⟨hValency, _, hOne, hSucc⟩
  · exact absurd hDangling hSurvives
  · exact ⟨hValency, hOne, hSucc⟩

/-- The nd3 branch: all three occurrences survive, and Figure 37's `k₁`, `k₂`
are both positive. -/
theorem nd3_displayed_indices (sourceProfile : W2R1SourceProfile.SourceProfile data star block)
    (hNd3 : ¬ IsDangling data sourceProfile.first.1) :
    0 < data.sourceEdgeIndex sourceProfile.first.1 ∧
      0 < data.sourceEdgeIndex sourceProfile.second.1 ∧
        nonDanglingValency data (WallBlock.sourceVertex data wall block) = 3 := by
  rcases sourceProfile.cases with ⟨hValency, _⟩ | ⟨_, hDangling, _, _⟩
  · exact ⟨sourceEdgeIndex_pos data sourceProfile.first.1,
      sourceEdgeIndex_pos data sourceProfile.second.1, hValency⟩
  · exact absurd hDangling hNd3

end Indices


/-! ## 5.  The two members at the two blocks -/

section Members

namespace Pair

variable (pair : Pair data star)

/-- The `A₀` count: one in the member that retains `A₀`, two in the other. -/
theorem first_newEdge_blockCountWithin (position : Fin 2) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel pair.first.1 anchor) :
    (pair.resolution position anchor).newEdge.blockCountWithin
        (data.vertexPartition wall) anchor =
      if position = pair.firstProfile.doubleLabel then 1 else 2 := by
  rw [pair.resolution_of_first position hAnchor]
  exact memberLocal_newEdge_blockCountWithin pair.firstProfile.toOccurrenceProfile
    position anchor hAnchor

/-- The `B₀` count, at the **opposite** position. -/
theorem second_newEdge_blockCountWithin (position : Fin 2) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel pair.second.1 anchor) :
    (pair.resolution position anchor).newEdge.blockCountWithin
        (data.vertexPartition wall) anchor =
      if other position = pair.secondProfile.doubleLabel then 1 else 2 := by
  rw [pair.resolution_of_second position hAnchor]
  exact memberLocal_newEdge_blockCountWithin pair.secondProfile.toOccurrenceProfile
    (other position) anchor hAnchor

/-- Figure 37's `|e'| = k₃` at `A₀`. -/
theorem first_retained_blockCard {position : Fin 2}
    (hPosition : position = pair.firstProfile.doubleLabel) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel pair.first.1 anchor) :
    (pair.resolution position anchor).newEdge.blockCard anchor =
      data.sourceEdgeIndex pair.firstProfile.third.1 := by
  rw [pair.resolution_of_first position hAnchor]
  exact memberLocal_newEdge_blockCard_retained pair.firstProfile.toOccurrenceProfile
    hPosition anchor hAnchor

/-- Figure 37's `|e'| = k₁`, `|e''| = k₂`, `k₁ + k₂ = k₃` at `A₀`. -/
theorem first_resolved_blockCard {position : Fin 2}
    (hPosition : position ≠ pair.firstProfile.doubleLabel) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel pair.first.1 anchor) :
    (pair.resolution position anchor).newEdge.blockCard
          (firstSheet pair.firstProfile.toOccurrenceProfile) =
        data.sourceEdgeIndex pair.firstProfile.first.1 ∧
      (pair.resolution position anchor).newEdge.blockCard
          (secondSheet pair.firstProfile.toOccurrenceProfile) =
        data.sourceEdgeIndex pair.firstProfile.second.1 ∧
        data.sourceEdgeIndex pair.firstProfile.first.1 +
            data.sourceEdgeIndex pair.firstProfile.second.1 =
          data.sourceEdgeIndex pair.firstProfile.third.1 := by
  rw [pair.resolution_of_first position hAnchor]
  exact memberLocal_newEdge_blockCard_resolved pair.firstProfile.toOccurrenceProfile hPosition

/-- Figure 37's `|e'| = k₃` at `B₀`. -/
theorem second_retained_blockCard {position : Fin 2}
    (hPosition : other position = pair.secondProfile.doubleLabel) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel pair.second.1 anchor) :
    (pair.resolution position anchor).newEdge.blockCard anchor =
      data.sourceEdgeIndex pair.secondProfile.third.1 := by
  rw [pair.resolution_of_second position hAnchor]
  exact memberLocal_newEdge_blockCard_retained pair.secondProfile.toOccurrenceProfile
    hPosition anchor hAnchor

/-- Figure 37's `|e'| = k₁`, `|e''| = k₂`, `k₁ + k₂ = k₃` at `B₀`. -/
theorem second_resolved_blockCard {position : Fin 2}
    (hPosition : other position ≠ pair.secondProfile.doubleLabel) {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel pair.second.1 anchor) :
    (pair.resolution position anchor).newEdge.blockCard
          (firstSheet pair.secondProfile.toOccurrenceProfile) =
        data.sourceEdgeIndex pair.secondProfile.first.1 ∧
      (pair.resolution position anchor).newEdge.blockCard
          (secondSheet pair.secondProfile.toOccurrenceProfile) =
        data.sourceEdgeIndex pair.secondProfile.second.1 ∧
        data.sourceEdgeIndex pair.secondProfile.first.1 +
            data.sourceEdgeIndex pair.secondProfile.second.1 =
          data.sourceEdgeIndex pair.secondProfile.third.1 := by
  rw [pair.resolution_of_second position hAnchor]
  exact memberLocal_newEdge_blockCard_resolved pair.secondProfile.toOccurrenceProfile hPosition

/-! ### Receipts of both members -/

/-- Both members are globally valid outgoing gluing data. -/
theorem candidate_datum_valid (hValid : data.Valid) (position : Fin 2) :
    (pair.candidate position).datum.Valid :=
  BalancedGlobal.Candidate.datum_valid _ hValid

/-- **Both members preserve the quotient-source genus.**  Every local shape is
a star: one endpoint is the whole wall block and the new edge is the other
endpoint. -/
theorem candidate_sourceGenus (position : Fin 2) :
    genus (pair.candidate position).datum.sourceGraph = genus data.sourceGraph :=
  M11SourceGenus.candidate_sourceGenus_of_stars (pair.candidate position)
    (fun anchor ↦ pair.resolution_star position anchor)

/-- Both members expand the divalent wall into `T₂`: two divalent endpoints. -/
theorem candidate_target_valencies (position : Fin 2) :
    (GluingDatum.incidentEdges
      (target := graph target wall (pair.candidate position).right)
      (oldVertex target wall)).card = 2 ∧
    (GluingDatum.incidentEdges
      (target := graph target wall (pair.candidate position).right)
      (freshVertex target)).card = 2 := by
  simpa using M11SourceCandidates.candidate_target_valencies (pair.candidate position)

/-! ### `δ⁽ᵠ⁾(Ã)` determines the member -/

/-- **`δ⁽ᵠ⁾(Ã) ≠ δ⁽ᵠ⁾(B̃)`**, because `ch u = ch v = 1`.  In the construction
this is definitional: the two blocks are always given opposite positions. -/
theorem positions_opposite (position : Fin 2) : other position ≠ position :=
  other_ne position

/-- **`δ⁽ᵠ⁾(Ã)` determines the gluing datum**: the position of `A₀` is a
bijective label for the member. -/
theorem member_determined : Function.Injective
    (fun position : Fin 2 ↦ (position, other position)) := by
  intro first second hEq
  exact congrArg Prod.fst hEq

/-- In `Fin 2` exactly one of two distinct positions can be the retained one. -/
theorem eq_iff_not_eq_of_ne {first second double : Fin 2} (hNe : first ≠ second) :
    (first = double) ↔ ¬(second = double) := by
  revert hNe
  revert first second double
  decide

/-- **The two members are genuinely distinct**: they induce different block
counts on `A₀`. -/
theorem resolution_ne_of_ne {first second : Fin 2} (hNe : first ≠ second)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel pair.first.1 anchor) :
    pair.resolution first anchor ≠ pair.resolution second anchor := by
  intro hEq
  have hFirst := pair.first_newEdge_blockCountWithin first hAnchor
  have hCount := pair.first_newEdge_blockCountWithin second hAnchor
  rw [hEq, hCount] at hFirst
  have hSplit := eq_iff_not_eq_of_ne (first := first) (second := second)
    (double := pair.firstProfile.doubleLabel) hNe
  by_cases hCase : first = pair.firstProfile.doubleLabel
  · rw [if_pos hCase, if_neg (hSplit.mp hCase)] at hFirst
    exact absurd hFirst (by decide)
  · rw [if_neg hCase, if_pos (by
      by_contra hContra
      exact hCase (hSplit.mpr hContra))] at hFirst
    exact absurd hFirst (by decide)

end Pair

end Members


/-! ## 6.  Alignment

The source labels each block's own directions: `A₀`'s `e₁`, `e₂` are above
`t₂` and `e₃` above `t₃`, and in the proof of Equation (*) `B₀` is given
notation analogous to that of `A₀`, which is a **per-block** choice.  Two
configurations are therefore
possible over one gluing datum, and they are genuinely different (`§7`: the
count that distinguishes them is a gauge invariant).

* **aligned** -- both blocks are doubled over the same direction.  Then in each
  member exactly one of the two blocks is resolved, and the single fine
  partition `data.edgePartition (star.edge 0)` is the right one (for
  `doubleLabel = 0`).
* **opposite** -- the blocks are doubled over different directions.  Then one
  member retains both blocks and the other resolves both, on **opposite
  sides** of the new edge.  A single fine partition cannot express this:
  whichever of the two directions `star` names `0`, the other block's new edge
  stays the whole wall block. -/

section Alignment

namespace Pair

variable (pair : Pair data star)

/-- **Alignment**: the two ramification-one blocks are doubled over one and
the same target direction. -/
def Aligned : Prop :=
  pair.firstProfile.doubleLabel = pair.secondProfile.doubleLabel

instance : Decidable pair.Aligned := by
  unfold Aligned
  infer_instance

theorem aligned_count_sum (position double : Fin 2) :
    ((if position = double then 1 else 2) +
      (if other position = double then 1 else 2) : ℕ) = 3 := by
  revert position double
  decide

theorem opposite_count_sum {position first second : Fin 2} (hNe : first ≠ second) :
    ((if position = first then 1 else 2) +
        (if other position = second then 1 else 2) : ℕ) =
      if position = first then 2 else 4 := by
  revert hNe
  revert position first second
  decide

/-- **Figure 37's pairing, in the aligned configuration.**  Each member
retains one of the two blocks and resolves the other, so across the two
members each block contributes `σ₀(J, 2)` once and `σ₀(J, 3)` once -- which is
exactly what Equation (10) adds up. -/
theorem aligned_counts (hAligned : pair.Aligned) (position : Fin 2)
    {anchorFirst anchorSecond : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel pair.first.1 anchorFirst)
    (hSecond : (data.vertexPartition wall).Rel pair.second.1 anchorSecond) :
    (pair.resolution position anchorFirst).newEdge.blockCountWithin
          (data.vertexPartition wall) anchorFirst +
        (pair.resolution position anchorSecond).newEdge.blockCountWithin
          (data.vertexPartition wall) anchorSecond = 3 := by
  rw [pair.first_newEdge_blockCountWithin position hFirst,
    pair.second_newEdge_blockCountWithin position hSecond, ← hAligned]
  exact aligned_count_sum position pair.firstProfile.doubleLabel

/-- **The opposite configuration**: one member retains both blocks and the
other resolves both.  Nothing here is false -- Equation (10) still balances
block by block -- but the two members are not the ones a single fine partition
would give. -/
theorem opposite_counts (hOpposite : ¬ pair.Aligned) (position : Fin 2)
    {anchorFirst anchorSecond : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel pair.first.1 anchorFirst)
    (hSecond : (data.vertexPartition wall).Rel pair.second.1 anchorSecond) :
    (pair.resolution position anchorFirst).newEdge.blockCountWithin
          (data.vertexPartition wall) anchorFirst +
        (pair.resolution position anchorSecond).newEdge.blockCountWithin
          (data.vertexPartition wall) anchorSecond =
      if position = pair.firstProfile.doubleLabel then 2 else 4 := by
  rw [pair.first_newEdge_blockCountWithin position hFirst,
    pair.second_newEdge_blockCountWithin position hSecond]
  exact opposite_count_sum hOpposite

/-! ### Equality of candidates -/

/-- Equality of candidates is equality of their four data fields; the
remaining six are propositions. -/
theorem candidate_eq {first second : BalancedGlobal.Candidate target degree data wall}
    (hRight : first.right = second.right)
    (hResolution : first.resolution = second.resolution)
    (hLeftEdges : first.leftEdges = second.leftEdges)
    (hRightEdges : first.rightEdges = second.rightEdges) : first = second := by
  cases first
  cases second
  simp only at hRight hResolution hLeftEdges hRightEdges
  subst hRight
  subst hResolution
  subst hLeftEdges
  subst hRightEdges
  rfl

end Pair

/-- **The pair's own member does resolve it**, with the reversed fine shape
`(fineResolution …).reverse`, which a single fine partition does not give. -/
theorem pair_newEdge_blockCountWithin_eq_two (pair : Pair data star)
    {position : Fin 2} (hPosition : other position ≠ pair.secondProfile.doubleLabel)
    {anchor : Fin degree}
    (hAnchor : (data.vertexPartition wall).Rel pair.second.1 anchor) :
    (pair.resolution position anchor).newEdge.blockCountWithin
      (data.vertexPartition wall) anchor = 2 := by
  rw [pair.second_newEdge_blockCountWithin position hAnchor, if_neg hPosition]

/-- **No orientation of the two-star suffices.**  In the opposite
configuration each of the two possible fine directions leaves one of the two
blocks whole, so a single fine partition taken from a direction cannot resolve
both blocks.  This is why the construction uses a per-block, direction-indexed
shape (`sideFine`) and not a re-labelling of `star`. -/
theorem opposite_no_common_fine_direction (pair : Pair data star)
    (hOpposite : ¬ pair.Aligned) (label : Fin 2)
    {anchorFirst anchorSecond : Fin degree}
    (hFirst : (data.vertexPartition wall).Rel pair.first.1 anchorFirst)
    (hSecond : (data.vertexPartition wall).Rel pair.second.1 anchorSecond) :
    (data.edgePartition (star.edge label)).blockCountWithin
          (data.vertexPartition wall) anchorFirst = 1 ∨
      (data.edgePartition (star.edge label)).blockCountWithin
          (data.vertexPartition wall) anchorSecond = 1 := by
  by_cases hLabel : label = pair.firstProfile.doubleLabel
  · refine Or.inr (blockCountWithin_eq_one_of_ne_doubleLabel
      pair.secondProfile.toOccurrenceProfile ?_ anchorSecond hSecond)
    rw [hLabel]
    exact hOpposite
  · exact Or.inl (blockCountWithin_eq_one_of_ne_doubleLabel
      pair.firstProfile.toOccurrenceProfile hLabel anchorFirst hFirst)

end Alignment


/-! ## 7.  Inhabitation from the divalent source input -/

section Inhabitation

/-- With two units of ramification split across two blocks, every other block
above the wall is unramified.  This is the `background` field of the
classifier's `r1` constructor, derived rather than assumed. -/
theorem background_of_split (input : W2SourceInput data star)
    {first second : WallBlock data wall} (hNe : first ≠ second)
    (hFirst : data.localRamification wall first = 1)
    (hSecond : data.localRamification wall second = 1)
    (block : WallBlock data wall) (hBlockFirst : block ≠ first)
    (hBlockSecond : block ≠ second) :
    data.localRamification wall block = 0 := by
  classical
  have hNotFirst : first ∉ ({second, block} : Finset (WallBlock data wall)) := by
    intro hMem
    rcases Finset.mem_insert.mp hMem with hEq | hEq
    · exact hNe hEq
    · exact hBlockFirst (Finset.mem_singleton.mp hEq).symm
  have hNotSecond : second ∉ ({block} : Finset (WallBlock data wall)) := by
    intro hMem
    exact hBlockSecond (Finset.mem_singleton.mp hMem).symm
  have hTriple : ∑ other ∈ ({first, second, block} : Finset (WallBlock data wall)),
      data.localRamification wall other =
        data.localRamification wall first + data.localRamification wall second +
          data.localRamification wall block := by
    rw [Finset.sum_insert hNotFirst, Finset.sum_insert hNotSecond, Finset.sum_singleton,
      add_assoc]
  have hSubset := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun other : WallBlock data wall ↦ data.localRamification wall other)
    (Finset.subset_univ ({first, second, block} : Finset (WallBlock data wall)))
    (fun other _ _ ↦ input.localRamification_nonneg other)
  rw [hTriple, input.sum_localRamification, hFirst, hSecond] at hSubset
  have hNonneg := input.localRamification_nonneg block
  omega

/-- **The `w2-r1` source datum exists at every divalent wall whose two units
of ramification split.**  No hypothesis beyond `W2SourceInput`
and the split itself: the profiles come from
`W2R1SourceProfile.exists_sourceProfile` and the background is
`background_of_split`. -/
noncomputable def pairOfSplit (input : W2SourceInput data star)
    {first second : WallBlock data wall} (hNe : first ≠ second)
    (hFirst : data.localRamification wall first = 1)
    (hSecond : data.localRamification wall second = 1) :
    Pair data star where
  first := first
  second := second
  distinct := hNe
  firstProfile := (W2R1SourceProfile.exists_sourceProfile input first hFirst).some
  secondProfile := (W2R1SourceProfile.exists_sourceProfile input second hSecond).some
  background := background_of_split input hNe hFirst hSecond

/-- The divalent source input either produces the `w2-r1` datum of this module
or concentrates its whole ramification on one block, which is the
`w2-r2-nd3-*` branch. -/
theorem exists_pair_or_concentrated (input : W2SourceInput data star) :
    Nonempty (Pair data star) ∨
      ∃ block : WallBlock data wall, data.localRamification wall block = 2 := by
  rcases input.ramification_split_or_concentrated with hSplit | hConcentrated
  · obtain ⟨first, second, hNe, hFirst, hSecond⟩ := hSplit
    exact Or.inl ⟨pairOfSplit input hNe hFirst hSecond⟩
  · exact Or.inr hConcentrated

end Inhabitation

/-! ## 8.  The gauge check

The two swap operations of Part I (tree-swap and branch-swap, in the discussion
before `definition-gd-iso`) act on this case's only invariant --
the induced block count of a direction inside a wall block -- in the two ways
below, and neither can change which direction a block is doubled over. -/

section Gauge

/-- **`doubleLabel` is characterised by the induced block count.**  It is the
unique direction whose occurrence partition cuts the block in two. -/
theorem doubleLabel_iff_blockCountWithin_eq_two
    {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block)
    (label : Fin 2) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    (data.edgePartition (star.edge label)).blockCountWithin
        (data.vertexPartition wall) anchor = 2 ↔ label = profile.doubleLabel := by
  constructor
  · intro hCount
    by_contra hLabel
    rw [blockCountWithin_eq_one_of_ne_doubleLabel profile hLabel anchor hAnchor] at hCount
    exact absurd hCount (by decide)
  · intro hLabel
    rw [hLabel]
    exact doublePartition_blockCountWithin profile anchor hAnchor

/-- A branch swap at the wall is a transposition of two sheets of **one** wall
block (Part I's branch-swap asks for `i ∼_v j`), hence fixes every wall block
setwise. -/
theorem branchSwap_pointwise {i j : Fin degree}
    (hRel : (data.vertexPartition wall).Rel i j) (sheet : Fin degree) :
    (data.vertexPartition wall).Rel (Equiv.swap i j sheet) sheet :=
  (data.vertexPartition wall).swap_apply_rel_self_of_rel hRel sheet

/-- **Branch-swap invariance.**  A branch swap taken at the wall leaves every
direction's induced block count on every wall block unchanged, so the
direction a ramification-one block is doubled over -- and therefore
`Pair.Aligned` -- is the same before and after. -/
theorem doubleLabel_iff_branchSwap
    {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block)
    (permutation : Equiv.Perm (Fin degree))
    (hPointwise : ∀ sheet, (data.vertexPartition wall).Rel (permutation sheet) sheet)
    (label : Fin 2) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    ((data.edgePartition (star.edge label)).relabel permutation).blockCountWithin
        (data.vertexPartition wall) anchor = 2 ↔ label = profile.doubleLabel := by
  rw [SheetPartition.relabel_blockCountWithin_fixed_of_pointwise
    (data.edgePartition (star.edge label)) (data.vertexPartition wall)
    permutation hPointwise anchor]
  exact doubleLabel_iff_blockCountWithin_eq_two profile label anchor hAnchor

/-- **Tree-swap invariance.**  One permutation applied to every relation
(Part I's tree-swap) transports the counts along itself, so again the doubled direction
is unchanged. -/
theorem doubleLabel_iff_treeSwap
    {block : WallBlock data wall}
    (profile : W2R1SourceProfile.OccurrenceProfile data star block)
    (permutation : Equiv.Perm (Fin degree))
    (label : Fin 2) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel block.1 anchor) :
    ((data.edgePartition (star.edge label)).relabel permutation).blockCountWithin
        ((data.vertexPartition wall).relabel permutation) (permutation anchor) = 2 ↔
      label = profile.doubleLabel := by
  rw [SheetPartition.relabel_blockCountWithin (data.edgePartition (star.edge label))
    (data.vertexPartition wall) permutation anchor]
  exact doubleLabel_iff_blockCountWithin_eq_two profile label anchor hAnchor

end Gauge

end DraismaVargas.LocalCases.W2R1SourceCandidates
