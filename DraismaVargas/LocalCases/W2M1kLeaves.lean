import DraismaVargas.LocalCases.W2M1kSourceCandidates
import DraismaVargas.LocalCases.M11SplitLeaves

/-!
# The target leaf of Figure 33's first member, and the arms it prunes

Source: Draisma--Vargas Part I, Case {w2-r2-nd3-M-1k} (abbreviated M-1k),
Figure 33 and Equation (7).  The Base I/II vocabulary is fixed in Case {w2-r2},
and the notation of Case {w2-r2-nd3} is used throughout.

`M⁽¹⁾` (`W2M1kSourceCandidates.LeafPair.candidate`, Base I.a) is the only
member of Figure 33 whose expanded wall is not `T₂`: its target valencies are
`(1, 3)` (`leaf_target_valencies`), the **retained** endpoint being a target
leaf.  This module is the M-1k analogue of `M11SplitLeaves`, and exactly its
scope: the source incidence count over that target leaf, blockwise, and the
resulting pruning of every monovalent arm.  Survival of the two arms that do
*not* prune, the surviving stars and the stable rows are
`W2M1kStableGraph`'s, as `M11SplitSurvival` is `M11SplitLeaves`'s successor.

Write `x := pinSheet profile 0` for Base I.a's common pinned sheet -- the one
sheet of `A₀` that *both* wall directions isolate, carrying `e₁` above `t₂`
and the dangling `e₄` above `t₃` -- and `pair.second` for its partner at the
new leaf.  Above `A₀` the member is `ResolutionM1k.firstResolution`: the leaf
retains the pair `{x, pair.second}` and splits every other sheet of `A₀` into
a singleton, the trivalent endpoint detaches `x`, and the new edge is discrete
on `A₀`.  Off `A₀` it installs `M11SourceCandidates.backgroundResolution`,
whose leaf side is discrete.

So the leaf source vertices are:

| leaf source vertex | incidences |
|---|---|
| over `{x, pair.second}` | new(`x`), new(`pair.second`) |
| over `{s}`, `s ∈ A₀ ∖ {x, pair.second}` | new(`s`) |
| over `{s}`, `s` in a background block | new(`s`) |

and the last two rows are monovalent, so by
`M11SplitLeaves.newSourceEdge_isDangling_of_left_card_one` their one arm is a
source leaf and is pruned.  That is `k - 1` pruned new occurrences over `A₀`
itself, plus every background one -- the M-1k phenomenon that has no analogue
in Figure 34, where every endpoint is divalent or trivalent.

## What is general, and where it lives

`pairBlock_block_of_rel_of_ne` and `pairBlock_splitBlock_count` are statements
about `SheetPartition.pairBlock` and `SheetPartition.splitBlock` alone, with
no wall, star, profile or candidate in them (compare `pairBlock_block_first`
in `Infrastructure/SheetPartition.lean`).
`incidentEdges_pair` is a local copy of `M11SourceCandidates`' private lemma
of the same name.

## What is *not* done here

No `IsDangling` verdict for a *surviving* arm, no `nonDanglingIncident`, no
`nonDanglingValency`, no `stablePath`: all of those are `W2M1kStableGraph`.
-/

namespace DraismaVargas.LocalCases.W2M1kLeaves

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open W2M1kSourceCandidates

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

section Leaves

variable {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

/-- A divalent wall has exactly its two labelled occurrences. -/
theorem incidentEdges_pair (star : TwoStar target wall) :
    GluingDatum.incidentEdges wall = {star.edge 0, star.edge 1} := by
  classical
  ext edge
  constructor
  · intro hEdge
    obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hEdge⟩
    have hTarget : star.edge label = edge := congrArg Subtype.val hLabel
    rw [← hTarget, Finset.mem_insert, Finset.mem_singleton]
    have hCases : label = 0 ∨ label = 1 := by omega
    rcases hCases with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hEdge
    rcases Finset.mem_insert.mp hEdge with hEq | hEq
    · rw [hEq]; exact star.edge_mem_incidentEdges 0
    · rw [Finset.mem_singleton.mp hEq]; exact star.edge_mem_incidentEdges 1

theorem star_edge_zero_ne_one (star : TwoStar target wall) :
    star.edge 0 ≠ star.edge 1 := fun hEq ↦
  (by decide : (0 : Fin 2) ≠ 1) (star.edge_injective hEq)

/-- Base I.a: both wall directions pin the same sheet of `A₀`. -/
theorem leaf_pinSheet_eq (pair : LeafPair profile) (label : Fin 2) :
    pinSheet profile label = pinSheet profile 0 := by
  have hCases : label = 0 ∨ label = 1 := by omega
  rcases hCases with rfl | rfl
  · rfl
  · exact pair.aligned.symm

/-- Retaining one pair leaves every other sheet of the block alone. -/
theorem pairBlock_block_of_rel_of_ne (partition : SheetPartition degree)
    (first second sheet : Fin degree) (hne : first ≠ second)
    (hTogether : partition.Rel first second) (hRel : partition.Rel first sheet)
    (hNeFirst : sheet ≠ first) (hNeSecond : sheet ≠ second) :
    (partition.pairBlock first second hne).block sheet = {sheet} := by
  classical
  have hReprSheet : (partition.pairBlock first second hne).repr sheet = sheet :=
    partition.pairBlock_repr_of_rel_of_ne_second first second sheet hne hRel hNeSecond
  ext value
  simp only [SheetPartition.mem_block_iff, Finset.mem_singleton, SheetPartition.rel_iff,
    hReprSheet]
  constructor
  · intro hEq
    by_cases hValueSecond : value = second
    · subst value
      rw [partition.pairBlock_repr_second first second hne hTogether] at hEq
      exact absurd hEq hNeFirst
    · by_cases hValueBlock : partition.Rel first value
      · rw [partition.pairBlock_repr_of_rel_of_ne_second first second value hne
          hValueBlock hValueSecond] at hEq
        exact hEq.symm
      · exfalso
        apply hValueBlock
        rw [partition.pairBlock_repr_of_not_rel first second value hne hValueBlock] at hEq
        exact (hEq ▸ hRel).trans (partition.rel_repr_left value)
  · rintro rfl
    exact (partition.pairBlock_repr_of_rel_of_ne_second first second value hne hRel
      hNeSecond).symm

/-- The retained pair carries two singleton new occurrences: `|e'| = |e''| = 1`
in Base I.a. -/
theorem pairBlock_splitBlock_count (partition : SheetPartition degree)
    (first second sheet : Fin degree) (hne : first ≠ second)
    (hTogether : partition.Rel first second)
    (hRel : (partition.pairBlock first second hne).Rel first sheet) :
    (partition.splitBlock first).blockCountWithin
      (partition.pairBlock first second hne) sheet = 2 := by
  classical
  have hBlock : (partition.pairBlock first second hne).block sheet = {first, second} :=
    ((partition.pairBlock first second hne).block_eq_of_rel hRel).symm.trans
      (partition.pairBlock_block_first first second hne hTogether)
  unfold SheetPartition.blockCountWithin
  rw [hBlock, Finset.image_insert, Finset.image_singleton,
    partition.splitBlock_repr_of_rel first first rfl,
    partition.splitBlock_repr_of_rel first second hTogether, Finset.card_pair hne]

/-- The member's side assignment sends **both** wall directions to the fresh
endpoint. -/
theorem leaf_right (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (edge : target.edges) :
    (LeafPair.candidate input shape pair).right edge = true := rfl

theorem leaf_resolution_selected (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (anchor : Fin degree)
    (hAnchor : (data.vertexPartition wall).Rel (pinSheet profile 0) anchor) :
    (LeafPair.candidate input shape pair).resolution anchor =
      firstResolution (data.vertexPartition wall) (pinSheet profile 0) pair.second
        pair.ne_second pair.rel_second := by
  change LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile 0) _
    (M11SourceCandidates.backgroundResolution (data.vertexPartition wall)) anchor = _
  rw [LocalResolution.onBlock_of_rel _ _ _ _ _ hAnchor]
  rfl

theorem leaf_resolution_background (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (anchor : Fin degree)
    (hAnchor : ¬(data.vertexPartition wall).Rel (pinSheet profile 0) anchor) :
    (LeafPair.candidate input shape pair).resolution anchor =
      M11SourceCandidates.backgroundResolution (data.vertexPartition wall) anchor := by
  change LocalResolution.onBlock (data.vertexPartition wall) (pinSheet profile 0) _
    (M11SourceCandidates.backgroundResolution (data.vertexPartition wall)) anchor = _
  rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _ hAnchor]

/-- The source incidence count over the member's target leaf is its local
new-edge block count, by `M11SplitLeaves.card_incident_left`. -/
theorem leaf_card_incident_left (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree) :
    Fintype.card (IncidentSourceEdge (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (oldVertex target wall) sheet)) =
      ((LeafPair.candidate input shape pair).resolution
          ((data.vertexPartition wall).repr sheet)).newEdge.blockCountWithin
        ((LeafPair.candidate input shape pair).resolution
          ((data.vertexPartition wall).repr sheet)).left sheet :=
  M11SplitLeaves.card_incident_left _ (leaf_target_valencies input shape pair).1 sheet

/-- **The retained pair's leaf source vertex is divalent**: its two incidences
are the new occurrences through `x` and through `pair.second`.  This is Base
I.a's `A_u`, `|A_u| = 2`, `r^q(A_u) = 2`. -/
theorem leaf_card_left_pair (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hRel : ((data.vertexPartition wall).pairBlock (pinSheet profile 0) pair.second
      pair.ne_second).Rel (pinSheet profile 0) sheet) :
    Fintype.card (IncidentSourceEdge (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) sheet)) = 2 := by
  have hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet :=
    ((data.vertexPartition wall).pairBlock_refines (pinSheet profile 0) pair.second
      pair.ne_second pair.rel_second).rel hRel
  rw [leaf_card_incident_left input shape pair sheet, leaf_resolution_selected input shape pair _
    (hWall.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  exact pairBlock_splitBlock_count (data.vertexPartition wall) (pinSheet profile 0)
    pair.second sheet pair.ne_second pair.rel_second hRel

/-- **Every other sheet of `A₀` has a monovalent leaf source vertex.** -/
theorem leaf_card_left_singleton (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNeFirst : sheet ≠ pinSheet profile 0) (hNeSecond : sheet ≠ pair.second) :
    Fintype.card (IncidentSourceEdge (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) sheet)) = 1 := by
  rw [leaf_card_incident_left input shape pair sheet, leaf_resolution_selected input shape pair _
    (hWall.trans ((data.vertexPartition wall).rel_repr_right sheet))]
  exact SheetPartition.blockCountWithin_eq_one_of_block_eq_singleton _ _ _
    (pairBlock_block_of_rel_of_ne (data.vertexPartition wall) (pinSheet profile 0)
      pair.second sheet pair.ne_second pair.rel_second hWall hNeFirst hNeSecond)

/-- **Every background sheet has a monovalent leaf source vertex.** -/
theorem leaf_card_left_background (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    Fintype.card (IncidentSourceEdge (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (oldVertex target wall) sheet)) = 1 := by
  have hRepr : ¬(data.vertexPartition wall).Rel (pinSheet profile 0)
      ((data.vertexPartition wall).repr sheet) := fun hRel ↦
    hBackground (hRel.trans ((data.vertexPartition wall).rel_repr_left sheet))
  rw [leaf_card_incident_left input shape pair sheet,
    leaf_resolution_background input shape pair _ hRepr]
  exact SheetPartition.blockCountWithin_self _ _

/-- **The pruned arms of `M⁽¹⁾`, over `A₀`**: every new occurrence through a
sheet of `A₀` outside the retained pair is a source leaf, hence dangling. -/
theorem leaf_new_singleton_dangling (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (hNeFirst : sheet ≠ pinSheet profile 0) (hNeSecond : sheet ≠ pair.second) :
    IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge sheet) :=
  M11SplitLeaves.newSourceEdge_isDangling_of_left_card_one _ input.valid sheet
    (leaf_card_left_singleton input shape pair sheet hWall hNeFirst hNeSecond)

/-- **The pruned arms of `M⁽¹⁾`, off `A₀`**: every background new occurrence is
a source leaf, hence dangling.  This is `M11SplitLeaves`'s own statement for
the M11 split, at arbitrary background block size. -/
theorem leaf_new_background_dangling (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬(data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge sheet) :=
  M11SplitLeaves.newSourceEdge_isDangling_of_left_card_one _ input.valid sheet
    (leaf_card_left_background input shape pair sheet hBackground)

end Leaves

end DraismaVargas.LocalCases.W2M1kLeaves
