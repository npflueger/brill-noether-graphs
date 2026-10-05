module

public import DraismaVargas.LocalCases.W2M1kLimitMatrix

@[expose] public section

/-!
# Figure 33's leaf member: the induced stable-row map

Source: Draisma--Vargas Part I, case `{w2-r2-nd3-M-1k}`, Figure 33 and
Equation (7); the induced-labelling paragraph of the `{w2-r2}` preamble.

`W2M1kStableLift` read Figure 33's two **divalent** members as instances of
`LimitChainCore`, and proved that the leaf member `M⁽¹⁾` is **not** one
(`W2M1kStableLift.leaf_not_wallCandidate`): Base I.a's retained endpoint is a
target leaf and carries no wall direction, so the core's
`LimitChainCore.WallCandidate.left` is unsatisfiable.  This module,
`W2M1kLeafRowDescent` and `W2M1kLeafLimitMatrix` are therefore a bespoke leaf
chain, on the pattern of the only other member with a target leaf, the M11
chain's split member (`M11SplitStableLift`, `M11SplitRowDescent`,
`M11SplitLimitMatrix`).

Nothing new about the member is proved here: `W2M1kLeaves` and
`W2M1kStableGraph` §8--§9 already carry the whole census.  What is added is the
**background** half -- which those two modules did not need -- and the lift:

* `leaf_pasted_right_rel_background` / `leaf_background_old_incident_iff` --
  off `A₀` the member installs `M11SourceCandidates.backgroundResolution`,
  which retains the whole wall block at the fresh endpoint, so the fresh source
  vertex over a background sheet has exactly the incoming wall vertex's old
  incidences;
* `leaf_nonDanglingIncident_background` -- and its regrown occurrences there are
  **all pruned** (`W2M1kLeaves.leaf_new_background_dangling`), so the surviving
  star off `A₀` is the literal `oldSourceEdge`-image of the incoming one.  This
  is where the leaf member parts company with `LimitChainCore`, whose
  `Background.replace` matches each regrown occurrence with an old one;
* `leaf_consecutive_retained` / `leafStablePathLift` -- retention respects the
  incoming stable quotient.  At the wall the only vertices of surviving valency
  two are background ones: the distinguished block's own source vertex is the
  case's `w2-r2-nd3` branch vertex, of surviving valency three
  (`W2M1kStableLift.selected_valency_ne_two`);
* `leaf_new_stablePath_eq_first` -- **both** surviving regrown occurrences join
  `e₁`'s row (`W2M1kStableGraph.leaf_new_pin_stablePath_eq`,
  `leaf_new_second_stablePath_eq`), which is Figure 33's `c⁽¹⁾ = 2c(e₁)` at the
  occurrence level, and gives `leafStablePathLift_surjective`.

The reverse map, hence injectivity, is `W2M1kLeafRowDescent`; the columns are
`W2M1kLeafLimitMatrix`.
-/

namespace DraismaVargas.LocalCases.W2M1kLeafStableLift

open DraismaVargas.Infrastructure
open TargetExpansion
open W4Assembly W4StableSource StableLocalProperties W2R1Target SecondEquation
open ResolutionM11 ResolutionM1k GlobalM11Arbitrary
open ResolutionAwayFromWall
open W2M1kSourceCandidates W2M1kLeaves
open W2M1kStableGraph
open LimitChainCore (pasted newSourceEdge_incident_old newSourceEdge_incident_fresh
  oldSourceEdge_ne_newSourceEdge sourceEndpoint_eq_of_rel)

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : TwoStar target wall}
  {block : WallBlock data wall}
  {profile : W2R2SourceProfile.SourceProfile data star block}

noncomputable local instance : DecidableEq target.edges := Classical.decEq _

/-! ## §0  The two spellings of "off `A₀`"

`W2M1kLeaves` anchors the leaf member at `pinSheet profile 0`, the sheet Base
I.a's two wall directions share; `W2M1kStableGraph`'s background section
anchors at `block.1`.  Both name the distinguished block. -/

theorem background_pin_of_block {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel block.1 sheet) :
    ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet :=
  fun hRel ↦ hSheet ((pinSheet_rel 0).trans hRel)

theorem background_block_of_pin {sheet : Fin degree}
    (hSheet : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    ¬ (data.vertexPartition wall).Rel block.1 sheet :=
  fun hRel ↦ hSheet ((pinSheet_rel 0).symm.trans hRel)

/-! ## §1  The leaf member off `A₀`

At a background wall block `M⁽¹⁾` installs
`M11SourceCandidates.backgroundResolution`, whose fresh endpoint is the whole
wall block. -/

/-- **Off `A₀` the fresh endpoint partition is the incoming wall partition.** -/
theorem leaf_pasted_right_rel_background (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (first second : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) first) :
    (pasted (LeafPair.candidate input shape pair)).right.Rel first second ↔
      (data.vertexPartition wall).Rel first second := by
  show (LocalResolution.pasteRight (data.vertexPartition wall)
    (LeafPair.candidate input shape pair).resolution
    (LeafPair.candidate input shape pair).contracts).Rel first second ↔ _
  unfold LocalResolution.pasteRight
  rw [SheetPartition.paste_rel_iff, leaf_resolution_background input shape pair _
    (fun hRel ↦ hBackground (hRel.trans ((data.vertexPartition wall).rel_repr_left first)))]
  exact Iff.rfl

theorem leaf_background_fresh_rel (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (first second : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) first) :
    ((LeafPair.candidate input shape pair).datum.vertexPartition
        (freshVertex target)).Rel first second ↔
      (data.vertexPartition wall).Rel first second := by
  have hVertex : (LeafPair.candidate input shape pair).datum.vertexPartition
      (freshVertex target) = (pasted (LeafPair.candidate input shape pair)).right :=
    GlobalResolution.expandedVertexPartition_fresh data wall _
  rw [hVertex]
  exact leaf_pasted_right_rel_background input shape pair first second hBackground

/-- **The retained occurrences at a background fresh vertex are exactly the
incoming ones.** -/
theorem leaf_background_old_incident_iff (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet)
    (edge : data.SourceEdge) :
    Incident (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).oldSourceEdge edge)
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (freshVertex target) sheet) ↔
      Incident data edge (data.sourceEndpoint wall sheet) := by
  have hTarget : occurrenceEquiv target wall (LeafPair.candidate input shape pair).right
        (some edge.1.1) ∈
      GluingDatum.incidentEdges
        (target := graph target wall (LeafPair.candidate input shape pair).right)
        (freshVertex target) ↔
      edge.1.1 ∈ GluingDatum.incidentEdges wall := by
    simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [occurrenceEquiv_some]
    exact (oldEnds_incident_freshVertex_iff target wall
      (LeafPair.candidate input shape pair).right edge.1.1).trans
      (and_iff_left (leaf_right input shape pair edge.1.1))
  rw [incident_iff_target_mem_and_rel, incident_iff_target_mem_and_rel]
  change (_ ∧ ((LeafPair.candidate input shape pair).datum.vertexPartition
      (freshVertex target)).Rel
      (((LeafPair.candidate input shape pair).datum.vertexPartition
        (freshVertex target)).repr sheet) edge.1.2) ↔
      (_ ∧ (data.vertexPartition wall).Rel
        ((data.vertexPartition wall).repr sheet) edge.1.2)
  simp only [SheetPartition.Rel, SheetPartition.repr_idem]
  change (_ ∧ ((LeafPair.candidate input shape pair).datum.vertexPartition
      (freshVertex target)).Rel sheet edge.1.2) ↔
      (_ ∧ (data.vertexPartition wall).Rel sheet edge.1.2)
  rw [leaf_background_fresh_rel input shape pair sheet edge.1.2 hBackground]
  exact and_congr_left fun _ ↦ hTarget

/-- A regrown occurrence meeting a background fresh vertex lies in that same
incoming wall block, hence is one of the proved pruned background arms. -/
theorem leaf_background_new_incident_rel (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (anchor sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) anchor)
    (hIncident : Incident (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge sheet)
      ((LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) anchor)) :
    (data.vertexPartition wall).Rel anchor sheet :=
  (leaf_pasted_right_rel_background input shape pair anchor sheet hBackground).mp
    (new_incident_fresh_sheet_rel (LeafPair.candidate input shape pair) anchor sheet hIncident)

/-- **The surviving star at a background fresh vertex is the literal
`oldSourceEdge`-image of the incoming one.**  Every regrown arm there is pruned
(`W2M1kLeaves.leaf_new_background_dangling`), so no replacement bijection --
`LimitChainCore.Background.replace` -- is involved. -/
theorem leaf_nonDanglingIncident_background (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    nonDanglingIncident (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (freshVertex target) sheet) =
      (nonDanglingIncident data (data.sourceEndpoint wall sheet)).image
        (LeafPair.candidate input shape pair).oldSourceEdge := by
  classical
  ext edge
  constructor
  · intro hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hMem
    rcases ResolutionPruning.sourceEdge_cases (LeafPair.candidate input shape pair) edge with
      ⟨old, rfl⟩ | ⟨other, rfl⟩
    · refine Finset.mem_image.mpr ⟨old, (mem_nonDanglingIncident _ _ _).mpr ⟨?_, ?_⟩, rfl⟩
      · exact fun hDangling ↦ hSurvives
          ((leaf_old_isDangling_iff input shape pair old).mpr hDangling)
      · exact (leaf_background_old_incident_iff input shape pair sheet hBackground old).mp
          hIncident
    · have hRel := leaf_background_new_incident_rel input shape pair sheet other hBackground
        hIncident
      exact (hSurvives (leaf_new_background_dangling input shape pair other
        (fun hOther ↦ hBackground (hOther.trans hRel.symm)))).elim
  · intro hMem
    obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hMem
    obtain ⟨hSurvives, hIncident⟩ := (mem_nonDanglingIncident _ _ _).mp hOld
    exact (mem_nonDanglingIncident _ _ _).mpr
      ⟨ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 old hSurvives,
        (leaf_background_old_incident_iff input shape pair sheet hBackground old).mpr hIncident⟩

theorem leaf_nonDanglingValency_background (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile) (sheet : Fin degree)
    (hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) sheet) :
    nonDanglingValency (LeafPair.candidate input shape pair).datum
        ((LeafPair.candidate input shape pair).datum.sourceEndpoint
          (freshVertex target) sheet) =
      nonDanglingValency data (data.sourceEndpoint wall sheet) := by
  classical
  rw [← card_nonDanglingIncident,
    leaf_nonDanglingIncident_background input shape pair sheet hBackground,
    Finset.card_image_of_injective _
      (ResolutionCut.oldSourceEdge_injective (LeafPair.candidate input shape pair)),
    card_nonDanglingIncident]

/-! ## §2  Retention respects the incoming stable quotient -/

/-- **Every incoming consecutive pair stays consecutive.**  At the wall the
junction is a background vertex: the distinguished block's own source vertex is
the case's `w2-r2-nd3` branch vertex, of surviving valency three. -/
theorem leaf_consecutive_retained (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (first second : NonDanglingEdge data)
    (hConsecutive : Consecutive data first second) :
    Consecutive (LeafPair.candidate input shape pair).datum
      (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 first)
      (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 second) := by
  obtain ⟨hNe, vertex, hFirst, hSecond, hValency⟩ := hConsecutive
  by_cases hAt : vertex.1.1 = wall
  · have hVertex : data.sourceEndpoint wall vertex.1.2 = vertex :=
      (data.sourceEndpoint_eq_iff wall vertex.1.2 vertex).mpr ⟨hAt.symm, rfl⟩
    have hBackground : ¬ (data.vertexPartition wall).Rel (pinSheet profile 0) vertex.1.2 := by
      intro hRel
      refine W2M1kStableLift.selected_valency_ne_two profile
        ((pinSheet_rel 0).trans hRel) ?_
      rw [hVertex]
      exact hValency
    refine ⟨fun hEq ↦ hNe (retainedEdge_injective _ input.valid.1 hEq),
      (LeafPair.candidate input shape pair).datum.sourceEndpoint
        (freshVertex target) vertex.1.2, ?_, ?_, ?_⟩
    · exact (leaf_background_old_incident_iff input shape pair vertex.1.2 hBackground
        first.1).mpr (hVertex.symm ▸ hFirst)
    · exact (leaf_background_old_incident_iff input shape pair vertex.1.2 hBackground
        second.1).mpr (hVertex.symm ▸ hSecond)
    · rw [leaf_nonDanglingValency_background input shape pair vertex.1.2 hBackground, hVertex]
      exact hValency
  · exact consecutive_retained_of_away (LeafPair.candidate input shape pair) input.valid
      (leaf_sourceGenus input shape pair) first second hNe vertex hAt hFirst hSecond hValency

/-- **Figure 33's induced stable-row map for `M⁽¹⁾`**, evaluated by retaining
any actual surviving occurrence of the incoming row. -/
noncomputable def leafStablePathLift (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    StablePath data → StablePath (LeafPair.candidate input shape pair).datum :=
  Quot.lift
    (fun edge ↦ (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 edge).stablePath)
    (fun _ _ hConsecutive ↦ stablePath_eq_of_consecutive
      (leaf_consecutive_retained input shape pair _ _ hConsecutive))

@[simp] theorem leafStablePathLift_mk (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (edge : NonDanglingEdge data) :
    leafStablePathLift input shape pair edge.stablePath =
      (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 edge).stablePath := rfl

theorem leaf_stablePath_retained_eq_of_consecutive (input : W2SourceInput data star)
    (shape : Shape profile) (pair : LeafPair profile)
    (first second : NonDanglingEdge data) (hConsecutive : Consecutive data first second) :
    (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 first).stablePath =
      (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 second).stablePath :=
  stablePath_eq_of_consecutive (leaf_consecutive_retained input shape pair first second
    hConsecutive)

/-! ## §3  Both surviving regrown occurrences join `e₁`'s row -/

/-- The retained copy of `e₁`, the incoming occurrence both of `M⁽¹⁾`'s
surviving regrown occurrences represent. -/
theorem leaf_first_survives (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    ¬ IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).oldSourceEdge profile.first.1) :=
  ResolutionSurvival.not_isDangling_oldSourceEdge _ input.valid.1 _ profile.first_survives

/-- **Only the retained pair's two regrown occurrences survive.**  Every other
sheet of `A₀` and every background sheet carries a pruned source leaf. -/
theorem leaf_new_survives_cases (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge sheet)) :
    sheet = pinSheet profile 0 ∨ sheet = pair.second := by
  by_cases hWall : (data.vertexPartition wall).Rel (pinSheet profile 0) sheet
  · by_cases hPin : sheet = pinSheet profile 0
    · exact Or.inl hPin
    · by_cases hSecond : sheet = pair.second
      · exact Or.inr hSecond
      · exact absurd (leaf_new_singleton_dangling input shape pair sheet hWall hPin hSecond)
          hSurvives
  · exact absurd (leaf_new_background_dangling input shape pair sheet hWall) hSurvives

/-- **`c⁽¹⁾ = 2c(e₁)` at the occurrence level.**  Both surviving regrown
occurrences of `M⁽¹⁾` join the retained `e₁`'s stable row: the one through `x`
at the trivalent endpoint over `{x}`, the one through `pair.second` through the
divalent leaf source vertex of the retained pair. -/
theorem leaf_new_stablePath_eq_first (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) (sheet : Fin degree)
    (hSurvives : ¬ IsDangling (LeafPair.candidate input shape pair).datum
      ((LeafPair.candidate input shape pair).newSourceEdge sheet)) :
    NonDanglingEdge.stablePath
        (⟨(LeafPair.candidate input shape pair).newSourceEdge sheet, hSurvives⟩ :
          NonDanglingEdge (LeafPair.candidate input shape pair).datum) =
      NonDanglingEdge.stablePath
        (⟨(LeafPair.candidate input shape pair).oldSourceEdge profile.first.1,
          leaf_first_survives input shape pair⟩ :
          NonDanglingEdge (LeafPair.candidate input shape pair).datum) := by
  rcases leaf_new_survives_cases input shape pair sheet hSurvives with rfl | rfl
  · exact leaf_new_pin_stablePath_eq input shape pair
  · exact leaf_new_second_stablePath_eq input shape pair

/-- No stable row of `M⁽¹⁾` lies entirely in the regrown fibre. -/
theorem leaf_exists_retained_row (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile)
    (edge : NonDanglingEdge (LeafPair.candidate input shape pair).datum) :
    ∃ old : NonDanglingEdge data,
      (retainedEdge (LeafPair.candidate input shape pair) input.valid.1 old).stablePath =
        edge.stablePath := by
  rcases nonDanglingEdge_cases (LeafPair.candidate input shape pair) input.valid
      (leaf_sourceGenus input shape pair) edge with ⟨old, rfl⟩ | ⟨sheet, hSurvives, rfl⟩
  · exact ⟨old, rfl⟩
  · exact ⟨⟨profile.first.1, profile.first_survives⟩,
      (leaf_new_stablePath_eq_first input shape pair sheet hSurvives).symm⟩

theorem leafStablePathLift_surjective (input : W2SourceInput data star) (shape : Shape profile)
    (pair : LeafPair profile) :
    Function.Surjective (leafStablePathLift input shape pair) := by
  intro path
  induction path using Quot.inductionOn with
  | h edge =>
      obtain ⟨old, hPath⟩ := leaf_exists_retained_row input shape pair edge
      exact ⟨old.stablePath, hPath⟩

end DraismaVargas.LocalCases.W2M1kLeafStableLift
