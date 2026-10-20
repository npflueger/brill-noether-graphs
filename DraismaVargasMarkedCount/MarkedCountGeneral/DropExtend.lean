module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropPos
public import DraismaVargasCount.ResolutionExpansionFree

@[expose] public section

/-!
# The drop lemma: extending an isomorphism of contractions over a divalent vertex

Two contraction sites `S₁, S₂` (a target edge `cᵢ` at a divalent change-zero vertex `xᵢ`, module
`DropContract`) on tree targets, and an isomorphism `φ : S₁.D ≅ S₂.D` of the contracted data that
fixes the merged vertex and carries the image `ō₁` of the other edge at `x₁` to `ō₂`. Then `φ`
**extends to an isomorphism `Ψ : data₁ ≅ data₂`** commuting with the two contractions, on source
vertices (`extend_vmap`) and on the occurrences away from `cᵢ` (`extend_emb`).

The construction is the public resolution machinery, read at the natural placement:

* `M11WallExhaustion.datumIso` identifies each `dataᵢ` with the resolution expansion of its own
  contraction at the merged vertex (the side of a wall occurrence is the end of `cᵢ` its
  unfolding meets);
* `ResolutionExpansionFree.liftFree` lifts `φ` between the two resolution expansions, given a
  decoupled transport (`transport`): the three free permutations are those of `φ` at the merged
  vertex and at `ō₁`, corrected inside blocks (`BlockNormalize.perm`) so as to relabel the three
  resolution partitions `P_x, P_w, P_c` literally. Over `x` the partitions of `x`, `c` and the
  other edge only have the same blocks (`DivalentZero`), and over the merged vertex the join has
  the blocks of `P_w` (`Site.merged_rel_iff`); these are exactly the facts the corrections need.
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.GluingDatum
open DraismaVargas.Infrastructure.GraphContraction
open DraismaVargas.Infrastructure.GluingContraction
open DraismaVargas.Infrastructure.ContractionRamification
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.MarkedCountGeneral.DivalentContraction

/-! ## 1.  Normalizing a relabelling inside blocks -/

namespace BlockNormalize

variable {d : ℕ}

/-- The relation of a relabelled partition, read back. -/
theorem relabel_rel_iff' (P : SheetPartition d) (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    (P.relabel σ).Rel i j ↔ P.Rel (σ.symm i) (σ.symm j) := by
  conv_lhs => rw [← σ.apply_symm_apply i, ← σ.apply_symm_apply j]
  exact SheetPartition.relabel_rel_iff P σ _ _

/-- Transfer of a relation through a literal relabelling. -/
theorem rel_of_relabel {P Q : SheetPartition d} {σ : Equiv.Perm (Fin d)} (h : Q = P.relabel σ)
    (i j : Fin d) : P.Rel (σ.symm i) j ↔ Q.Rel i (σ j) := by
  rw [h, relabel_rel_iff', Equiv.symm_apply_apply]

/-- **The normalized relabelling**: if `Q` has the blocks of `P` relabelled by `σ`, then `σ`
corrected inside the blocks of `Q` relabels `P` to `Q` literally
(`PartitionNormalization.permutation`). -/
noncomputable def perm (P Q : SheetPartition d) (σ : Equiv.Perm (Fin d))
    (h : ∀ i j, Q.Rel i j ↔ P.Rel (σ.symm i) (σ.symm j)) : Equiv.Perm (Fin d) :=
  σ.trans (PartitionNormalization.permutation (P.relabel σ) Q
    (fun i j ↦ (relabel_rel_iff' P σ i j).trans (h i j).symm))

/-- The normalized relabelling relabels `P` to `Q` literally. -/
theorem perm_eq (P Q : SheetPartition d) (σ : Equiv.Perm (Fin d))
    (h : ∀ i j, Q.Rel i j ↔ P.Rel (σ.symm i) (σ.symm j)) : Q = P.relabel (perm P Q σ h) := by
  unfold perm
  rw [← SheetPartition.relabel_relabel]
  exact (PartitionNormalization.relabel_eq (P.relabel σ) Q
    (fun i j ↦ (relabel_rel_iff' P σ i j).trans (h i j).symm)).symm

/-- The normalized relabelling agrees with `σ` inside the blocks of `Q`. -/
theorem perm_rel (P Q : SheetPartition d) (σ : Equiv.Perm (Fin d))
    (h : ∀ i j, Q.Rel i j ↔ P.Rel (σ.symm i) (σ.symm j)) (s : Fin d) :
    Q.Rel (perm P Q σ h s) (σ s) := by
  have hSame : (P.relabel σ).SameBlocks Q :=
    fun i j ↦ (relabel_rel_iff' P σ i j).trans (h i j).symm
  exact (hSame _ _).mp (PartitionNormalization.permutation_rel (P.relabel σ) Q hSame (σ s))

end BlockNormalize

/-! ## 2.  One site: the merged vertex, the other edge and the sides -/

namespace DivalentContraction.Site

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree} (S : Site data)

/-- The merged vertex of the contraction. -/
abbrev wallV : S.T'.V := ⟨(S.c : target.V × target.V).1, fst_ne_snd S.c⟩

/-- The image of the other edge at `x`. -/
noncomputable abbrev oBar : S.T'.edges :=
  foldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne ⟨S.other, S.other_ne⟩

/-- The natural placement: a wall occurrence is on the fresh side when its unfolding meets the
second end of `c`. -/
noncomputable abbrev side : S.T'.edges → Bool :=
  IncomingTargetExpansion.right (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne

/-- Whether `x` is the second end of `c`. -/
noncomputable abbrev xFresh : Bool := decide (S.x = (S.c : target.V × target.V).2)

/-- `ō` is at the merged vertex. -/
theorem oBar_mem : S.oBar ∈ incidentEdges (target := S.T') S.wallV := by
  refine foldEdge_mem_incidentEdges_merge rfl (fst_ne_snd S.c) S.hOne S.other_ne ?_
  rcases S.x_eq_or with h | h
  · exact Finset.mem_union_left _ (h ▸ S.other_mem)
  · exact Finset.mem_union_right _ (h ▸ S.other_mem)

/-- `ō` unfolds to the other edge at `x`. -/
theorem unfold_oBar :
    unfoldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne S.oBar = S.other :=
  unfoldEdge_foldEdge rfl (fst_ne_snd S.c) S.hOne _

/-- The side of `ō` is the side of `x`. -/
theorem side_oBar : S.side S.oBar = S.xFresh := by
  unfold side IncomingTargetExpansion.right xFresh
  rw [S.unfold_oBar]
  refine decide_eq_decide.mpr ?_
  rw [← mem_incidentEdges_iff]
  constructor
  · intro h
    rcases S.c_ends with h' | h'
    · rw [h'.2] at h; exact absurd h S.other_not_mem_w
    · exact h'.2.symm
  · intro h
    exact h ▸ S.other_mem

/-- **The side of every other wall occurrence is the side of `w`.** -/
theorem side_of_ne {e : S.T'.edges} (he : e ∈ incidentEdges (target := S.T') S.wallV)
    (hne : e ≠ S.oBar) : S.side e = !S.xFresh := by
  have htc : unfoldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne e ≠ S.c :=
    unfoldEdge_ne_contracted rfl (fst_ne_snd S.c) S.hOne e
  have hto : unfoldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne e ≠ S.other := by
    intro h
    apply hne
    rw [← foldEdge_unfoldEdge rfl (fst_ne_snd S.c) S.hOne e htc]
    exact congrArg _ (Subtype.ext h)
  have hf := fold_unfoldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne e
  have hEnds : unfoldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne e ∈
        incidentEdges (S.c : target.V × target.V).1 ∨
      unfoldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne e ∈
        incidentEdges (S.c : target.V × target.V).2 := by
    rcases (mem_incidentEdges_iff _ e).mp he with h | h
    · have h1 := (congrArg Prod.fst hf).trans h
      rcases (fold_eq_iff target _ _ _).mp h1 with h2 | ⟨-, h2⟩
      · exact Or.inl ((mem_incidentEdges_iff _ _).mpr (Or.inl h2))
      · exact Or.inr ((mem_incidentEdges_iff _ _).mpr (Or.inl h2))
    · have h1 := (congrArg Prod.snd hf).trans h
      rcases (fold_eq_iff target _ _ _).mp h1 with h2 | ⟨-, h2⟩
      · exact Or.inl ((mem_incidentEdges_iff _ _).mpr (Or.inr h2))
      · exact Or.inr ((mem_incidentEdges_iff _ _).mpr (Or.inr h2))
  have hNotX : unfoldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne e ∉ incidentEdges S.x :=
    fun h ↦ (S.eq_c_or_other h).elim htc hto
  have key : unfoldEdge (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne e ∈
      incidentEdges (S.c : target.V × target.V).2 ↔ ¬ S.x = (S.c : target.V × target.V).2 := by
    rcases S.c_ends with h' | h'
    · have hx : S.x ≠ (S.c : target.V × target.V).2 := by rw [h'.2]; exact S.w_ne_x.symm
      refine ⟨fun _ ↦ hx, fun _ ↦ ?_⟩
      rcases hEnds with h | h
      · exact absurd (h'.1 ▸ h) hNotX
      · exact h
    · exact ⟨fun h hx ↦ hNotX (by rw [hx]; exact h), fun h ↦ absurd h'.2.symm h⟩
  unfold side IncomingTargetExpansion.right xFresh
  rw [← decide_not]
  exact decide_eq_decide.mpr ((mem_incidentEdges_iff _ _).symm.trans key)

/-- A placement of the wall occurrences (`M11WallExhaustion`'s placement disjunction). -/
abbrev Placed (sec : S.T'.edges → Bool) : Prop :=
  (∀ e ∈ incidentEdges (target := S.T') S.wallV, S.side e = sec e) ∨
    (∀ e ∈ incidentEdges (target := S.T') S.wallV, S.side e = !(sec e))

/-- The local resolution `data` presents at a placement. -/
noncomputable abbrev res (sec : S.T'.edges → Bool) (hP : S.Placed sec) :
    ResolutionM11.LocalResolution degree :=
  M11WallExhaustion.incomingResolution data (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne sec hP

/-- **The regrown occurrence carries the partition of `c`.** -/
theorem res_newEdge (hConn : graph_connected target) (hGenus : genus target = 0)
    (sec : S.T'.edges → Bool) (hP : S.Placed sec) :
    (S.res sec hP).newEdge = data.edgePartition S.c :=
  M11IncomingOuterPartitions.transported_edgePartition_new data rfl (fst_ne_snd S.c) S.hOne sec hP
    hConn hGenus

/-- **The two expanded endpoints carry the partitions of `x` and `w`**, `x` on the side of `ō`. -/
theorem res_ends (sec : S.T'.edges → Bool) (hP : S.Placed sec) :
    (S.res sec hP).left =
        (if sec S.oBar = true then data.vertexPartition S.w else data.vertexPartition S.x) ∧
      (S.res sec hP).right =
        (if sec S.oBar = true then data.vertexPartition S.x else data.vertexPartition S.w) := by
  have hpair := M11IncomingOuterPartitions.transported_endpointPartitions data (contracted := S.c)
    rfl (fst_ne_snd S.c) S.hOne sec hP
  have hne := fst_ne_snd S.c
  by_cases hAll : ∀ e ∈ incidentEdges (target := S.T') S.wallV, S.side e = sec e
  · rw [ite_eq_left hAll] at hpair
    have hL : (S.res sec hP).left = data.vertexPartition (S.c : target.V × target.V).1 :=
      congrArg Prod.fst hpair
    have hR : (S.res sec hP).right = data.vertexPartition (S.c : target.V × target.V).2 :=
      congrArg Prod.snd hpair
    have hF : sec S.oBar = S.xFresh := (hAll _ S.oBar_mem).symm.trans S.side_oBar
    rw [hF]
    rcases S.c_ends with h' | h'
    · rw [show S.xFresh = false from decide_eq_false fun h ↦ hne (h'.1.trans h)]
      exact ⟨hL.trans (congrArg _ h'.1), hR.trans (congrArg _ h'.2)⟩
    · rw [show S.xFresh = true from decide_eq_true h'.2.symm]
      exact ⟨hL.trans (congrArg _ h'.1), hR.trans (congrArg _ h'.2)⟩
  · rw [ite_eq_right hAll] at hpair
    have hL : (S.res sec hP).left = data.vertexPartition (S.c : target.V × target.V).2 :=
      congrArg Prod.fst hpair
    have hR : (S.res sec hP).right = data.vertexPartition (S.c : target.V × target.V).1 :=
      congrArg Prod.snd hpair
    have hF : sec S.oBar = !S.xFresh := by
      have h := (hP.resolve_left hAll) _ S.oBar_mem
      rw [S.side_oBar] at h
      rw [h, Bool.not_not]
    rw [hF]
    rcases S.c_ends with h' | h'
    · rw [show S.xFresh = false from decide_eq_false fun h ↦ hne (h'.1.trans h)]
      exact ⟨hL.trans (congrArg _ h'.2), hR.trans (congrArg _ h'.1)⟩
    · rw [show S.xFresh = true from decide_eq_true h'.2.symm]
      exact ⟨hL.trans (congrArg _ h'.2), hR.trans (congrArg _ h'.1)⟩

/-- The merged partition, read on `w`. -/
theorem wall_rel_iff (i j : Fin degree) :
    (S.D.vertexPartition S.wallV).Rel i j ↔ (data.vertexPartition S.w).Rel i j := by
  rw [contractDatum_vertexPartition_merge]
  exact S.merged_rel_iff i j

/-- The partition of `ō` is that of the other edge. -/
theorem oBar_partition : S.D.edgePartition S.oBar = data.edgePartition S.other :=
  contractDatum_edgePartition_foldEdge data rfl (fst_ne_snd S.c) S.hOne _

end DivalentContraction.Site

/-! ## 3.  Two sites: the decoupled transport -/

namespace DivalentContraction

open Site

section TwoSites

variable {target₁ target₂ : CFGraph} {degree : ℕ} {data₁ : GluingDatum target₁ degree}
  {data₂ : GluingDatum target₂ degree} (S₁ : Site data₁) (S₂ : Site data₂)
  (φ : GeometricDatumIso S₁.D S₂.D)

/-- The placement of the second site read through `φ`. -/
noncomputable def pullSide : S₂.T'.edges → Bool := fun e ↦ S₁.side (φ.targetEdge.symm e)

variable {S₁ S₂ φ} (hWall : φ.targetVertex S₁.wallV = S₂.wallV)
  (hO : φ.targetEdge S₁.oBar = S₂.oBar)

include hWall in
/-- `φ` carries the wall occurrences to the wall occurrences. -/
theorem mem_wall_map (e : S₁.T'.edges) :
    φ.targetEdge e ∈ incidentEdges (target := S₂.T') S₂.wallV ↔
      e ∈ incidentEdges (target := S₁.T') S₁.wallV := by
  rw [mem_incidentEdges_iff, mem_incidentEdges_iff, ← hWall]
  exact φ.target_incident_map_iff e S₁.wallV

include hO in
/-- The pulled placement puts `ō` on the side of `x` of the first site. -/
theorem pullSide_oBar : pullSide S₁ S₂ φ S₂.oBar = S₁.xFresh := by
  unfold pullSide
  rw [← hO, Equiv.symm_apply_apply, S₁.side_oBar]

include hWall hO in
/-- **The pulled placement is a placement.** -/
theorem placed_pull : S₂.Placed (pullSide S₁ S₂ φ) := by
  have key : ∀ e ∈ incidentEdges (target := S₂.T') S₂.wallV,
      S₂.side e = (if e = S₂.oBar then S₂.xFresh else !S₂.xFresh) ∧
        pullSide S₁ S₂ φ e = (if e = S₂.oBar then S₁.xFresh else !S₁.xFresh) := by
    intro e he
    have he₁ : φ.targetEdge.symm e ∈ incidentEdges (target := S₁.T') S₁.wallV := by
      rw [← mem_wall_map hWall, Equiv.apply_symm_apply]; exact he
    by_cases h : e = S₂.oBar
    · subst h
      rw [ite_eq_left rfl, ite_eq_left rfl]
      exact ⟨S₂.side_oBar, pullSide_oBar hO⟩
    · rw [ite_eq_right h, ite_eq_right h]
      refine ⟨S₂.side_of_ne he h, S₁.side_of_ne he₁ fun h' ↦ h ?_⟩
      rw [← hO, ← h', Equiv.apply_symm_apply]
  by_cases hx : S₁.xFresh = S₂.xFresh
  · left
    intro e he
    rw [(key e he).1, (key e he).2, hx]
  · right
    intro e he
    rw [(key e he).1, (key e he).2]
    have hx' : S₂.xFresh = !S₁.xFresh := by
      cases h₁ : S₁.xFresh <;> cases h₂ : S₂.xFresh <;> simp_all
    split_ifs <;> simp [hx']

/-- The natural placement is a placement. -/
theorem placed_side (S : Site data₁) : S.Placed S.side := Or.inl fun _ _ ↦ rfl

/-! ### The relations `φ` transports -/

include hWall in
/-- The partition of `w`, read through `φ`'s permutation at the merged vertex. -/
theorem wall_rel_map (i j : Fin degree) :
    (data₂.vertexPartition S₂.w).Rel i j ↔
      (data₁.vertexPartition S₁.w).Rel ((φ.vertexPerm S₁.wallV).symm i)
        ((φ.vertexPerm S₁.wallV).symm j) := by
  have h := φ.vertexPartition S₁.wallV
  rw [hWall] at h
  rw [← S₂.wall_rel_iff, h, BlockNormalize.relabel_rel_iff', S₁.wall_rel_iff]

include hO in
/-- The partition of the other edge, read through `φ`'s permutation at `ō`. -/
theorem other_rel_map (i j : Fin degree) :
    (data₂.edgePartition S₂.other).Rel i j ↔
      (data₁.edgePartition S₁.other).Rel ((φ.edgePerm S₁.oBar).symm i)
        ((φ.edgePerm S₁.oBar).symm j) := by
  have h := φ.edgePartition S₁.oBar
  rw [hO, S₂.oBar_partition, S₁.oBar_partition] at h
  rw [h, BlockNormalize.relabel_rel_iff']

include hO in
/-- The partition of `x`, read through `φ`'s permutation at `ō`. -/
theorem x_rel_map (i j : Fin degree) :
    (data₂.vertexPartition S₂.x).Rel i j ↔
      (data₁.vertexPartition S₁.x).Rel ((φ.edgePerm S₁.oBar).symm i)
        ((φ.edgePerm S₁.oBar).symm j) := by
  rw [← S₂.other_rel_iff, other_rel_map hO, S₁.other_rel_iff]

include hO in
/-- The partition of `c`, read through `φ`'s permutation at `ō`. -/
theorem c_rel_map (i j : Fin degree) :
    (data₂.edgePartition S₂.c).Rel i j ↔
      (data₁.edgePartition S₁.c).Rel ((φ.edgePerm S₁.oBar).symm i)
        ((φ.edgePerm S₁.oBar).symm j) := by
  rw [S₂.c_rel_iff, x_rel_map hO, S₁.c_rel_iff]

include hWall in
/-- **Compatibility at the merged vertex, read on `w`.** -/
theorem compat_w {e : S₁.T'.edges} (he : e ∈ incidentEdges (target := S₁.T') S₁.wallV)
    (sheet : Fin degree) :
    (data₂.vertexPartition S₂.w).Rel (φ.edgePerm e sheet) (φ.vertexPerm S₁.wallV sheet) := by
  have h := φ.compatible e S₁.wallV ((mem_incidentEdges_iff _ _).mp he) sheet
  rw [wall_rel_map hWall, Equiv.symm_apply_apply]
  exact (S₁.wall_rel_iff _ _).mp h

/-! ### The three corrected permutations -/

/-- The permutation over `x`. -/
noncomputable def ξ : Equiv.Perm (Fin degree) :=
  BlockNormalize.perm (data₁.vertexPartition S₁.x) (data₂.vertexPartition S₂.x)
    (φ.edgePerm S₁.oBar) (x_rel_map hO)

/-- The permutation over `c`. -/
noncomputable def ν : Equiv.Perm (Fin degree) :=
  BlockNormalize.perm (data₁.edgePartition S₁.c) (data₂.edgePartition S₂.c)
    (φ.edgePerm S₁.oBar) (c_rel_map hO)

/-- The permutation over `w`. -/
noncomputable def ω : Equiv.Perm (Fin degree) :=
  BlockNormalize.perm (data₁.vertexPartition S₁.w) (data₂.vertexPartition S₂.w)
    (φ.vertexPerm S₁.wallV) (wall_rel_map hWall)

/-- The permutation on the retained wall copy. -/
noncomputable def oldPerm : Equiv.Perm (Fin degree) :=
  if S₁.xFresh = true then ω hWall else ξ hO

/-- The permutation on the fresh vertex. -/
noncomputable def freshPerm : Equiv.Perm (Fin degree) :=
  if S₁.xFresh = true then ξ hO else ω hWall

include hWall in
/-- The corrected permutation over `x` agrees with `φ`'s at the merged vertex, on `w`. -/
theorem ξ_w (sheet : Fin degree) :
    (data₂.vertexPartition S₂.w).Rel (ξ hO sheet) (φ.vertexPerm S₁.wallV sheet) :=
  (S₂.x_refines_w _ _ (BlockNormalize.perm_rel _ _ _ _ sheet)).trans
    (compat_w hWall S₁.oBar_mem sheet)

/-- The corrected permutation over `w` agrees with `φ`'s at the merged vertex, on `w`. -/
theorem ω_w (sheet : Fin degree) :
    (data₂.vertexPartition S₂.w).Rel (ω hWall sheet) (φ.vertexPerm S₁.wallV sheet) :=
  BlockNormalize.perm_rel _ _ _ _ sheet

/-- The two resolutions, at the natural and the pulled placements. -/
noncomputable abbrev res₁ : ResolutionM11.LocalResolution degree := S₁.res S₁.side (placed_side S₁)

/-- The resolution of the second site at the pulled placement. -/
noncomputable abbrev res₂ : ResolutionM11.LocalResolution degree :=
  S₂.res (pullSide S₁ S₂ φ) (placed_pull hWall hO)

/-- The retained endpoint of the first resolution. -/
theorem res₁_left : (res₁ (S₁ := S₁)).left =
    if S₁.xFresh = true then data₁.vertexPartition S₁.w else data₁.vertexPartition S₁.x := by
  rw [(S₁.res_ends _ _).1, S₁.side_oBar]

/-- The fresh endpoint of the first resolution. -/
theorem res₁_right : (res₁ (S₁ := S₁)).right =
    if S₁.xFresh = true then data₁.vertexPartition S₁.x else data₁.vertexPartition S₁.w := by
  rw [(S₁.res_ends _ _).2, S₁.side_oBar]

/-- The retained endpoint of the second resolution. -/
theorem res₂_left : (res₂ hWall hO).left =
    if S₁.xFresh = true then data₂.vertexPartition S₂.w else data₂.vertexPartition S₂.x := by
  rw [(S₂.res_ends _ _).1, pullSide_oBar hO]

/-- The fresh endpoint of the second resolution. -/
theorem res₂_right : (res₂ hWall hO).right =
    if S₁.xFresh = true then data₂.vertexPartition S₂.x else data₂.vertexPartition S₂.w := by
  rw [(S₂.res_ends _ _).2, pullSide_oBar hO]

/-! ### The literal relabellings -/

/-- The retained endpoints are relabelled by `oldPerm`. -/
theorem left_relabel : (res₂ hWall hO).left = (res₁ (S₁ := S₁)).left.relabel (oldPerm hWall hO) := by
  rw [res₂_left, res₁_left]
  unfold oldPerm
  split_ifs
  · exact BlockNormalize.perm_eq _ _ _ _
  · exact BlockNormalize.perm_eq _ _ _ _

/-- The fresh endpoints are relabelled by `freshPerm`. -/
theorem right_relabel :
    (res₂ hWall hO).right = (res₁ (S₁ := S₁)).right.relabel (freshPerm hWall hO) := by
  rw [res₂_right, res₁_right]
  unfold freshPerm
  split_ifs
  · exact BlockNormalize.perm_eq _ _ _ _
  · exact BlockNormalize.perm_eq _ _ _ _

variable (hConn₁ : graph_connected target₁) (hGenus₁ : genus target₁ = 0)
  (hConn₂ : graph_connected target₂) (hGenus₂ : genus target₂ = 0)

include hConn₁ hGenus₁ hConn₂ hGenus₂ in
/-- The regrown occurrences are relabelled by `ν`. -/
theorem newEdge_relabel :
    (res₂ hWall hO).newEdge = (res₁ (S₁ := S₁)).newEdge.relabel (ν hO) := by
  rw [S₂.res_newEdge hConn₂ hGenus₂, S₁.res_newEdge hConn₁ hGenus₁]
  exact BlockNormalize.perm_eq _ _ _ _

/-- The regrown occurrence's permutation, read on the `x` and `w` partitions of the second site. -/
theorem ν_x (sheet : Fin degree) :
    (data₂.vertexPartition S₂.x).Rel (ν hO sheet) (ξ hO sheet) :=
  ((S₂.c_rel_iff _ _).mp (BlockNormalize.perm_rel _ _ _ _ sheet)).trans
    (BlockNormalize.perm_rel _ _ _ _ sheet).symm

include hWall in
/-- The regrown occurrence's permutation agrees with `ω` on `w`. -/
theorem ν_w (sheet : Fin degree) :
    (data₂.vertexPartition S₂.w).Rel (ν hO sheet) (ω hWall sheet) :=
  ((edgePartition_refines_of_mem_incidentEdges data₂ S₂.w S₂.c S₂.c_mem_w _ _
    (BlockNormalize.perm_rel _ _ _ _ sheet)).trans (compat_w hWall S₁.oBar_mem sheet)).trans
      (ω_w hWall sheet).symm

include hWall in
/-- The merged agreement of a permutation, from its agreement on `w`. -/
theorem merged_of_w {σ : Equiv.Perm (Fin degree)}
    (h : ∀ sheet, (data₂.vertexPartition S₂.w).Rel (σ sheet) (φ.vertexPerm S₁.wallV sheet))
    (sheet : Fin degree) :
    (S₁.D.vertexPartition S₁.wallV).Rel ((φ.vertexPerm S₁.wallV).symm (σ sheet)) sheet := by
  refine (S₁.wall_rel_iff _ _).mpr ?_
  have h' := (wall_rel_map hWall _ _).mp (h sheet)
  rwa [Equiv.symm_apply_apply] at h'

include hConn₁ hGenus₁ hConn₂ hGenus₂ in
/-- **The decoupled transport of `φ`.** -/
noncomputable def transport :
    ResolutionExpansionFree.TransportFree φ S₁.wallV S₂.wallV S₁.side (pullSide S₁ S₂ φ)
      (res₁ (S₁ := S₁)) (res₂ hWall hO) where
  oldPerm := oldPerm hWall hO
  freshPerm := freshPerm hWall hO
  newPerm := ν hO
  wall_map := hWall
  side_map e := by unfold pullSide; rw [Equiv.symm_apply_apply]
  old_merged := merged_of_w hWall (σ := oldPerm hWall hO) fun sheet ↦ by
    unfold oldPerm; split_ifs
    · exact ω_w hWall sheet
    · exact ξ_w hWall hO sheet
  fresh_merged := merged_of_w hWall (σ := freshPerm hWall hO) fun sheet ↦ by
    unfold freshPerm; split_ifs
    · exact ξ_w hWall hO sheet
    · exact ω_w hWall sheet
  left_relabel := left_relabel hWall hO
  right_relabel := right_relabel hWall hO
  newEdge_relabel := newEdge_relabel hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂
  newEdge_old sheet := by
    refine (BlockNormalize.rel_of_relabel (left_relabel hWall hO) _ _).mpr ?_
    rw [res₂_left]
    unfold oldPerm; split_ifs
    · exact ν_w hWall hO sheet
    · exact ν_x hO sheet
  newEdge_fresh sheet := by
    refine (BlockNormalize.rel_of_relabel (right_relabel hWall hO) _ _).mpr ?_
    rw [res₂_right]
    unfold freshPerm; split_ifs
    · exact ν_x hO sheet
    · exact ν_w hWall hO sheet
  endpoint_compatible e hInc sheet := by
    have he : e ∈ incidentEdges (target := S₁.T') S₁.wallV := (mem_incidentEdges_iff _ _).mpr hInc
    by_cases h : e = S₁.oBar
    · subst h
      rw [S₁.side_oBar]
      cases hF : S₁.xFresh
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine (BlockNormalize.rel_of_relabel (left_relabel hWall hO) _ _).mpr ?_
        rw [res₂_left]
        simp only [oldPerm, hF, Bool.false_eq_true, ↓reduceIte]
        exact (BlockNormalize.perm_rel _ _ _ _ sheet).symm
      · simp only [↓reduceIte]
        refine (BlockNormalize.rel_of_relabel (right_relabel hWall hO) _ _).mpr ?_
        rw [res₂_right]
        simp only [freshPerm, hF, ↓reduceIte]
        exact (BlockNormalize.perm_rel _ _ _ _ sheet).symm
    · rw [S₁.side_of_ne he h]
      cases hF : S₁.xFresh
      · simp only [Bool.not_false, ↓reduceIte]
        refine (BlockNormalize.rel_of_relabel (right_relabel hWall hO) _ _).mpr ?_
        rw [res₂_right]
        simp only [freshPerm, hF, Bool.false_eq_true, ↓reduceIte]
        exact (compat_w hWall he sheet).trans (ω_w hWall sheet).symm
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine (BlockNormalize.rel_of_relabel (left_relabel hWall hO) _ _).mpr ?_
        rw [res₂_left]
        simp only [oldPerm, hF, ↓reduceIte]
        exact (compat_w hWall he sheet).trans (ω_w hWall sheet).symm

/-! ### The extension and its two squares -/

/-- The normalization of the first datum onto the resolution expansion of its contraction. -/
noncomputable abbrev norm₁ := M11WallExhaustion.datumIso data₁ (contracted := S₁.c) rfl
  (fst_ne_snd S₁.c) S₁.hOne S₁.side (placed_side S₁) hConn₁ hGenus₁

/-- The normalization of the second datum, at the pulled placement. -/
noncomputable abbrev norm₂ := M11WallExhaustion.datumIso data₂ (contracted := S₂.c) rfl
  (fst_ne_snd S₂.c) S₂.hOne (pullSide S₁ S₂ φ) (placed_pull hWall hO) hConn₂ hGenus₂

/-- The lift of `φ` between the two resolution expansions. -/
noncomputable abbrev lift := ResolutionExpansionFree.liftFree φ S₁.wallV S₂.wallV S₁.side
  (pullSide S₁ S₂ φ) (res₁ (S₁ := S₁)) (res₂ hWall hO)
  (M11WallExhaustion.incomingOldCompatible data₁ (contracted := S₁.c) rfl (fst_ne_snd S₁.c)
    S₁.hOne S₁.side (placed_side S₁) hConn₁ hGenus₁)
  (M11WallExhaustion.incomingOldCompatible data₂ (contracted := S₂.c) rfl (fst_ne_snd S₂.c)
    S₂.hOne (pullSide S₁ S₂ φ) (placed_pull hWall hO) hConn₂ hGenus₂)
  (transport hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂)

/-- **The extension of `φ` over the two contracted edges.** -/
noncomputable def extend : GeometricDatumIso data₁ data₂ :=
  (norm₁ hConn₁ hGenus₁).trans ((lift hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂).trans
    (norm₂ hWall hO hConn₂ hGenus₂).symm)

/-- **The vertex square**: the extension commutes with the contractions. -/
theorem extend_vmap (X : data₁.SourceVertex) :
    S₂.vmap ((extend hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂).sourceVertexEquiv X) =
      φ.sourceVertexEquiv (S₁.vmap X) := by
  have h₁ := M11WallExhaustion.sourceVertexMap_datumIso data₁ (contracted := S₁.c) rfl
    (fst_ne_snd S₁.c) S₁.hOne S₁.side (placed_side S₁) hConn₁ hGenus₁ X
  have hL := ResolutionExpansionFree.sourceVertexMap_liftFree φ S₁.wallV S₂.wallV S₁.side
    (pullSide S₁ S₂ φ) (res₁ (S₁ := S₁)) (res₂ hWall hO)
    (M11WallExhaustion.incomingOldCompatible data₁ (contracted := S₁.c) rfl (fst_ne_snd S₁.c)
      S₁.hOne S₁.side (placed_side S₁) hConn₁ hGenus₁)
    (M11WallExhaustion.incomingOldCompatible data₂ (contracted := S₂.c) rfl (fst_ne_snd S₂.c)
      S₂.hOne (pullSide S₁ S₂ φ) (placed_pull hWall hO) hConn₂ hGenus₂)
    (transport hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂)
    ((norm₁ hConn₁ hGenus₁).sourceVertexEquiv X)
  have h₂ := M11WallExhaustion.sourceVertexMap_datumIso data₂ (contracted := S₂.c) rfl
    (fst_ne_snd S₂.c) S₂.hOne (pullSide S₁ S₂ φ) (placed_pull hWall hO) hConn₂ hGenus₂
    ((extend hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂).sourceVertexEquiv X)
  refine h₂.trans ?_
  change GlobalResolution.sourceVertexMap _ _ _ _ _
      ((norm₂ hWall hO hConn₂ hGenus₂).sourceVertexEquiv
        ((norm₂ hWall hO hConn₂ hGenus₂).sourceVertexEquiv.symm
          ((lift hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂).sourceVertexEquiv
            ((norm₁ hConn₁ hGenus₁).sourceVertexEquiv X)))) = _
  rw [Equiv.apply_symm_apply]
  exact hL.symm.trans (congrArg φ.sourceVertexEquiv h₁.symm)

/-- **The edge square**: on the occurrences away from the contracted edges, the extension is
`φ` read through the contractions. -/
theorem extend_emb (f : S₁.D.SourceEdge) :
    (extend hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂).sourceEdgeEquiv
        (WallDegeneration.sourceEdgeEmbedding data₁ (contracted := S₁.c) rfl (fst_ne_snd S₁.c)
          S₁.hOne f) =
      WallDegeneration.sourceEdgeEmbedding data₂ (contracted := S₂.c) rfl (fst_ne_snd S₂.c)
        S₂.hOne (φ.sourceEdgeEquiv f) := by
  have h₁ := M11WallExhaustion.retainedSourceEdge_datumIso data₁ (contracted := S₁.c) rfl
    (fst_ne_snd S₁.c) S₁.hOne S₁.side (placed_side S₁) hConn₁ hGenus₁ f
  have hL := ResolutionExpansionFree.retainedSourceEdge_liftFree φ S₁.wallV S₂.wallV S₁.side
    (pullSide S₁ S₂ φ) (res₁ (S₁ := S₁)) (res₂ hWall hO)
    (M11WallExhaustion.incomingOldCompatible data₁ (contracted := S₁.c) rfl (fst_ne_snd S₁.c)
      S₁.hOne S₁.side (placed_side S₁) hConn₁ hGenus₁)
    (M11WallExhaustion.incomingOldCompatible data₂ (contracted := S₂.c) rfl (fst_ne_snd S₂.c)
      S₂.hOne (pullSide S₁ S₂ φ) (placed_pull hWall hO) hConn₂ hGenus₂)
    (transport hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂) f
  have h₂ := M11WallExhaustion.retainedSourceEdge_datumIso data₂ (contracted := S₂.c) rfl
    (fst_ne_snd S₂.c) S₂.hOne (pullSide S₁ S₂ φ) (placed_pull hWall hO) hConn₂ hGenus₂
    (φ.sourceEdgeEquiv f)
  change (norm₂ hWall hO hConn₂ hGenus₂).sourceEdgeEquiv.symm
      ((lift hWall hO hConn₁ hGenus₁ hConn₂ hGenus₂).sourceEdgeEquiv
        ((norm₁ hConn₁ hGenus₁).sourceEdgeEquiv _)) = _
  rw [h₁, hL, Equiv.symm_apply_eq]
  exact h₂.symm

end TwoSites

/-! ## 4.  What the two squares give -/

section Squares

variable {target₁ target₂ : CFGraph} {degree : ℕ} {data₁ : GluingDatum target₁ degree}
  {data₂ : GluingDatum target₂ degree} {S₁ : Site data₁} {S₂ : Site data₂}
  {φ : GeometricDatumIso S₁.D S₂.D} {Ψ : GeometricDatumIso data₁ data₂}
  (hV : ∀ X, S₂.vmap (Ψ.sourceVertexEquiv X) = φ.sourceVertexEquiv (S₁.vmap X))
  (hE : ∀ f, Ψ.sourceEdgeEquiv (WallDegeneration.sourceEdgeEmbedding data₁ (contracted := S₁.c)
      rfl (fst_ne_snd S₁.c) S₁.hOne f) =
    WallDegeneration.sourceEdgeEmbedding data₂ (contracted := S₂.c) rfl (fst_ne_snd S₂.c)
      S₂.hOne (φ.sourceEdgeEquiv f))

/-- The embedding read back through the edge map. -/
theorem emap_of_eq_emb {S : Site data₂} {f : data₂.SourceEdge} {g : S.D.SourceEdge}
    (hf : f = WallDegeneration.sourceEdgeEmbedding data₂ (contracted := S.c) rfl (fst_ne_snd S.c)
      S.hOne g) (h : f.1.1 ≠ S.c) : S.emap ⟨f, h⟩ = g := by
  subst hf
  exact (ContractionFibre.sourceEdgeEquiv data₂ (contracted := S.c) rfl (fst_ne_snd S.c)
    S.hOne).apply_symm_apply g

include hE in
/-- The edge square, read on an occurrence away from `c₁`. -/
theorem sq_emb (e : {e : data₁.SourceEdge // e.1.1 ≠ S₁.c}) :
    Ψ.sourceEdgeEquiv e.1 = WallDegeneration.sourceEdgeEmbedding data₂ (contracted := S₂.c) rfl
      (fst_ne_snd S₂.c) S₂.hOne (φ.sourceEdgeEquiv (S₁.emap e)) := by
  have h := hE (S₁.emap e)
  rwa [WallDegeneration.sourceEdgeEmbedding_sourceEdgeMap] at h

include hE in
/-- Occurrences away from `c₁` go to occurrences away from `c₂`. -/
theorem sq_ne_c (e : {e : data₁.SourceEdge // e.1.1 ≠ S₁.c}) : (Ψ.sourceEdgeEquiv e.1).1.1 ≠ S₂.c := by
  rw [sq_emb hE e]
  exact WallDegeneration.sourceEdgeEmbedding_ne_contracted _ _ _ _ _

include hE in
/-- **The edge square, on the edge maps.** -/
theorem sq_emap (e : {e : data₁.SourceEdge // e.1.1 ≠ S₁.c}) :
    S₂.emap ⟨Ψ.sourceEdgeEquiv e.1, sq_ne_c hE e⟩ = φ.sourceEdgeEquiv (S₁.emap e) :=
  emap_of_eq_emb (sq_emb hE e) _

include hE in
/-- Target edges other than `c₁` go to target edges other than `c₂`. -/
theorem sq_targetEdge_ne {t : target₁.edges} (ht : t ≠ S₁.c) : Ψ.targetEdge t ≠ S₂.c :=
  sq_ne_c hE ⟨data₁.sourceEdge t ⟨0, data₁.degree_pos⟩, ht⟩

include hE in
/-- **The contracted edge goes to the contracted edge.** -/
theorem sq_targetEdge_c : Ψ.targetEdge S₁.c = S₂.c := by
  obtain ⟨t, ht⟩ := Ψ.targetEdge.surjective S₂.c
  by_cases h : t = S₁.c
  · rw [← h]; exact ht
  · exact absurd ht (sq_targetEdge_ne hE h)

/-- Incidence of target edges under an isomorphism. -/
theorem mem_incidentEdges_map {first : GluingDatum target₁ degree}
    {second : GluingDatum target₂ degree} (iso : GeometricDatumIso first second)
    (t : target₁.edges) (v : target₁.V) :
    iso.targetEdge t ∈ incidentEdges (iso.targetVertex v) ↔ t ∈ incidentEdges v := by
  rw [mem_incidentEdges_iff, mem_incidentEdges_iff]
  exact iso.target_incident_map_iff t v

include hE in
/-- **The other edge goes to the other edge**, when `φ` carries `ō` to `ō`. -/
theorem sq_targetEdge_other (hO : φ.targetEdge S₁.oBar = S₂.oBar) :
    Ψ.targetEdge S₁.other = S₂.other := by
  let e : {e : data₁.SourceEdge // e.1.1 ≠ S₁.c} :=
    ⟨data₁.sourceEdge S₁.other ⟨0, data₁.degree_pos⟩, S₁.other_ne⟩
  have h := congrArg (fun g : S₂.D.SourceEdge ↦ g.1.1) (sq_emap hE e)
  change foldEdge (contracted := S₂.c) rfl (fst_ne_snd S₂.c) S₂.hOne
      ⟨Ψ.targetEdge S₁.other, _⟩ = φ.targetEdge S₁.oBar at h
  rw [hO] at h
  exact congrArg Subtype.val (foldEdge_injective rfl (fst_ne_snd S₂.c) S₂.hOne h)

include hE in
/-- **`x` goes to `x`.** -/
theorem sq_targetVertex_x (hO : φ.targetEdge S₁.oBar = S₂.oBar) :
    Ψ.targetVertex S₁.x = S₂.x := by
  have hc : S₂.c ∈ incidentEdges (Ψ.targetVertex S₁.x) := by
    rw [← sq_targetEdge_c hE, mem_incidentEdges_map]; exact S₁.mem
  have ho : S₂.other ∈ incidentEdges (Ψ.targetVertex S₁.x) := by
    rw [← sq_targetEdge_other hE hO, mem_incidentEdges_map]; exact S₁.other_mem
  rcases S₂.eq_x_or_eq_w hc with h | h
  · exact h
  · exact absurd (h ▸ ho) S₂.other_not_mem_w

include hE in
/-- **The partner of an occurrence over `c` goes to the partner of its image.** -/
theorem sq_partner (hO : φ.targetEdge S₁.oBar = S₂.oBar) {e : data₁.SourceEdge}
    (h : e.1.1 = S₁.c) : Ψ.sourceEdgeEquiv (S₁.partner e) = S₂.partner (Ψ.sourceEdgeEquiv e) := by
  set X := data₁.sourceEndpoint S₁.x e.1.2
  have hY : (Ψ.sourceVertexEquiv X).1.1 = S₂.x := by
    change Ψ.targetVertex S₁.x = S₂.x
    exact sq_targetVertex_x hE hO
  have h₁ : Incident data₂ (Ψ.sourceEdgeEquiv e) (Ψ.sourceVertexEquiv X) :=
    (Ψ.incident_map_iff _ _).mpr (S₁.incident_c_x h)
  have h₂ : Incident data₂ (Ψ.sourceEdgeEquiv (S₁.partner e)) (Ψ.sourceVertexEquiv X) :=
    (Ψ.incident_map_iff _ _).mpr (S₁.incident_partner_x e)
  have hEt : (Ψ.sourceEdgeEquiv e).1.1 = S₂.c := by
    change Ψ.targetEdge e.1.1 = S₂.c
    rw [h]; exact sq_targetEdge_c hE
  have hPt : (Ψ.sourceEdgeEquiv (S₁.partner e)).1.1 = S₂.other := by
    change Ψ.targetEdge S₁.other = S₂.other
    exact sq_targetEdge_other hE hO
  have hEc : Ψ.sourceEdgeEquiv e = data₂.sourceEdge S₂.c (Ψ.sourceVertexEquiv X).1.2 := by
    rcases (S₂.incident_x_iff _ hY _).mp h₁ with h' | h'
    · exact h'
    · exact absurd (hEt.symm.trans (congrArg (fun f : data₂.SourceEdge ↦ f.1.1) h')) S₂.other_ne.symm
  have hPo : Ψ.sourceEdgeEquiv (S₁.partner e) =
      data₂.sourceEdge S₂.other (Ψ.sourceVertexEquiv X).1.2 := by
    rcases (S₂.incident_x_iff _ hY _).mp h₂ with h' | h'
    · exact absurd (hPt.symm.trans (congrArg (fun f : data₂.SourceEdge ↦ f.1.1) h')) S₂.other_ne
    · exact h'
  rw [hPo, hEc, S₂.partner_sourceEdge_c]

include hE in
/-- **The edge maps commute with the extension.** -/
theorem sq_edgeMap (hO : φ.targetEdge S₁.oBar = S₂.oBar) (e : data₁.SourceEdge) :
    S₂.edgeMap (Ψ.sourceEdgeEquiv e) = φ.sourceEdgeEquiv (S₁.edgeMap e) := by
  by_cases h : e.1.1 = S₁.c
  · have h₂ : (Ψ.sourceEdgeEquiv e).1.1 = S₂.c := by
      change Ψ.targetEdge e.1.1 = S₂.c
      rw [h]; exact sq_targetEdge_c hE
    unfold Site.edgeMap
    rw [S₁.mu_of_eq h, S₂.mu_of_eq h₂, ← sq_emap hE ⟨S₁.partner e, S₁.other_ne⟩]
    exact congrArg S₂.emap (Subtype.ext (sq_partner hE hO h).symm)
  · rw [S₁.edgeMap_of_ne h, S₂.edgeMap_of_ne (sq_ne_c hE ⟨e, h⟩)]
    exact sq_emap hE ⟨e, h⟩

end Squares

end DivalentContraction

/-! ## 5.  The extension of an isomorphism of drops -/

namespace DivalentContraction.Site

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree} (S : Site data)

/-- An occurrence over `c` goes to an occurrence over `ō`. -/
theorem edgeMap_target_of_c {e : data.SourceEdge} (h : e.1.1 = S.c) :
    (S.edgeMap e).1.1 = S.oBar := by
  unfold edgeMap
  rw [S.mu_of_eq h]
  rfl

/-- The far end of `c` folds to the merged vertex. -/
theorem fold_w : fold target (fst_ne_snd S.c) S.w = S.wallV := by
  rcases S.c_ends with h | h
  · rw [← h.2]; exact fold_self target _
  · rw [← h.1]; exact fold_a target _

end DivalentContraction.Site

namespace DropSmooth

open GenusSixExistence.Tripod.Gadget (subdivide)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}
  {s : Fin p} (hc : IsMarkedCubic core mark)
  {κ₁ κ₂ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree}
  (φ : TypedFrameIso (dropFrame' hc κ₁) (dropFrame' hc κ₂))
  (hg : φ.datum.sourceEdgeEquiv ((site κ₁ hc).edgeMap ((site κ₁ hc).fc (markHyp κ₁ hc)).1) =
    (site κ₂ hc).edgeMap ((site κ₂ hc).fc (markHyp κ₂ hc)).1)
  (hm : φ.datum.sourceVertexEquiv
      ((site κ₁ hc).vmap (Site.far (V κ₁) ((site κ₁ hc).fc (markHyp κ₁ hc)))) =
    (site κ₂ hc).vmap (Site.far (V κ₂) ((site κ₂ hc).fc (markHyp κ₂ hc))))

include hg in
/-- `φ` carries `ō` to `ō`. -/
theorem ext_hO : φ.datum.targetEdge (site κ₁ hc).oBar = (site κ₂ hc).oBar := by
  have h : φ.datum.targetEdge ((site κ₁ hc).edgeMap ((site κ₁ hc).fc (markHyp κ₁ hc)).1).1.1 =
      ((site κ₂ hc).edgeMap ((site κ₂ hc).fc (markHyp κ₂ hc)).1).1.1 :=
    congrArg (fun g : (site κ₂ hc).D.SourceEdge ↦ g.1.1) hg
  exact (congrArg φ.datum.targetEdge ((site κ₁ hc).edgeMap_target_of_c
    (e := ((site κ₁ hc).fc (markHyp κ₁ hc)).1) rfl).symm).trans
    (h.trans ((site κ₂ hc).edgeMap_target_of_c (e := ((site κ₂ hc).fc (markHyp κ₂ hc)).1) rfl))

include hm in
/-- `φ` fixes the merged vertex. -/
theorem ext_hWall : φ.datum.targetVertex (site κ₁ hc).wallV = (site κ₂ hc).wallV := by
  have h : φ.datum.targetVertex (fold _ (fst_ne_snd (site κ₁ hc).c)
      (Site.far (V κ₁) ((site κ₁ hc).fc (markHyp κ₁ hc))).1.1) =
      fold _ (fst_ne_snd (site κ₂ hc).c) (Site.far (V κ₂) ((site κ₂ hc).fc (markHyp κ₂ hc))).1.1 :=
    congrArg (fun X : (site κ₂ hc).D.SourceVertex ↦ X.1.1) hm
  have e₁ : fold _ (fst_ne_snd (site κ₁ hc).c)
      (Site.far (V κ₁) ((site κ₁ hc).fc (markHyp κ₁ hc))).1.1 = (site κ₁ hc).wallV :=
    (congrArg (fun X : κ₁.data.SourceVertex ↦ fold _ (fst_ne_snd (site κ₁ hc).c) X.1.1)
      ((site κ₁ hc).far_fc (markHyp κ₁ hc))).trans (Site.fold_w _)
  have e₂ : fold _ (fst_ne_snd (site κ₂ hc).c)
      (Site.far (V κ₂) ((site κ₂ hc).fc (markHyp κ₂ hc))).1.1 = (site κ₂ hc).wallV :=
    (congrArg (fun X : κ₂.data.SourceVertex ↦ fold _ (fst_ne_snd (site κ₂ hc).c) X.1.1)
      ((site κ₂ hc).far_fc (markHyp κ₂ hc))).trans (Site.fold_w _)
  exact (congrArg φ.datum.targetVertex e₁.symm).trans (h.trans e₂)

/-- **The extension of the datum isomorphism.** -/
noncomputable def extΨ : GeometricDatumIso κ₁.data κ₂.data :=
  DivalentContraction.extend (S₁ := site κ₁ hc) (S₂ := site κ₂ hc) (φ := φ.datum)
    (ext_hWall hc φ hm) (ext_hO hc φ hg) κ₁.fullDim.targetConnected κ₁.fullDim.targetGenus
    κ₂.fullDim.targetConnected κ₂.fullDim.targetGenus

/-- The extension commutes with the vertex maps of the two drops. -/
theorem ext_vmap (X : κ₁.data.SourceVertex) :
    (site κ₂ hc).vmap ((extΨ hc φ hg hm).sourceVertexEquiv X) =
      φ.datum.sourceVertexEquiv ((site κ₁ hc).vmap X) :=
  DivalentContraction.extend_vmap _ _ _ _ _ _ X

/-- The extension commutes with the edge embeddings of the two drops. -/
theorem ext_emb (f : (site κ₁ hc).D.SourceEdge) :
    (extΨ hc φ hg hm).sourceEdgeEquiv
        (WallDegeneration.sourceEdgeEmbedding κ₁.data (contracted := (site κ₁ hc).c) rfl
          (fst_ne_snd (site κ₁ hc).c) (site κ₁ hc).hOne f) =
      WallDegeneration.sourceEdgeEmbedding κ₂.data (contracted := (site κ₂ hc).c) rfl
        (fst_ne_snd (site κ₂ hc).c) (site κ₂ hc).hOne (φ.datum.sourceEdgeEquiv f) :=
  DivalentContraction.extend_emb _ _ _ _ _ _ f

/-- The extension carries `x₁` to `x₂`. -/
theorem ext_x : (extΨ hc φ hg hm).targetVertex (site κ₁ hc).x = (site κ₂ hc).x :=
  DivalentContraction.sq_targetVertex_x (ext_emb hc φ hg hm) (ext_hO hc φ hg)

/-- The edge map at `fc`, as the edge map of `fo`. -/
theorem edgeMap_fc (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree) :
    (site κ hc).edgeMap ((site κ hc).fc (markHyp κ hc)).1 =
      (site κ hc).emap ⟨((site κ hc).fo (markHyp κ hc)).1, (site κ hc).other_ne⟩ := by
  unfold Site.edgeMap
  rw [(site κ hc).mu_of_eq (e := ((site κ hc).fc (markHyp κ hc)).1) rfl]
  exact congrArg _ (Subtype.ext ((site κ hc).partner_sourceEdge_c _))

/-- **The extension carries `fo` to `fo`.** -/
theorem ext_fo : (extΨ hc φ hg hm).sourceEdgeEquiv ((site κ₁ hc).fo (markHyp κ₁ hc)).1 =
    ((site κ₂ hc).fo (markHyp κ₂ hc)).1 := by
  have h := DivalentContraction.sq_emap (ext_emb hc φ hg hm)
    ⟨((site κ₁ hc).fo (markHyp κ₁ hc)).1, (site κ₁ hc).other_ne⟩
  rw [← edgeMap_fc hc κ₁] at h
  exact congrArg Subtype.val (sourceEdgeMap_injective _ _ _ _ (h.trans (hg.trans (edgeMap_fc hc κ₂))))

/-- **The extension carries the dropped mark to the dropped mark.** -/
theorem ext_V : (extΨ hc φ hg hm).sourceVertexEquiv (V κ₁) = V κ₂ := by
  set Ψ := extΨ hc φ hg hm
  have hY : (Ψ.sourceVertexEquiv (V κ₁)).1.1 = (site κ₂ hc).x := ext_x hc φ hg hm
  have hInc : Incident κ₂.data ((site κ₂ hc).fo (markHyp κ₂ hc)).1 (Ψ.sourceVertexEquiv (V κ₁)) := by
    rw [← ext_fo hc φ hg hm]
    exact (Ψ.incident_map_iff _ _).mpr ((site κ₁ hc).incident_fo (markHyp κ₁ hc))
  rcases ((site κ₂ hc).incident_x_iff _ hY _).mp hInc with h | h
  · exact absurd (congrArg (fun f : κ₂.data.SourceEdge ↦ f.1.1) h) (site κ₂ hc).other_ne
  · have hRel : (κ₂.data.vertexPartition (site κ₂ hc).x).Rel (V κ₂).1.2
        (Ψ.sourceVertexEquiv (V κ₁)).1.2 :=
      ((site κ₂ hc).other_rel_iff _ _).mp ((sourceEdge_eq_iff κ₂.data _ _ _).mp h)
    refine ((κ₂.data.sourceEndpoint_eq_iff _ _ _).mpr ⟨hY.symm, hRel⟩).symm.trans ?_
    exact ((site κ₂ hc).eq_sourceEndpoint_x (V κ₂) rfl).symm

/-- **The extension carries `fc` to `fc`.** -/
theorem ext_fc : (extΨ hc φ hg hm).sourceEdgeEquiv ((site κ₁ hc).fc (markHyp κ₁ hc)).1 =
    ((site κ₂ hc).fc (markHyp κ₂ hc)).1 := by
  set Ψ := extΨ hc φ hg hm
  have hInc : Incident κ₂.data (Ψ.sourceEdgeEquiv ((site κ₁ hc).fc (markHyp κ₁ hc)).1) (V κ₂) := by
    rw [← ext_V hc φ hg hm]
    exact (Ψ.incident_map_iff _ _).mpr ((site κ₁ hc).incident_fc (markHyp κ₁ hc))
  have hT : (Ψ.sourceEdgeEquiv ((site κ₁ hc).fc (markHyp κ₁ hc)).1).1.1 = (site κ₂ hc).c :=
    DivalentContraction.sq_targetEdge_c (ext_emb hc φ hg hm)
  rcases ((site κ₂ hc).incident_x_iff _ rfl _).mp hInc with h | h
  · exact h
  · exact absurd (hT.symm.trans (congrArg (fun f : κ₂.data.SourceEdge ↦ f.1.1) h))
      (site κ₂ hc).other_ne.symm

/-- **Marks go to marks.** -/
theorem ext_mark (j : Fin (k + 1)) :
    (extΨ hc φ hg hm).sourceVertexEquiv (κ₁.markSource j) = κ₂.markSource j := by
  set Ψ := extΨ hc φ hg hm
  induction j using Fin.lastCases with
  | last => exact ext_V hc φ hg hm
  | cast j =>
    have h₁ := φ.mark j
    change φ.datum.sourceVertexEquiv ((site κ₁ hc).vmap (κ₁.markSource j.castSucc)) =
      (site κ₂ hc).vmap (κ₂.markSource j.castSucc) at h₁
    rw [← ext_vmap hc φ hg hm] at h₁
    refine ((site κ₂ hc).vmap_inj ?_ ?_).mp h₁
    · change Ψ.targetVertex (κ₁.markSource j.castSucc).1.1 ≠ (site κ₂ hc).x
      rw [← ext_x hc φ hg hm]
      exact fun h ↦ markSource_castSucc_ne κ₁ hc j (Ψ.targetVertex.injective h)
    · exact markSource_castSucc_ne κ₂ hc j

/-- The extension carries marks to marks. -/
theorem ext_mem_marks (Y : κ₁.data.SourceVertex) :
    (extΨ hc φ hg hm).sourceVertexEquiv Y ∈ M κ₂ ↔ Y ∈ M κ₁ := by
  simp only [M, markSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (extΨ hc φ hg hm).sourceVertexEquiv.injective ((ext_mark hc φ hg hm j).trans hj)⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, (ext_mark hc φ hg hm j).symm⟩

/-- **The surviving-edge map commutes with the extension.** -/
theorem ext_ndMap (e : NonDanglingEdge κ₁.data) :
    (site κ₂ hc).ndMap ((extΨ hc φ hg hm).nonDanglingEdgeEquiv κ₁.fullDim.valid.1 e) =
      φ.datum.nonDanglingEdgeEquiv (dropFrame' hc κ₁).fullDim.valid.1 ((site κ₁ hc).ndMap e) :=
  Subtype.ext (DivalentContraction.sq_edgeMap (ext_emb hc φ hg hm) (ext_hO hc φ hg) e.1)

/-- The extension on rows. -/
theorem ext_row (e : NonDanglingEdge κ₁.data) :
    κ₂.ident.row (markedRow (M κ₂) ((extΨ hc φ hg hm).nonDanglingEdgeEquiv κ₁.fullDim.valid.1 e)) =
      κ₁.ident.row (markedRow (M κ₁) e) := by
  set Ψ := extΨ hc φ hg hm
  -- the merged labels agree
  have hMerge : merge s (κ₂.ident.row (markedRow (M κ₂) (Ψ.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 e))) =
      merge s (κ₁.ident.row (markedRow (M κ₁) e)) := by
    rw [← rowEquiv_rowMap, ← rowEquiv_rowMap]
    have h := φ.overCore_row ((site κ₁ hc).ndMap e)
    change rowEquiv κ₂ hc (markedRow (MD κ₂ hc) _) = rowEquiv κ₁ hc (markedRow (MD κ₁ hc) _) at h
    rw [← ext_ndMap hc φ hg hm e] at h
    exact h
  -- the rows through `V` correspond
  have hRowMap : ∀ f : NonDanglingEdge κ₁.data, markedRow (M κ₁) e = markedRow (M κ₁) f →
      markedRow (M κ₂) (Ψ.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 e) =
        markedRow (M κ₂) (Ψ.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 f) := fun f h ↦
    congrArg (markedStablePathEquiv Ψ κ₁.fullDim.valid.1 (ext_mem_marks hc φ hg hm)) h
  have hfc : Ψ.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 ((site κ₁ hc).fc (markHyp κ₁ hc)) =
      (site κ₂ hc).fc (markHyp κ₂ hc) := Subtype.ext (ext_fc hc φ hg hm)
  have hfo : Ψ.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 ((site κ₁ hc).fo (markHyp κ₁ hc)) =
      (site κ₂ hc).fo (markHyp κ₂ hc) := Subtype.ext (ext_fo hc φ hg hm)
  set ℓ₁ := κ₁.ident.row (markedRow (M κ₁) e) with hℓ₁
  by_cases hP : ℓ₁ = s.castSucc ∨ ℓ₁ = Fin.last p
  · have hr := (mem_pair_iff κ₁ hc ℓ₁).mpr hP
    rw [hℓ₁, Equiv.symm_apply_apply] at hr
    rcases hr with h | h
    · rw [hRowMap _ h, hfc, row_fc κ₂ hc, Equiv.apply_symm_apply, hℓ₁, h, row_fc κ₁ hc,
        Equiv.apply_symm_apply]
    · rw [hRowMap _ h, hfo, row_fo κ₂ hc, Equiv.apply_symm_apply, hℓ₁, h, row_fo κ₁ hc,
        Equiv.apply_symm_apply]
  · rw [not_or] at hP
    obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr hP.2
    have hjs : j ≠ s := fun h ↦ hP.1 (by rw [← hj, h])
    rw [← hj] at hMerge ⊢
    have hm₁ : merge s j.castSucc = j := by simp [merge]
    rw [hm₁] at hMerge
    revert hMerge
    generalize κ₂.ident.row (markedRow (M κ₂) (Ψ.nonDanglingEdgeEquiv κ₁.fullDim.valid.1 e)) = ℓ₂
    intro hMerge
    induction ℓ₂ using Fin.lastCases with
    | last =>
      exfalso
      apply hjs
      rw [← hMerge]
      simp [merge]
    | cast j₂ =>
      have : merge s j₂.castSucc = j₂ := by simp [merge]
      rw [this] at hMerge
      rw [hMerge]

/-- **The extension over the dropped vertex.** -/
noncomputable def extendIso' : TypedFrameIso κ₁ κ₂ where
  datum := extΨ hc φ hg hm
  mark := ext_mark hc φ hg hm
  overCore_vertex B hImage := by
    by_cases hB : B.1 = V κ₁
    · have hB₂ : (extΨ hc φ hg hm).sourceVertexEquiv B.1 = V κ₂ := by
        rw [hB]; exact ext_V hc φ hg hm
      exact ((ident_vertex_eq_last_iff κ₂ ⟨_, hImage⟩).mpr hB₂).trans
        ((ident_vertex_eq_last_iff κ₁ B).mpr hB).symm
    · have hB₂ : (extΨ hc φ hg hm).sourceVertexEquiv B.1 ≠ V κ₂ := fun h ↦
        hB ((extΨ hc φ hg hm).sourceVertexEquiv.injective (h.trans (ext_V hc φ hg hm).symm))
      have hVal : ((site κ₂ hc).branchEquiv (markHyp κ₂ hc)
          ⟨⟨(extΨ hc φ hg hm).sourceVertexEquiv B.1, hImage⟩, hB₂⟩).1 =
          φ.datum.sourceVertexEquiv ((site κ₁ hc).vmap B.1) := ext_vmap hc φ hg hm B.1
      have hIm := hVal ▸ ((site κ₂ hc).branchEquiv (markHyp κ₂ hc)
          ⟨⟨(extΨ hc φ hg hm).sourceVertexEquiv B.1, hImage⟩, hB₂⟩).2
      have h := φ.overCore_vertex ((site κ₁ hc).branchEquiv (markHyp κ₁ hc) ⟨B, hB⟩) hIm
      change vertexEquiv κ₂ hc _ = vertexEquiv κ₁ hc _ at h
      have hEq : (⟨φ.datum.sourceVertexEquiv ((site κ₁ hc).branchEquiv (markHyp κ₁ hc) ⟨B, hB⟩).1,
          hIm⟩ : MarkedBranchVertex (site κ₂ hc).D (MD κ₂ hc)) =
          (site κ₂ hc).branchEquiv (markHyp κ₂ hc)
            ⟨⟨(extΨ hc φ hg hm).sourceVertexEquiv B.1, hImage⟩, hB₂⟩ :=
        Subtype.ext hVal.symm
      have h' := congrArg Fin.castSucc ((congrArg (vertexEquiv κ₂ hc) hEq).symm.trans h)
      exact (vertexEquiv_branchEquiv κ₂ hc ⟨⟨_, hImage⟩, hB₂⟩).symm.trans
        (h'.trans (vertexEquiv_branchEquiv κ₁ hc ⟨B, hB⟩))
  overCore_row := ext_row hc φ hg hm

end DropSmooth

end DraismaVargas.Count.MarkedCountGeneral
