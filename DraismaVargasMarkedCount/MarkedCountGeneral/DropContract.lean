module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropBase
public import DraismaVargas.LocalCases.WallAdmissibility
public import DraismaVargas.LocalCases.NonTrivalentValencyTwoExit

@[expose] public section

/-!
# The drop lemma: contracting a divalent change-zero target vertex

The generic dictionary behind the drop of an unramified mark. Let `x` be a **divalent target
vertex with `r = 0` at every source vertex over it** (`DivalentZero data x`: `typeZero_image'`
gives this at the image of a type-`0` mark). Then:

* the partitions above `x` and above its two target edges have the **same blocks**
  (`rel_iff_of_divalentZero`): `r = 0` and `val x = 2` force a single edge block of each incident
  edge inside every vertex block;
* every source edge above an edge at `x` has the index of its block at `x`
  (`sourceEdgeIndex_of_divalentZero`).

Contract one edge `t'` at `x` (the public `GluingContraction.contractDatum`, in either
orientation). Then:

* the **contraction fibre is a forest** (`contractionForest_of_divalentZero`), so the public
  `ContractionRamification.valid_contractDatum`, `WallAdmissibility.danglingCompatible_of_contractionForest`
  and `NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum` apply: the contracted datum is
  valid, danglingness of the surviving occurrences is unchanged, and so is the source genus.

The marked rows, the incidences and the matrix are in module `DropRows`.
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

namespace DivalentContraction

/-! ## 1.  The local structure at a divalent change-zero vertex -/

section Local

variable {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree)

/-- **A divalent target vertex of change zero, block by block**: two incident target edges, and
`r = 0` at every source vertex over it. -/
def DivalentZero (x : target.V) : Prop :=
  (incidentEdges x).card = 2 ∧
    ∀ sheet : Fin degree, data.localRamification x ((data.vertexPartition x).toBlock sheet) = 0

variable {data}

/-- **One edge block per vertex block**: over a divalent change-zero vertex, each incident edge
partition induces a single block inside every vertex block. -/
theorem blockCountWithin_eq_one {x : target.V} (h : DivalentZero data x) {e : target.edges}
    (he : e ∈ incidentEdges x) (i : Fin degree) :
    (data.edgePartition e).blockCountWithin (data.vertexPartition x) i = 1 := by
  have hZero := h.2 i
  unfold GluingDatum.localRamification at hZero
  rw [h.1] at hZero
  simp only [SheetPartition.toBlock_val, Nat.cast_ofNat, sub_self, mul_zero, sub_zero] at hZero
  have hSum : ∑ f ∈ incidentEdges x,
      (data.edgePartition f).blockCountWithin (data.vertexPartition x)
        ((data.vertexPartition x).repr i) = (incidentEdges x).card := by
    rw [h.1]
    exact_mod_cast (by linarith : (∑ f ∈ incidentEdges x,
      ((data.edgePartition f).blockCountWithin (data.vertexPartition x)
        ((data.vertexPartition x).repr i) : ℤ)) = 2)
  have hOne := eq_one_of_sum_eq_card
    (fun f _ ↦ SheetPartition.blockCountWithin_pos _ _ _) hSum he
  rwa [blockCountWithin_congr _ _ ((data.vertexPartition x).rel_repr_left i)] at hOne

/-- **The same blocks**: over a divalent change-zero vertex, each incident edge partition has the
blocks of the vertex partition. -/
theorem rel_iff {x : target.V} (h : DivalentZero data x) {e : target.edges}
    (he : e ∈ incidentEdges x) (i j : Fin degree) :
    (data.edgePartition e).Rel i j ↔ (data.vertexPartition x).Rel i j := by
  have hBlock := SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one
    (data.edgePartition e) (data.vertexPartition x)
    (edgePartition_refines_of_mem_incidentEdges data x e he) i (blockCountWithin_eq_one h he i)
  rw [← SheetPartition.mem_block_iff, ← SheetPartition.mem_block_iff, hBlock]

/-- The two edges at `x` have the same blocks. -/
theorem edge_rel_iff {x : target.V} (h : DivalentZero data x) {e f : target.edges}
    (he : e ∈ incidentEdges x) (hf : f ∈ incidentEdges x) (i j : Fin degree) :
    (data.edgePartition e).Rel i j ↔ (data.edgePartition f).Rel i j :=
  (rel_iff h he i j).trans (rel_iff h hf i j).symm

/-- **The index of an edge at `x` is the local degree at `x`.** -/
theorem blockCard_eq {x : target.V} (h : DivalentZero data x) {e : target.edges}
    (he : e ∈ incidentEdges x) (i : Fin degree) :
    (data.edgePartition e).blockCard i = (data.vertexPartition x).blockCard i :=
  SheetPartition.blockCard_eq_of_refines_of_blockCountWithin_eq_one _ _
    (edgePartition_refines_of_mem_incidentEdges data x e he) i (blockCountWithin_eq_one h he i)

/-- The two edges at `x` have the same block sizes. -/
theorem edge_blockCard_eq {x : target.V} (h : DivalentZero data x) {e f : target.edges}
    (he : e ∈ incidentEdges x) (hf : f ∈ incidentEdges x) (i : Fin degree) :
    (data.edgePartition e).blockCard i = (data.edgePartition f).blockCard i :=
  (blockCard_eq h he i).trans (blockCard_eq h hf i).symm

/-- Every source vertex over `x` has graph degree two. -/
theorem vertex_degree_eq_two {x : target.V} (h : DivalentZero data x)
    (X : data.SourceVertex) (hX : X.1.1 = x) : vertex_degree data.sourceGraph X = 2 := by
  have hDeg := StableLocalProperties.vertex_degree_eq_two_of_divalent_localRamification_zero
    data x h.1 X.1.2 (h.2 X.1.2)
  have hX' : data.sourceEndpoint x X.1.2 = X := by
    rw [← hX]
    exact data.sourceEndpoint_self X
  rwa [hX'] at hDeg

end Local

/-! ## 2.  The contraction: a forest, hence valid, with the same dangling and genus -/

section Contraction

variable {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- **A contraction site**: a target edge `c` with an end `x` that is divalent of change zero.
The contraction is `contractDatumAt data c hOne` (the public `contractDatum` read off `c`, which
folds `c.2` onto `c.1`). -/
structure Site (data : GluingDatum target degree) where
  /-- The divalent change-zero vertex. -/
  x : target.V
  /-- The contracted edge, one of the two edges at `x`. -/
  c : target.edges
  /-- `c` is the only edge between its ends (the target is a tree). -/
  hOne : num_edges target (c : target.V × target.V).1 (c : target.V × target.V).2 = 1
  /-- `c` is at `x`. -/
  mem : c ∈ incidentEdges x
  /-- `x` is divalent of change zero. -/
  div : DivalentZero data x

namespace Site

variable (S : Site data)

/-- The contracted target. -/
abbrev T' : CFGraph := GraphContraction.contract target (fst_ne_snd S.c) S.hOne

/-- The contracted datum. -/
noncomputable abbrev D : GluingDatum S.T' degree :=
  contractDatum data (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne

/-- The source vertex map of the contraction. -/
noncomputable abbrev vmap (X : data.SourceVertex) : S.D.SourceVertex :=
  sourceVertexMap data (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne X

/-- The source edge map of the contraction, on occurrences away from `c`. -/
noncomputable abbrev emap (e : {e : data.SourceEdge // e.1.1 ≠ S.c}) : S.D.SourceEdge :=
  sourceEdgeMap data (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne e

/-- `x` is one of the two ends of `c`. -/
theorem x_eq_or : S.x = (S.c : target.V × target.V).1 ∨ S.x = (S.c : target.V × target.V).2 := by
  rcases (mem_incidentEdges_iff S.x S.c).mp S.mem with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

/-- The partition of `c` has the blocks of the partition at `x`. -/
theorem c_rel_iff (i j : Fin degree) :
    (data.edgePartition S.c).Rel i j ↔ (data.vertexPartition S.x).Rel i j :=
  rel_iff S.div S.mem i j

/-- **The contraction fibre is a forest** (`ContractionForest`): inside every merged block there
is one block of the far end, and as many blocks of `c` as of `x`. -/
theorem contractionForest :
    ContractionForest data (S.c : target.V × target.V).1 (S.c : target.V × target.V).2 S.c := by
  classical
  have hca : (data.edgePartition S.c).Refines
      (data.vertexPartition (S.c : target.V × target.V).1) :=
    edgePartition_refines_of_mem_incidentEdges data _ S.c (by simp [mem_incidentEdges_iff])
  have hcb : (data.edgePartition S.c).Refines
      (data.vertexPartition (S.c : target.V × target.V).2) :=
    edgePartition_refines_of_mem_incidentEdges data _ S.c (by simp [mem_incidentEdges_iff])
  -- the number of fine blocks inside a coarse block depends only on the fine relation
  have hFine : ∀ (F F' C : SheetPartition degree), (∀ i j, F.Rel i j ↔ F'.Rel i j) →
      F.Refines C → ∀ B : C.Blocks,
        (SheetPartition.blocksWithin F C B).card = (SheetPartition.blocksWithin F' C B).card := by
    intro F F' C hFF' hFC B
    have hF'C : F'.Refines C := fun i j h ↦ hFC i j ((hFF' i j).mpr h)
    rw [SheetPartition.card_blocksWithin_eq_blockCountWithin F C hFC,
      SheetPartition.card_blocksWithin_eq_blockCountWithin F' C hF'C]
    unfold SheetPartition.blockCountWithin
    refine Finset.card_bij (fun r _ ↦ F'.repr r) ?_ ?_ ?_
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
      exact ((hFF' _ _).mp (F.rel_repr_left j)).symm
    · intro r₁ hr₁ r₂ hr₂ h
      obtain ⟨j₁, -, rfl⟩ := Finset.mem_image.mp hr₁
      obtain ⟨j₂, -, rfl⟩ := Finset.mem_image.mp hr₂
      have h' : F'.Rel (F.repr j₁) (F.repr j₂) := h
      have h'' := (hFF' _ _).mpr h'
      unfold SheetPartition.Rel at h''
      rwa [F.repr_idem, F.repr_idem] at h''
    · intro r hr
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      refine ⟨F.repr j, Finset.mem_image.mpr ⟨j, hj, rfl⟩, ?_⟩
      exact ((hFF' _ _).mp (F.rel_repr_left j))
  -- a partition with one block inside every coarse block
  have hSingle : ∀ (F C : SheetPartition degree), F.Refines C → C.Refines F →
      ∀ B : C.Blocks, (SheetPartition.blocksWithin F C B).card = 1 := by
    intro F C hFC hCF B
    rw [SheetPartition.card_blocksWithin_eq_blockCountWithin F C hFC]
    have hBlock : C.block B.1 = F.block B.1 := by
      ext j
      rw [SheetPartition.mem_block_iff, SheetPartition.mem_block_iff]
      exact ⟨fun h ↦ hCF _ _ h, fun h ↦ hFC _ _ h⟩
    unfold SheetPartition.blockCountWithin
    rw [hBlock]
    exact SheetPartition.blockCountWithin_self F B.1
  intro B
  rcases S.x_eq_or with hx | hx
  · -- `x = a`: the merged partition has the blocks of `b`
    have hEq : ∀ i j, (data.edgePartition S.c).Rel i j ↔
        (data.vertexPartition (S.c : target.V × target.V).1).Rel i j := fun i j ↦ by
      rw [← hx]; exact S.c_rel_iff i j
    have hab : (data.vertexPartition (S.c : target.V × target.V).1).Refines
        (data.vertexPartition (S.c : target.V × target.V).2) :=
      fun i j h ↦ hcb i j ((hEq i j).mpr h)
    have hJoin : (mergedPartition data (S.c : target.V × target.V).1
        (S.c : target.V × target.V).2).Refines
          (data.vertexPartition (S.c : target.V × target.V).2) :=
      (SheetPartition.join_refines_iff _ _ _).mpr ⟨hab, SheetPartition.Refines.refl _⟩
    rw [hFine _ _ _ hEq (edgePartition_refines_mergedPartition data (contracted := S.c) rfl) B,
      hSingle _ _ (vertexPartition_refines_mergedPartition_right data _ _) hJoin B]
  · -- `x = b`: the merged partition has the blocks of `a`
    have hEq : ∀ i j, (data.edgePartition S.c).Rel i j ↔
        (data.vertexPartition (S.c : target.V × target.V).2).Rel i j := fun i j ↦ by
      rw [← hx]; exact S.c_rel_iff i j
    have hba : (data.vertexPartition (S.c : target.V × target.V).2).Refines
        (data.vertexPartition (S.c : target.V × target.V).1) :=
      fun i j h ↦ hca i j ((hEq i j).mpr h)
    have hJoin : (mergedPartition data (S.c : target.V × target.V).1
        (S.c : target.V × target.V).2).Refines
          (data.vertexPartition (S.c : target.V × target.V).1) :=
      (SheetPartition.join_refines_iff _ _ _).mpr ⟨SheetPartition.Refines.refl _, hba⟩
    rw [hFine _ _ _ hEq (edgePartition_refines_mergedPartition data (contracted := S.c) rfl) B,
      hSingle _ _ (vertexPartition_refines_mergedPartition data _ _) hJoin B]
    exact Nat.add_comm _ _

/-- **The contracted datum is valid** (`ContractionRamification.valid_contractDatum`). -/
theorem valid (hValid : data.Valid) : S.D.Valid :=
  valid_contractDatum data rfl (fst_ne_snd S.c) S.hOne S.contractionForest hValid

/-- **Danglingness is unchanged** on the occurrences away from `c`
(`WallAdmissibility.isDangling_sourceEdgeMap_iff` under the forest). -/
theorem isDangling_emap_iff (e : {e : data.SourceEdge // e.1.1 ≠ S.c}) :
    IsDangling S.D (S.emap e) ↔ IsDangling data e.1 :=
  WallAdmissibility.isDangling_sourceEdgeMap_iff data rfl (fst_ne_snd S.c) S.hOne
    S.contractionForest e

/-- **The source genus is unchanged** (`NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum`). -/
theorem genus_sourceGraph : genus S.D.sourceGraph = genus data.sourceGraph :=
  NonTrivalentValencyTwoExit.genus_sourceGraph_contractDatum data rfl (fst_ne_snd S.c) S.hOne
    S.contractionForest

/-! ### The far end and the other edge -/

/-- The end of `c` other than `x`. -/
noncomputable def w : target.V :=
  if S.x = (S.c : target.V × target.V).1 then (S.c : target.V × target.V).2
  else (S.c : target.V × target.V).1

/-- The far end of `c` is not `x`. -/
theorem w_ne_x : S.w ≠ S.x := by
  unfold w
  have hne := fst_ne_snd S.c
  split_ifs with h
  · rw [h]; exact hne.symm
  · exact fun h' ↦ h h'.symm

/-- `c` joins `x` and `w`, in one of the two orders. -/
theorem c_ends : ((S.c : target.V × target.V).1 = S.x ∧ (S.c : target.V × target.V).2 = S.w) ∨
    ((S.c : target.V × target.V).1 = S.w ∧ (S.c : target.V × target.V).2 = S.x) := by
  rcases S.x_eq_or with h | h
  · left
    unfold w
    rw [ite_eq_left h]
    exact ⟨h.symm, rfl⟩
  · right
    have hne : S.x ≠ (S.c : target.V × target.V).1 := by rw [h]; exact (fst_ne_snd S.c).symm
    unfold w
    rw [ite_eq_right hne]
    exact ⟨rfl, h.symm⟩

/-- `c` is at its far end `w`. -/
theorem c_mem_w : S.c ∈ incidentEdges S.w := by
  rw [mem_incidentEdges_iff]
  rcases S.c_ends with h | h
  · exact Or.inr h.2
  · exact Or.inl h.1

/-- The ends of `c` are `x` and `w`. -/
theorem eq_x_or_eq_w {u : target.V} (hu : S.c ∈ incidentEdges u) : u = S.x ∨ u = S.w := by
  rw [mem_incidentEdges_iff] at hu
  rcases S.c_ends with h | h <;> rcases hu with hu | hu
  · exact Or.inl (hu.symm.trans h.1)
  · exact Or.inr (hu.symm.trans h.2)
  · exact Or.inr (hu.symm.trans h.1)
  · exact Or.inl (hu.symm.trans h.2)

/-- The partition of `x` refines that of `w`. -/
theorem x_refines_w : (data.vertexPartition S.x).Refines (data.vertexPartition S.w) :=
  fun i j h ↦ edgePartition_refines_of_mem_incidentEdges data S.w S.c S.c_mem_w i j
    ((S.c_rel_iff i j).mpr h)

/-- **The merged partition has the blocks of `w`.** -/
theorem merged_rel_iff (i j : Fin degree) :
    (mergedPartition data (S.c : target.V × target.V).1 (S.c : target.V × target.V).2).Rel i j ↔
      (data.vertexPartition S.w).Rel i j := by
  have hRef : (mergedPartition data (S.c : target.V × target.V).1
      (S.c : target.V × target.V).2).Refines (data.vertexPartition S.w) := by
    refine (SheetPartition.join_refines_iff _ _ _).mpr ⟨?_, ?_⟩ <;>
    · rcases S.c_ends with h | h
      · first
        | (rw [h.1]; exact S.x_refines_w)
        | (rw [h.2]; exact SheetPartition.Refines.refl _)
      · first
        | (rw [h.1]; exact SheetPartition.Refines.refl _)
        | (rw [h.2]; exact S.x_refines_w)
  have hRef' : (data.vertexPartition S.w).Refines (mergedPartition data
      (S.c : target.V × target.V).1 (S.c : target.V × target.V).2) := by
    rcases S.c_ends with h | h
    · rw [← h.2]; exact vertexPartition_refines_mergedPartition_right data _ _
    · rw [← h.1]; exact vertexPartition_refines_mergedPartition data _ _
  exact ⟨hRef i j, hRef' i j⟩

/-- The two edges at `x`. -/
theorem card_erase_c : ((incidentEdges S.x).erase S.c).card = 1 := by
  rw [Finset.card_erase_of_mem S.mem, S.div.1]

/-- **The other edge at `x`.** -/
noncomputable def other : target.edges :=
  (Finset.card_eq_one.mp S.card_erase_c).choose

/-- The edges at `x` other than `c`. -/
theorem erase_eq : (incidentEdges S.x).erase S.c = {S.other} :=
  (Finset.card_eq_one.mp S.card_erase_c).choose_spec

/-- The other edge is at `x`. -/
theorem other_mem : S.other ∈ incidentEdges S.x :=
  Finset.mem_of_mem_erase (S.erase_eq ▸ Finset.mem_singleton_self S.other)

/-- The other edge is not `c`. -/
theorem other_ne : S.other ≠ S.c :=
  Finset.ne_of_mem_erase (S.erase_eq ▸ Finset.mem_singleton_self S.other)

/-- An edge at `x` is `c` or the other edge. -/
theorem eq_c_or_other {e : target.edges} (he : e ∈ incidentEdges S.x) : e = S.c ∨ e = S.other := by
  by_cases h : e = S.c
  · exact Or.inl h
  · right
    have : e ∈ (incidentEdges S.x).erase S.c := Finset.mem_erase.mpr ⟨h, he⟩
    rw [S.erase_eq] at this
    exact Finset.mem_singleton.mp this

/-- The partition of the other edge has the blocks of `x`. -/
theorem other_rel_iff (i j : Fin degree) :
    (data.edgePartition S.other).Rel i j ↔ (data.vertexPartition S.x).Rel i j :=
  rel_iff S.div S.other_mem i j

/-- **The other edge at `x` does not reach `w`**: the target is a tree with one edge between `x`
and `w`. -/
theorem other_not_mem_w : S.other ∉ incidentEdges S.w := by
  intro hw
  have hKept := coe_mem_keptEdges (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne S.other_ne
  rw [GraphContraction.mem_keptEdges] at hKept
  apply hKept.2
  have hx := (mem_incidentEdges_iff _ _).mp S.other_mem
  have hw' := (mem_incidentEdges_iff _ _).mp hw
  have hne := fst_ne_snd S.other
  have hwx := S.w_ne_x
  rcases S.c_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx with hx | hx <;> rcases hw' with hw' | hw'
  all_goals first
    | exact absurd (hx.symm.trans hw') hwx.symm
    | exact Or.inl (Prod.ext (hx.trans h1.symm) (hw'.trans h2.symm))
    | exact Or.inl (Prod.ext (hw'.trans h1.symm) (hx.trans h2.symm))
    | exact Or.inr (Prod.ext (hx.trans h2.symm) (hw'.trans h1.symm))
    | exact Or.inr (Prod.ext (hw'.trans h2.symm) (hx.trans h1.symm))

/-! ### Source vertices -/

/-- **The `c`-neighbour** of a source vertex over `x`: the source vertex over `w` in its block. -/
noncomputable def cNbr (X : data.SourceVertex) : data.SourceVertex := data.sourceEndpoint S.w X.1.2

/-- The `c`-neighbour lies over `w`. -/
theorem cNbr_target (X : data.SourceVertex) : (S.cNbr X).1.1 = S.w := rfl

/-- The source edge over `c` through a sheet joins the source vertices over `x` and `w` through
that sheet. -/
theorem incident_c_iff (i : Fin degree) (Y : data.SourceVertex) :
    Incident data (data.sourceEdge S.c i) Y ↔
      Y = data.sourceEndpoint S.x i ∨ Y = data.sourceEndpoint S.w i := by
  rw [incident_iff_target_mem_and_rel]
  simp only [GluingDatum.sourceEdge_target, GluingDatum.sourceEdge_sheet]
  constructor
  · rintro ⟨hMem, hRel⟩
    rcases S.eq_x_or_eq_w hMem with h | h
    · left
      refine ((data.sourceEndpoint_eq_iff _ _ _).mpr ⟨h.symm, ?_⟩).symm
      have hRel' : (data.vertexPartition S.x).Rel Y.1.2 ((data.edgePartition S.c).repr i) :=
        h ▸ hRel
      exact ((S.c_rel_iff _ _).mp ((data.edgePartition S.c).rel_repr_right i)).trans hRel'.symm
    · right
      refine ((data.sourceEndpoint_eq_iff _ _ _).mpr ⟨h.symm, ?_⟩).symm
      have hRel' : (data.vertexPartition S.w).Rel Y.1.2 ((data.edgePartition S.c).repr i) :=
        h ▸ hRel
      exact (edgePartition_refines_of_mem_incidentEdges data S.w S.c S.c_mem_w _ _
        ((data.edgePartition S.c).rel_repr_right i)).trans hRel'.symm
  · rintro (rfl | rfl)
    · refine ⟨S.mem, ?_⟩
      show (data.vertexPartition S.x).Rel ((data.vertexPartition S.x).repr i) _
      exact ((data.vertexPartition S.x).rel_repr_left i).trans
        ((S.c_rel_iff _ _).mp ((data.edgePartition S.c).rel_repr_right i))
    · refine ⟨S.c_mem_w, ?_⟩
      show (data.vertexPartition S.w).Rel ((data.vertexPartition S.w).repr i) _
      exact ((data.vertexPartition S.w).rel_repr_left i).trans
        (edgePartition_refines_of_mem_incidentEdges data S.w S.c S.c_mem_w _ _
          ((data.edgePartition S.c).rel_repr_right i))

/-- Two canonical source edges over one target edge agree exactly when their sheets are in one
block. -/
theorem _root_.DraismaVargas.Count.MarkedCountGeneral.DivalentContraction.sourceEdge_eq_iff
    {target : CFGraph} {degree : ℕ} (data : GluingDatum target degree) (e : target.edges)
    (i j : Fin degree) :
    data.sourceEdge e i = data.sourceEdge e j ↔ (data.edgePartition e).Rel i j := by
  constructor
  · intro h
    exact congrArg (fun f : data.SourceEdge ↦ f.1.2) h
  · intro h
    exact Subtype.ext (Prod.ext rfl h)

/-- A source edge is the canonical one through any sheet of its block. -/
theorem _root_.DraismaVargas.Count.MarkedCountGeneral.DivalentContraction.eq_sourceEdge_of_rel
    {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree} (f : data.SourceEdge)
    {i : Fin degree} (h : (data.edgePartition f.1.1).Rel i f.1.2) :
    f = data.sourceEdge f.1.1 i := by
  conv_lhs => rw [← GluingDatum.sourceEdge_self data f]
  exact (sourceEdge_eq_iff data _ _ _).mpr h.symm

/-- **The two source edges at a source vertex over `x`**: the ones over `c` and over the other
edge through its sheet. -/
theorem incident_x_iff (X : data.SourceVertex) (hX : X.1.1 = S.x) (e : data.SourceEdge) :
    Incident data e X ↔ e = data.sourceEdge S.c X.1.2 ∨ e = data.sourceEdge S.other X.1.2 := by
  rw [incident_iff_target_mem_and_rel]
  constructor
  · rintro ⟨hMem, hRel⟩
    rw [hX] at hMem
    have hRel' : (data.vertexPartition S.x).Rel X.1.2 e.1.2 := hX ▸ hRel
    rcases S.eq_c_or_other hMem with h | h
    · left
      have hR : (data.edgePartition e.1.1).Rel X.1.2 e.1.2 := by
        rw [h]; exact (S.c_rel_iff _ _).mpr hRel'
      rw [eq_sourceEdge_of_rel e hR, h]
    · right
      have hR : (data.edgePartition e.1.1).Rel X.1.2 e.1.2 := by
        rw [h]; exact (S.other_rel_iff _ _).mpr hRel'
      rw [eq_sourceEdge_of_rel e hR, h]
  · rintro (rfl | rfl)
    · refine ⟨hX ▸ S.mem, ?_⟩
      show (data.vertexPartition X.1.1).Rel X.1.2 ((data.edgePartition S.c).repr X.1.2)
      have h := (S.c_rel_iff _ _).mp ((data.edgePartition S.c).rel_repr_right X.1.2)
      exact hX ▸ h
    · refine ⟨hX ▸ S.other_mem, ?_⟩
      show (data.vertexPartition X.1.1).Rel X.1.2 ((data.edgePartition S.other).repr X.1.2)
      have h := (S.other_rel_iff _ _).mp ((data.edgePartition S.other).rel_repr_right X.1.2)
      exact hX ▸ h

/-- A source vertex over `x` is the canonical one through its own sheet. -/
theorem eq_sourceEndpoint_x (X : data.SourceVertex) (hX : X.1.1 = S.x) :
    X = data.sourceEndpoint S.x X.1.2 := by
  refine ((data.sourceEndpoint_eq_iff _ _ _).mpr ⟨hX.symm, ?_⟩).symm
  exact rfl

/-- **The contraction identifies a source vertex over `x` with its `c`-neighbour.** -/
theorem vmap_cNbr (X : data.SourceVertex) (hX : X.1.1 = S.x) : S.vmap X = S.vmap (S.cNbr X) := by
  have hSame := sourceVertexMap_sourceEnds_eq_of_contracted data (contracted := S.c) rfl
    (fst_ne_snd S.c) S.hOne (data.sourceEdge S.c X.1.2) rfl
  have h1 := (S.incident_c_iff X.1.2 _).mp (incident_left data (data.sourceEdge S.c X.1.2))
  have h2 := (S.incident_c_iff X.1.2 _).mp (incident_right data (data.sourceEdge S.c X.1.2))
  have hne := data.sourceEnds_ne (data.sourceEdge S.c X.1.2)
  rw [← S.eq_sourceEndpoint_x X hX] at h1 h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · rw [h1, h2] at hSame; exact hSame
  · rw [h1, h2] at hSame; exact hSame.symm
  · exact absurd (h1.trans h2.symm) hne

/-- **The contraction is injective away from `x`.** -/
theorem vmap_inj {Y Z : data.SourceVertex} (hY : Y.1.1 ≠ S.x) (hZ : Z.1.1 ≠ S.x) :
    S.vmap Y = S.vmap Z ↔ Y = Z := by
  constructor
  · intro h
    rcases (ContractionFibre.sourceVertexMap_eq_iff_cases data (contracted := S.c) rfl
      (fst_ne_snd S.c) S.hOne Y Z).mp h with h | ⟨hYab, hZab, hJoin⟩
    · exact h
    · have hYw : Y.1.1 = S.w := by
        rcases S.eq_x_or_eq_w (u := Y.1.1) (by
          rw [mem_incidentEdges_iff]; rcases hYab with h | h
          · exact Or.inl h.symm
          · exact Or.inr h.symm) with h | h
        · exact absurd h hY
        · exact h
      have hZw : Z.1.1 = S.w := by
        rcases S.eq_x_or_eq_w (u := Z.1.1) (by
          rw [mem_incidentEdges_iff]; rcases hZab with h | h
          · exact Or.inl h.symm
          · exact Or.inr h.symm) with h | h
        · exact absurd h hZ
        · exact h
      have hRel : (data.vertexPartition S.w).Rel Y.1.2 Z.1.2 :=
        (S.merged_rel_iff _ _).mp ((SheetPartition.join_rel_iff _ _ _ _).mpr hJoin)
      have hY2 : (data.vertexPartition S.w).repr Y.1.2 = Y.1.2 := hYw ▸ Y.2
      have hZ2 : (data.vertexPartition S.w).repr Z.1.2 = Z.1.2 := hZw ▸ Z.2
      have h2 : Y.1.2 = Z.1.2 := by
        unfold SheetPartition.Rel at hRel
        rw [hY2, hZ2] at hRel
        exact hRel
      exact Subtype.ext (Prod.ext (hYw.trans hZw.symm) h2)
  · rintro rfl
    rfl

/-- **Every contracted source vertex comes from a source vertex away from `x`.** -/
theorem exists_vmap_eq (Y' : S.D.SourceVertex) : ∃ Y : data.SourceVertex,
    Y.1.1 ≠ S.x ∧ S.vmap Y = Y' := by
  obtain ⟨Y, rfl⟩ := sourceVertexMap_surjective data (contracted := S.c) rfl (fst_ne_snd S.c)
    S.hOne Y'
  by_cases hY : Y.1.1 = S.x
  · exact ⟨S.cNbr Y, by rw [S.cNbr_target]; exact S.w_ne_x, (S.vmap_cNbr Y hY).symm⟩
  · exact ⟨Y, hY, rfl⟩

/-! ### The edge map -/

/-- The partner of a source edge over `c`: the source edge over the other edge at `x` through
the same sheet (the other edge at the same source vertex over `x`). -/
noncomputable def partner (e : data.SourceEdge) : data.SourceEdge :=
  data.sourceEdge S.other e.1.2

/-- The partner lies over the other edge. -/
theorem partner_target (e : data.SourceEdge) : (S.partner e).1.1 = S.other := rfl

/-- **The edge map on occurrences**: an occurrence over `c` goes to its partner, the others to
themselves; then the public `sourceEdgeMap`. -/
noncomputable def mu (e : data.SourceEdge) : {e : data.SourceEdge // e.1.1 ≠ S.c} :=
  if h : e.1.1 = S.c then ⟨S.partner e, S.other_ne⟩ else ⟨e, h⟩

/-- The edge map of the contraction on all occurrences. -/
noncomputable def edgeMap (e : data.SourceEdge) : S.D.SourceEdge := S.emap (S.mu e)

/-- Away from `c`, the occurrence itself. -/
theorem mu_of_ne {e : data.SourceEdge} (h : e.1.1 ≠ S.c) : S.mu e = ⟨e, h⟩ := by
  unfold mu; split_ifs with h'
  · exact absurd h' h
  · rfl

/-- Over `c`, the partner. -/
theorem mu_of_eq {e : data.SourceEdge} (h : e.1.1 = S.c) :
    S.mu e = ⟨S.partner e, S.other_ne⟩ := by
  unfold mu; rw [dite_eq_left h]

/-- The edge map away from `c`. -/
theorem edgeMap_of_ne {e : data.SourceEdge} (h : e.1.1 ≠ S.c) : S.edgeMap e = S.emap ⟨e, h⟩ := by
  unfold edgeMap; rw [S.mu_of_ne h]

/-- The source vertex over `x` of an occurrence over `c`. -/
theorem incident_c_x {e : data.SourceEdge} (h : e.1.1 = S.c) :
    Incident data e (data.sourceEndpoint S.x e.1.2) := by
  have he : e = data.sourceEdge S.c e.1.2 := by
    conv_lhs => rw [← GluingDatum.sourceEdge_self data e]
    rw [h]
  rw [he]
  exact (S.incident_c_iff _ _).mpr (Or.inl (by rw [← he]))

/-- The partner of an occurrence over `c` meets it at the source vertex over `x`. -/
theorem incident_partner_x (e : data.SourceEdge) :
    Incident data (S.partner e) (data.sourceEndpoint S.x e.1.2) :=
  (S.incident_x_iff _ rfl _).mpr (Or.inr ((sourceEdge_eq_iff data _ _ _).mpr
    ((S.other_rel_iff _ _).mpr ((data.vertexPartition S.x).rel_repr_right e.1.2))))

/-- **Danglingness of an occurrence over `c` and of its partner agree** (they meet at a source
vertex of graph degree two, `W4StableSource.isDangling_of_incident_of_vertex_degree_eq_two`). -/
theorem isDangling_partner_iff {e : data.SourceEdge} (h : e.1.1 = S.c) :
    IsDangling data (S.partner e) ↔ IsDangling data e := by
  have he : e = data.sourceEdge S.c e.1.2 := by
    conv_lhs => rw [← GluingDatum.sourceEdge_self data e]
    rw [h]
  have hIff := StableLocalProperties.isDangling_sourceEdge_iff_of_divalent_localRamification_zero
    data S.x S.div.1 e.1.2 (S.div.2 e.1.2) (first := S.c) (second := S.other) S.other_ne.symm
    S.mem S.other_mem
  conv_rhs => rw [he]
  exact hIff.symm

/-- **Danglingness is unchanged** by the edge map. -/
theorem isDangling_edgeMap_iff (e : data.SourceEdge) :
    IsDangling S.D (S.edgeMap e) ↔ IsDangling data e := by
  unfold edgeMap
  by_cases h : e.1.1 = S.c
  · rw [S.mu_of_eq h, S.isDangling_emap_iff]
    exact S.isDangling_partner_iff h
  · rw [S.mu_of_ne h, S.isDangling_emap_iff]

/-- **Incidence away from `x` is carried forwards.** -/
theorem incident_edgeMap {e : data.SourceEdge} {A : data.SourceVertex} (hA : A.1.1 ≠ S.x)
    (h : Incident data e A) : Incident S.D (S.edgeMap e) (S.vmap A) := by
  unfold edgeMap
  by_cases hc : e.1.1 = S.c
  · rw [S.mu_of_eq hc]
    -- `A` is the `w`-end of `e`, identified with its `x`-end
    have hA' : A = data.sourceEndpoint S.w e.1.2 := by
      have he : e = data.sourceEdge S.c e.1.2 := by
        conv_lhs => rw [← GluingDatum.sourceEdge_self data e]
        rw [hc]
      rw [he] at h
      rcases (S.incident_c_iff _ _).mp h with h' | h'
      · exact absurd (h' ▸ rfl : A.1.1 = S.x) hA
      · exact h'
    have hX := S.vmap_cNbr (data.sourceEndpoint S.x e.1.2) rfl
    have hNbr : S.cNbr (data.sourceEndpoint S.x e.1.2) = A := by
      rw [hA']
      unfold cNbr
      refine (data.sourceEndpoint_eq_iff _ _ _).mpr ⟨rfl, ?_⟩
      exact (S.x_refines_w _ _ ((data.vertexPartition S.x).rel_repr_left e.1.2)).trans
        ((data.vertexPartition S.w).rel_repr_right e.1.2)
    rw [hNbr] at hX
    rw [← hX]
    exact WallDegeneration.incident_sourceEdgeMap data rfl (fst_ne_snd S.c) S.hOne _ (S.incident_partner_x e)
  · rw [S.mu_of_ne hc]
    exact WallDegeneration.incident_sourceEdgeMap data rfl (fst_ne_snd S.c) S.hOne _ h

/-- An occurrence over `c` is the canonical one through its sheet. -/
theorem eq_sourceEdge_c {e : data.SourceEdge} (h : e.1.1 = S.c) : e = data.sourceEdge S.c e.1.2 := by
  conv_lhs => rw [← GluingDatum.sourceEdge_self data e]
  rw [h]

/-- The partner of the canonical occurrence over `c` through a sheet is the canonical occurrence
over the other edge through that sheet. -/
theorem partner_sourceEdge_c (i : Fin degree) :
    S.partner (data.sourceEdge S.c i) = data.sourceEdge S.other i := by
  unfold partner
  refine (sourceEdge_eq_iff data _ _ _).mpr ?_
  exact (S.other_rel_iff _ _).mpr ((S.c_rel_iff _ _).mp ((data.edgePartition S.c).rel_repr_left i))

/-- **When two occurrences have the same image**: they are equal, or they are the two
occurrences at one source vertex over `x`. -/
theorem edgeMap_eq_imp {e f : data.SourceEdge} (h : S.edgeMap e = S.edgeMap f) :
    e = f ∨ ∃ X : data.SourceVertex, X.1.1 = S.x ∧ Incident data e X ∧ Incident data f X := by
  have hmu : S.mu e = S.mu f :=
    sourceEdgeMap_injective data (contracted := S.c) rfl (fst_ne_snd S.c) S.hOne h
  by_cases he : e.1.1 = S.c <;> by_cases hf : f.1.1 = S.c
  · left
    rw [S.mu_of_eq he, S.mu_of_eq hf] at hmu
    have hp : S.partner e = S.partner f := congrArg Subtype.val hmu
    unfold partner at hp
    have hRel := (sourceEdge_eq_iff data _ _ _).mp hp
    rw [S.eq_sourceEdge_c he, S.eq_sourceEdge_c hf]
    exact (sourceEdge_eq_iff data _ _ _).mpr ((S.c_rel_iff _ _).mpr ((S.other_rel_iff _ _).mp hRel))
  · right
    rw [S.mu_of_eq he, S.mu_of_ne hf] at hmu
    have hp : S.partner e = f := congrArg Subtype.val hmu
    exact ⟨_, rfl, S.incident_c_x he, hp ▸ S.incident_partner_x e⟩
  · right
    rw [S.mu_of_ne he, S.mu_of_eq hf] at hmu
    have hp : e = S.partner f := congrArg Subtype.val hmu
    exact ⟨_, rfl, hp ▸ S.incident_partner_x f, S.incident_c_x hf⟩
  · left
    rw [S.mu_of_ne he, S.mu_of_ne hf] at hmu
    exact congrArg Subtype.val hmu

/-- **The two occurrences at a source vertex over `x` have the same image.** -/
theorem edgeMap_eq_of_incident_x {X : data.SourceVertex} (hX : X.1.1 = S.x) {e f : data.SourceEdge}
    (he : Incident data e X) (hf : Incident data f X) : S.edgeMap e = S.edgeMap f := by
  have hc : S.edgeMap (data.sourceEdge S.c X.1.2) = S.edgeMap (data.sourceEdge S.other X.1.2) := by
    unfold edgeMap
    rw [S.mu_of_eq rfl, S.mu_of_ne (S.other_ne)]
    congr 1
    exact Subtype.ext (S.partner_sourceEdge_c X.1.2)
  rcases (S.incident_x_iff X hX e).mp he with rfl | rfl <;>
    rcases (S.incident_x_iff X hX f).mp hf with rfl | rfl
  · rfl
  · exact hc
  · exact hc.symm
  · rfl

/-- **Every contracted occurrence at the image of a source vertex away from `x` comes from an
occurrence at that vertex.** -/
theorem exists_incident_edgeMap {g : S.D.SourceEdge} {A : data.SourceVertex} (hA : A.1.1 ≠ S.x)
    (h : Incident S.D g (S.vmap A)) : ∃ e : data.SourceEdge, Incident data e A ∧ S.edgeMap e = g := by
  obtain ⟨g₀, rfl⟩ := ContractionFibre.sourceEdgeMap_surjective data (contracted := S.c) rfl
    (fst_ne_snd S.c) S.hOne g
  -- an end of `g₀` has the image of `A`
  have hEnd : ∃ Y : data.SourceVertex, Incident data g₀.1 Y ∧ S.vmap Y = S.vmap A := by
    rcases (WallDegeneration.incident_sourceEdgeMap_iff data rfl (fst_ne_snd S.c) S.hOne g₀ A).mp
      h with hR | hR
    · exact ⟨_, incident_left data _, (ContractionFibre.sourceVertexMap_eq_iff data rfl
        (fst_ne_snd S.c) S.hOne _ _).mpr hR⟩
    · exact ⟨_, incident_right data _, (ContractionFibre.sourceVertexMap_eq_iff data rfl
        (fst_ne_snd S.c) S.hOne _ _).mpr hR⟩
  obtain ⟨Y, hY, hYA⟩ := hEnd
  by_cases hYx : Y.1.1 = S.x
  · -- `g₀` is the other occurrence at `Y`; take the occurrence over `c` at `Y`
    have hNbr : S.cNbr Y = A := by
      rw [S.vmap_cNbr Y hYx] at hYA
      exact (S.vmap_inj (by rw [S.cNbr_target]; exact S.w_ne_x) hA).mp hYA
    have hg₀ : g₀.1 = data.sourceEdge S.other Y.1.2 := by
      rcases (S.incident_x_iff Y hYx g₀.1).mp hY with h' | h'
      · exact absurd (h' ▸ rfl : g₀.1.1.1 = S.c) g₀.2
      · exact h'
    refine ⟨data.sourceEdge S.c Y.1.2, ?_, ?_⟩
    · rw [← hNbr]
      exact (S.incident_c_iff _ _).mpr (Or.inr rfl)
    · unfold edgeMap
      rw [S.mu_of_eq rfl]
      congr 1
      exact Subtype.ext ((S.partner_sourceEdge_c Y.1.2).trans hg₀.symm)
  · have hYA' : Y = A := (S.vmap_inj hYx hA).mp hYA
    refine ⟨g₀.1, hYA' ▸ hY, ?_⟩
    rw [S.edgeMap_of_ne g₀.2]

/-- **The edge map is injective at a source vertex away from `x`.** -/
theorem edgeMap_injOn {A : data.SourceVertex} (hA : A.1.1 ≠ S.x) {e f : data.SourceEdge}
    (he : Incident data e A) (hf : Incident data f A) (h : S.edgeMap e = S.edgeMap f) : e = f := by
  rcases S.edgeMap_eq_imp h with h | ⟨X, hX, heX, hfX⟩
  · exact h
  · -- both meet `A` and `X`; the two occurrences at `X` lie over different target edges
    by_contra hne
    rcases (S.incident_x_iff X hX e).mp heX with rfl | rfl <;>
      rcases (S.incident_x_iff X hX f).mp hfX with rfl | rfl
    · exact hne rfl
    · -- the occurrence over `c` at `X` meets `A` over `w`, the other one meets `A` too
      have hw := (S.incident_c_iff _ _).mp he
      rcases hw with hw | hw
      · exact hA (hw ▸ rfl)
      · have hAw : A.1.1 = S.w := hw ▸ rfl
        have hMem := ((incident_iff_target_mem_and_rel data _ _).mp hf).1
        rw [hAw] at hMem
        exact S.other_not_mem_w hMem
    · have hw := (S.incident_c_iff _ _).mp hf
      rcases hw with hw | hw
      · exact hA (hw ▸ rfl)
      · have hAw : A.1.1 = S.w := hw ▸ rfl
        have hMem := ((incident_iff_target_mem_and_rel data _ _).mp he).1
        rw [hAw] at hMem
        exact S.other_not_mem_w hMem
    · exact hne rfl

/-! ### Surviving valencies -/

/-- **The surviving valency is unchanged away from `x`.** -/
theorem nonDanglingValency_vmap {A : data.SourceVertex} (hA : A.1.1 ≠ S.x) :
    nonDanglingValency S.D (S.vmap A) = nonDanglingValency data A := by
  rw [← card_nonDanglingIncident, ← card_nonDanglingIncident]
  symm
  refine Finset.card_bij (fun e _ ↦ S.edgeMap e) ?_ ?_ ?_
  · intro e he
    obtain ⟨hNd, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp he
    exact (mem_nonDanglingIncident _ _ _).mpr ⟨(S.isDangling_edgeMap_iff e).not.mpr hNd,
      S.incident_edgeMap hA hInc⟩
  · intro e he f hf h
    exact S.edgeMap_injOn hA ((mem_nonDanglingIncident _ _ _).mp he).2
      ((mem_nonDanglingIncident _ _ _).mp hf).2 h
  · intro g hg
    obtain ⟨hNd, hInc⟩ := (mem_nonDanglingIncident _ _ _).mp hg
    obtain ⟨e, he, rfl⟩ := S.exists_incident_edgeMap hA hInc
    exact ⟨e, (mem_nonDanglingIncident _ _ _).mpr
      ⟨(S.isDangling_edgeMap_iff e).not.mp hNd, he⟩, rfl⟩

/-- A source vertex over `x` has surviving valency at most two. -/
theorem nonDanglingValency_le_two {X : data.SourceVertex} (hX : X.1.1 = S.x) :
    nonDanglingValency data X ≤ 2 := by
  have h := nonDanglingValency_le_vertex_degree data X
  rw [vertex_degree_eq_two S.div X hX] at h
  exact_mod_cast h

/-! ### Surviving occurrences -/

/-- The edge map on surviving occurrences. -/
noncomputable def ndMap (e : NonDanglingEdge data) : NonDanglingEdge S.D :=
  ⟨S.edgeMap e.1, (S.isDangling_edgeMap_iff e.1).not.mpr e.2⟩

/-- The surviving-edge map, unfolded. -/
theorem ndMap_val (e : NonDanglingEdge data) : (S.ndMap e).1 = S.edgeMap e.1 := rfl

/-- Every surviving contracted occurrence comes from a surviving occurrence. -/
theorem ndMap_surjective : Function.Surjective S.ndMap := by
  intro g
  obtain ⟨g₀, hg₀⟩ := ContractionFibre.sourceEdgeMap_surjective data (contracted := S.c) rfl
    (fst_ne_snd S.c) S.hOne g.1
  have hEq : S.edgeMap g₀.1 = g.1 := by rw [S.edgeMap_of_ne g₀.2]; exact hg₀
  refine ⟨⟨g₀.1, (S.isDangling_edgeMap_iff g₀.1).not.mp (hEq ▸ g.2)⟩, Subtype.ext hEq⟩

/-- At most two surviving occurrences at a vertex of surviving valency at most two. -/
theorem nonDanglingValency_eq_two_of_ne {X : data.SourceVertex} (hX : X.1.1 = S.x)
    {e f : NonDanglingEdge data} (hne : e ≠ f) (he : Incident data e.1 X) (hf : Incident data f.1 X) :
    nonDanglingValency data X = 2 := by
  refine le_antisymm (S.nonDanglingValency_le_two hX) ?_
  rw [← card_nonDanglingIncident]
  have hSub : ({e.1, f.1} : Finset data.SourceEdge) ⊆ nonDanglingIncident data X := by
    intro g hg
    rcases Finset.mem_insert.mp hg with rfl | hg
    · exact (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, he⟩
    · rw [Finset.mem_singleton.mp hg]
      exact (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hf⟩
  have hCard : ({e.1, f.1} : Finset data.SourceEdge).card = 2 :=
    Finset.card_pair fun h ↦ hne (Subtype.ext h)
  rw [← hCard]
  exact Finset.card_le_card hSub

end Site

end Contraction

end DivalentContraction

end DraismaVargas.Count.MarkedCountGeneral
