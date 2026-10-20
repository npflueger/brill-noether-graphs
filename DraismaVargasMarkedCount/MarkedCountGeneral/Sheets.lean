module

public import DraismaVargasMarkedCount.MarkedCount.RestrictDatum

@[expose] public section

/-!
# Adding and deleting lone sheets of a gluing datum

Restriction (module `Restriction`) splits off the `shed J` index-one
components of a restricted frame, which are sheets alone in their block at every target vertex;
regrowth (module `Regrowth`) adds them back. Both directions are built here, generically, once.

A **sheet decomposition** is an equivalence `σ : Fin d ≃ Fin m ⊕ N`: the old sheets `Fin m` and
the new sheets `N`. Then

* `extendSheets D σ : GluingDatum T d` adds the new sheets to `D : GluingDatum T m`, each alone in
  its block everywhere (`extendPartition`);
* `restrictSheets D σ hLone hm : GluingDatum T m` deletes them from `D : GluingDatum T d`, given
  that every new sheet is **lone** in `D` (`IsLone`: alone in its block at every target vertex,
  hence also over every edge);
* the two are inverse **literally**: `restrictSheets_extendSheets`, `extendSheets_restrictSheets`
  (equalities of data, by `gluingDatum_ext`).

Dictionaries (all definitional):

* `extendSheets`: `oldSV`, `newSV`, `oldSE`, `newSE`, with the equivalences `extendSVEquiv`,
  `extendSEEquiv` from `D.SourceVertex ⊕ (T.V × N)` and `D.SourceEdge ⊕ (T.edges × N)`; ends,
  incidence, indices, block sizes, local ramification (`0` at a new vertex) and Riemann--Hurwitz;
* `restrictSheets`: `inclSV`, `loneSV`, `inclSE`, `loneSE`, with `restrictSVEquiv`,
  `restrictSEEquiv` onto `D.SourceVertex`, `D.SourceEdge`; the same compatibilities;
* isomorphisms: `extendSheetsIso` (an isomorphism of the old data, the identity on the new sheets),
  `restrictSheetsIso` (an isomorphism carrying new sheets to new sheets), and the computation of
  their source dictionaries.

Connectedness is not here: `extendSheets` is never connected when `N` is nonempty, and whether a
restriction is connected depends on the caller.
-/

namespace DraismaVargas.Count.MarkedCountGeneral.Sheets

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.Count (GeometricDatumIso)

/-! ## 1.  Partitions -/

section Partition

variable {d m : ℕ} {N : Type*}

/-- `i` is a **new sheet** of the decomposition `σ`. -/
def IsNew (σ : Fin d ≃ Fin m ⊕ N) (i : Fin d) : Prop := (σ i).isRight

instance (σ : Fin d ≃ Fin m ⊕ N) (i : Fin d) : Decidable (IsNew σ i) := by
  unfold IsNew; infer_instance

@[simp] theorem isNew_inr (σ : Fin d ≃ Fin m ⊕ N) (n : N) : IsNew σ (σ.symm (.inr n)) := by
  simp [IsNew]

@[simp] theorem not_isNew_inl (σ : Fin d ≃ Fin m ⊕ N) (a : Fin m) :
    ¬ IsNew σ (σ.symm (.inl a)) := by
  simp [IsNew]

/-- Every sheet is old or new. -/
theorem sheet_cases (σ : Fin d ≃ Fin m ⊕ N) (i : Fin d) :
    (∃ a, σ.symm (.inl a) = i) ∨ ∃ n, σ.symm (.inr n) = i := by
  rcases h : σ i with a | n
  · exact Or.inl ⟨a, by rw [← h, Equiv.symm_apply_apply]⟩
  · exact Or.inr ⟨n, by rw [← h, Equiv.symm_apply_apply]⟩

theorem isNew_iff (σ : Fin d ≃ Fin m ⊕ N) (i : Fin d) : IsNew σ i ↔ ∃ n, σ.symm (.inr n) = i := by
  rcases sheet_cases σ i with ⟨a, rfl⟩ | ⟨n, rfl⟩
  · simp only [not_isNew_inl, false_iff, not_exists]
    intro n h
    simpa using congrArg σ h
  · simp

/-- **The extended partition**: the old partition on the old sheets, every new sheet alone. -/
def extendPartition (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N) : SheetPartition d where
  repr i := Sum.elim (fun a ↦ σ.symm (.inl (P.repr a))) (fun _ ↦ i) (σ i)
  repr_idem i := by
    rcases h : σ i with a | n
    · simp [P.repr_idem]
    · simp [h]

@[simp] theorem extendPartition_repr_inl (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N)
    (a : Fin m) : (extendPartition P σ).repr (σ.symm (.inl a)) = σ.symm (.inl (P.repr a)) := by
  simp [extendPartition]

@[simp] theorem extendPartition_repr_inr (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N) (n : N) :
    (extendPartition P σ).repr (σ.symm (.inr n)) = σ.symm (.inr n) := by
  simp [extendPartition]

theorem extendPartition_rel_inl_inl (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N)
    (a b : Fin m) :
    (extendPartition P σ).Rel (σ.symm (.inl a)) (σ.symm (.inl b)) ↔ P.Rel a b := by
  simp [SheetPartition.Rel]

theorem extendPartition_rel_inr (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N) (n : N)
    (j : Fin d) : (extendPartition P σ).Rel (σ.symm (.inr n)) j ↔ j = σ.symm (.inr n) := by
  rcases sheet_cases σ j with ⟨b, rfl⟩ | ⟨n', rfl⟩
  · simp only [SheetPartition.rel_iff, extendPartition_repr_inr, extendPartition_repr_inl,
      EmbeddingLike.apply_eq_iff_eq, reduceCtorEq]
  · simp only [SheetPartition.rel_iff, extendPartition_repr_inr, EmbeddingLike.apply_eq_iff_eq,
      Sum.inr.injEq]
    exact eq_comm

theorem extendPartition_rel_inl_inr (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N) (a : Fin m)
    (n : N) : ¬ (extendPartition P σ).Rel (σ.symm (.inl a)) (σ.symm (.inr n)) := by
  intro h
  have := (extendPartition_rel_inr P σ n _).mp h.symm
  simpa using congrArg σ this

theorem extendPartition_refines {P Q : SheetPartition m} (h : P.Refines Q)
    (σ : Fin d ≃ Fin m ⊕ N) : (extendPartition P σ).Refines (extendPartition Q σ) := by
  intro i j hij
  rcases sheet_cases σ i with ⟨a, rfl⟩ | ⟨n, rfl⟩
  · rcases sheet_cases σ j with ⟨b, rfl⟩ | ⟨n', rfl⟩
    · exact (extendPartition_rel_inl_inl Q σ a b).mpr
        (h a b ((extendPartition_rel_inl_inl P σ a b).mp hij))
    · exact absurd hij (extendPartition_rel_inl_inr P σ a n')
  · rw [(extendPartition_rel_inr P σ n j).mp hij]
    exact SheetPartition.rel_repr_left _ _ |>.symm.trans (SheetPartition.rel_repr_left _ _)

/-- **The restricted partition**, on the old sheets, when no new sheet shares a block. -/
def restrictPartition (P : SheetPartition d) (σ : Fin d ≃ Fin m ⊕ N)
    (_hLone : ∀ n j, P.Rel (σ.symm (.inr n)) j → j = σ.symm (.inr n)) : SheetPartition m where
  repr a := Sum.elim id (fun _ ↦ a) (σ (P.repr (σ.symm (.inl a))))
  repr_idem a := by
    rcases h : σ (P.repr (σ.symm (.inl a))) with b | n
    · have hb : σ.symm (.inl b) = P.repr (σ.symm (.inl a)) := by rw [← h]; simp
      simp only [Sum.elim_inl, id_eq]
      rw [hb, P.repr_idem, h]
      rfl
    · simp only [Sum.elim_inr, h]

variable {P : SheetPartition d} {σ : Fin d ≃ Fin m ⊕ N}
  {hLone : ∀ n j, P.Rel (σ.symm (.inr n)) j → j = σ.symm (.inr n)}

/-- The representative of an old sheet is old. -/
theorem restrictPartition_spec (a : Fin m) :
    σ (P.repr (σ.symm (.inl a))) = .inl ((restrictPartition P σ hLone).repr a) := by
  rcases h : σ (P.repr (σ.symm (.inl a))) with b | n
  · simp [restrictPartition, h]
  · exfalso
    have hn : σ.symm (.inr n) = P.repr (σ.symm (.inl a)) := by rw [← h]; simp
    have hRel : P.Rel (σ.symm (.inr n)) (σ.symm (.inl a)) := by
      rw [SheetPartition.rel_iff, hn, P.repr_idem]
    have := hLone n _ hRel
    simpa using congrArg σ this

theorem restrictPartition_repr (a : Fin m) :
    σ.symm (.inl ((restrictPartition P σ hLone).repr a)) = P.repr (σ.symm (.inl a)) := by
  rw [← restrictPartition_spec]; simp

theorem restrictPartition_rel_iff (a b : Fin m) :
    (restrictPartition P σ hLone).Rel a b ↔ P.Rel (σ.symm (.inl a)) (σ.symm (.inl b)) := by
  rw [SheetPartition.rel_iff, SheetPartition.rel_iff, ← restrictPartition_repr (hLone := hLone),
    ← restrictPartition_repr (hLone := hLone)]
  simp

end Partition

/-! ### Splitting off a set of sheets -/

/-- **The decomposition splitting off a set `S` of sheets**: old sheets the complement, numbered
by `Fin m`, new sheets `S`, numbered by `Fin s`. -/
noncomputable def splitBy (S : Finset (Fin d)) (m s : ℕ) (hm : m + s = d) (hs : S.card = s) :
    Fin d ≃ Fin m ⊕ Fin s :=
  ((Equiv.sumCompl (· ∈ S)).symm.trans (Equiv.sumComm _ _)).trans
    (Equiv.sumCongr (Fintype.equivFinOfCardEq (by
        rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]; omega))
      (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe, hs])))

theorem isNew_splitBy (S : Finset (Fin d)) (m s : ℕ) (hm : m + s = d) (hs : S.card = s)
    (i : Fin d) : IsNew (splitBy S m s hm hs) i ↔ i ∈ S := by
  unfold IsNew splitBy
  by_cases h : i ∈ S
  · simp [Equiv.sumCompl, h]
  · simp [Equiv.sumCompl, h]

/-! ## 2.  Lone sheets -/

section Lone

variable {T : CFGraph} {d : ℕ}

/-- **A lone sheet**: alone in its block at every target vertex. -/
def IsLone (D : GluingDatum T d) (i : Fin d) : Prop :=
  ∀ v j, (D.vertexPartition v).Rel i j → j = i

variable {D : GluingDatum T d} {i : Fin d}

/-- A lone sheet is alone over every edge (edges refine their ends). -/
theorem IsLone.edge (h : IsLone D i) (e : T.edges) (j : Fin d)
    (hij : (D.edgePartition e).Rel i j) : j = i :=
  h _ j ((D.refines_left e).rel hij)

theorem IsLone.repr_vertex (h : IsLone D i) (v : T.V) : (D.vertexPartition v).repr i = i :=
  h v _ ((D.vertexPartition v).rel_repr_right i)

theorem IsLone.repr_edge (h : IsLone D i) (e : T.edges) : (D.edgePartition e).repr i = i :=
  h.edge e _ ((D.edgePartition e).rel_repr_right i)

theorem IsLone.blockCard_vertex (h : IsLone D i) (v : T.V) :
    (D.vertexPartition v).blockCard i = 1 := by
  unfold SheetPartition.blockCard
  rw [Finset.card_eq_one]
  exact ⟨i, Finset.eq_singleton_iff_unique_mem.mpr ⟨(D.vertexPartition v).self_mem_block i,
    fun j hj ↦ h v j ((SheetPartition.mem_block_iff _ _ _).mp hj)⟩⟩

theorem IsLone.blockCard_edge (h : IsLone D i) (e : T.edges) :
    (D.edgePartition e).blockCard i = 1 := by
  unfold SheetPartition.blockCard
  rw [Finset.card_eq_one]
  exact ⟨i, Finset.eq_singleton_iff_unique_mem.mpr ⟨(D.edgePartition e).self_mem_block i,
    fun j hj ↦ h.edge e j ((SheetPartition.mem_block_iff _ _ _).mp hj)⟩⟩

end Lone

/-! ## 3.  The two data -/

section Data

variable {T : CFGraph} {d m : ℕ} {N : Type*}

/-- **Adding lone sheets**: the old data on the old sheets, every new sheet alone everywhere. -/
def extendSheets (D : GluingDatum T m) (σ : Fin d ≃ Fin m ⊕ N) : GluingDatum T d where
  degree_pos := (σ.symm (.inl ⟨0, D.degree_pos⟩)).pos
  vertexPartition v := extendPartition (D.vertexPartition v) σ
  edgePartition e := extendPartition (D.edgePartition e) σ
  refines_left e := extendPartition_refines (D.refines_left e) σ
  refines_right e := extendPartition_refines (D.refines_right e) σ

@[simp] theorem extendSheets_vertexPartition (D : GluingDatum T m) (σ : Fin d ≃ Fin m ⊕ N)
    (v : T.V) : (extendSheets D σ).vertexPartition v = extendPartition (D.vertexPartition v) σ :=
  rfl

@[simp] theorem extendSheets_edgePartition (D : GluingDatum T m) (σ : Fin d ≃ Fin m ⊕ N)
    (e : T.edges) : (extendSheets D σ).edgePartition e = extendPartition (D.edgePartition e) σ :=
  rfl

/-- The new sheets of an extension are lone. -/
theorem isLone_extendSheets (D : GluingDatum T m) (σ : Fin d ≃ Fin m ⊕ N) (n : N) :
    IsLone (extendSheets D σ) (σ.symm (.inr n)) :=
  fun v j h ↦ (extendPartition_rel_inr (D.vertexPartition v) σ n j).mp h

/-- **Deleting lone sheets**: the partitions read on the old sheets. -/
def restrictSheets (D : GluingDatum T d) (σ : Fin d ≃ Fin m ⊕ N)
    (hLone : ∀ n, IsLone D (σ.symm (.inr n))) (hm : 0 < m) : GluingDatum T m where
  degree_pos := hm
  vertexPartition v := restrictPartition (D.vertexPartition v) σ (fun n j h ↦ hLone n v j h)
  edgePartition e := restrictPartition (D.edgePartition e) σ (fun n j h ↦ (hLone n).edge e j h)
  refines_left e a b h := (restrictPartition_rel_iff a b).mpr
    ((D.refines_left e).rel ((restrictPartition_rel_iff a b).mp h))
  refines_right e a b h := (restrictPartition_rel_iff a b).mpr
    ((D.refines_right e).rel ((restrictPartition_rel_iff a b).mp h))

variable {D : GluingDatum T d} {σ : Fin d ≃ Fin m ⊕ N} {hLone : ∀ n, IsLone D (σ.symm (.inr n))}
  {hm : 0 < m}

theorem restrictSheets_vertex_rel_iff (v : T.V) (a b : Fin m) :
    ((restrictSheets D σ hLone hm).vertexPartition v).Rel a b ↔
      (D.vertexPartition v).Rel (σ.symm (.inl a)) (σ.symm (.inl b)) :=
  restrictPartition_rel_iff (hLone := fun n j h ↦ hLone n v j h) a b

theorem restrictSheets_edge_rel_iff (e : T.edges) (a b : Fin m) :
    ((restrictSheets D σ hLone hm).edgePartition e).Rel a b ↔
      (D.edgePartition e).Rel (σ.symm (.inl a)) (σ.symm (.inl b)) :=
  restrictPartition_rel_iff (hLone := fun n j h ↦ (hLone n).edge e j h) a b

theorem restrictSheets_vertex_repr (v : T.V) (a : Fin m) :
    σ.symm (.inl (((restrictSheets D σ hLone hm).vertexPartition v).repr a)) =
      (D.vertexPartition v).repr (σ.symm (.inl a)) :=
  restrictPartition_repr (hLone := fun n j h ↦ hLone n v j h) a

theorem restrictSheets_edge_repr (e : T.edges) (a : Fin m) :
    σ.symm (.inl (((restrictSheets D σ hLone hm).edgePartition e).repr a)) =
      (D.edgePartition e).repr (σ.symm (.inl a)) :=
  restrictPartition_repr (hLone := fun n j h ↦ (hLone n).edge e j h) a

/-! ### The round trips, literally -/

/-- **Deleting the added sheets gives back the datum**, literally. -/
theorem restrictSheets_extendSheets (D : GluingDatum T m) (σ : Fin d ≃ Fin m ⊕ N) :
    restrictSheets (extendSheets D σ) σ (isLone_extendSheets D σ) D.degree_pos = D := by
  refine gluingDatum_ext (funext fun v ↦ ?_) (funext fun e ↦ ?_)
  · refine SheetPartition.ext_repr _ _ (funext fun a ↦ ?_)
    have h := restrictSheets_vertex_repr (D := extendSheets D σ) (σ := σ)
      (hLone := isLone_extendSheets D σ) (hm := D.degree_pos) v a
    rw [extendSheets_vertexPartition, extendPartition_repr_inl] at h
    simpa using h
  · refine SheetPartition.ext_repr _ _ (funext fun a ↦ ?_)
    have h := restrictSheets_edge_repr (D := extendSheets D σ) (σ := σ)
      (hLone := isLone_extendSheets D σ) (hm := D.degree_pos) e a
    rw [extendSheets_edgePartition, extendPartition_repr_inl] at h
    simpa using h

/-- **Adding back the deleted sheets gives back the datum**, literally. -/
theorem extendSheets_restrictSheets (D : GluingDatum T d) (σ : Fin d ≃ Fin m ⊕ N)
    (hLone : ∀ n, IsLone D (σ.symm (.inr n))) (hm : 0 < m) :
    extendSheets (restrictSheets D σ hLone hm) σ = D := by
  refine gluingDatum_ext (funext fun v ↦ ?_) (funext fun e ↦ ?_)
  · refine SheetPartition.ext_repr _ _ (funext fun i ↦ ?_)
    rcases sheet_cases σ i with ⟨a, rfl⟩ | ⟨n, rfl⟩
    · rw [extendSheets_vertexPartition, extendPartition_repr_inl, restrictSheets_vertex_repr]
    · rw [extendSheets_vertexPartition, extendPartition_repr_inr, (hLone n).repr_vertex]
  · refine SheetPartition.ext_repr _ _ (funext fun i ↦ ?_)
    rcases sheet_cases σ i with ⟨a, rfl⟩ | ⟨n, rfl⟩
    · rw [extendSheets_edgePartition, extendPartition_repr_inl, restrictSheets_edge_repr]
    · rw [extendSheets_edgePartition, extendPartition_repr_inr, (hLone n).repr_edge]

end Data

/-! ## 4.  Block sizes and block counts -/

section Counts

variable {d m : ℕ} {N : Type*}

/-- The old sheets, as an embedding. -/
def oldEmb (σ : Fin d ≃ Fin m ⊕ N) : Fin m ↪ Fin d :=
  ⟨fun b ↦ σ.symm (.inl b), fun b c h ↦ by simpa using h⟩

@[simp] theorem oldEmb_apply (σ : Fin d ≃ Fin m ⊕ N) (b : Fin m) :
    oldEmb σ b = σ.symm (.inl b) := rfl

/-- The block of an old sheet in an extension is the image of its old block. -/
theorem extendPartition_block_inl (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N) (a : Fin m) :
    (extendPartition P σ).block (σ.symm (.inl a)) = (P.block a).map (oldEmb σ) := by
  ext j
  simp only [SheetPartition.mem_block_iff, Finset.mem_map, oldEmb_apply]
  rcases sheet_cases σ j with ⟨b, rfl⟩ | ⟨n, rfl⟩
  · rw [extendPartition_rel_inl_inl]
    constructor
    · exact fun h ↦ ⟨b, h, rfl⟩
    · rintro ⟨c, hc, hcb⟩
      have : c = b := by simpa using hcb
      exact this ▸ hc
  · simp only [extendPartition_rel_inl_inr, false_iff, not_exists, not_and]
    intro c _ h
    have := congrArg σ h
    simp at this

@[simp] theorem extendPartition_blockCard_inl (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N)
    (a : Fin m) : (extendPartition P σ).blockCard (σ.symm (.inl a)) = P.blockCard a := by
  unfold SheetPartition.blockCard
  rw [extendPartition_block_inl, Finset.card_map]

@[simp] theorem extendPartition_blockCard_inr (P : SheetPartition m) (σ : Fin d ≃ Fin m ⊕ N)
    (n : N) : (extendPartition P σ).blockCard (σ.symm (.inr n)) = 1 := by
  unfold SheetPartition.blockCard
  rw [Finset.card_eq_one]
  refine ⟨σ.symm (.inr n), Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, rfl⟩, fun j hj ↦ ?_⟩⟩
  exact (extendPartition_rel_inr P σ n j).mp ((SheetPartition.mem_block_iff _ _ _).mp hj)

@[simp] theorem extendPartition_blockCountWithin_inl (fine coarse : SheetPartition m)
    (σ : Fin d ≃ Fin m ⊕ N) (a : Fin m) :
    (extendPartition fine σ).blockCountWithin (extendPartition coarse σ) (σ.symm (.inl a)) =
      fine.blockCountWithin coarse a := by
  classical
  unfold SheetPartition.blockCountWithin
  rw [extendPartition_block_inl, Finset.map_eq_image, Finset.image_image]
  have : ((extendPartition fine σ).repr ∘ oldEmb σ) = oldEmb σ ∘ fine.repr := by
    funext b; simp
  rw [this, ← Finset.image_image, Finset.card_image_of_injective _ (oldEmb σ).injective]

@[simp] theorem extendPartition_blockCountWithin_inr (fine coarse : SheetPartition m)
    (σ : Fin d ≃ Fin m ⊕ N) (n : N) :
    (extendPartition fine σ).blockCountWithin (extendPartition coarse σ) (σ.symm (.inr n)) = 1 := by
  classical
  unfold SheetPartition.blockCountWithin
  rw [SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _
    (extendPartition_blockCard_inr coarse σ n)]
  simp

/-- **The partition-level round trip.** -/
theorem extendPartition_restrictPartition (P : SheetPartition d) (σ : Fin d ≃ Fin m ⊕ N)
    (hLone : ∀ n j, P.Rel (σ.symm (.inr n)) j → j = σ.symm (.inr n)) :
    extendPartition (restrictPartition P σ hLone) σ = P := by
  refine SheetPartition.ext_repr _ _ (funext fun i ↦ ?_)
  rcases sheet_cases σ i with ⟨a, rfl⟩ | ⟨n, rfl⟩
  · rw [extendPartition_repr_inl, restrictPartition_repr]
  · rw [extendPartition_repr_inr]
    exact (hLone n _ (P.rel_repr_right _)).symm

theorem restrictPartition_blockCard (P : SheetPartition d) (σ : Fin d ≃ Fin m ⊕ N)
    (hLone : ∀ n j, P.Rel (σ.symm (.inr n)) j → j = σ.symm (.inr n)) (a : Fin m) :
    (restrictPartition P σ hLone).blockCard a = P.blockCard (σ.symm (.inl a)) := by
  conv_rhs => rw [← extendPartition_restrictPartition P σ hLone]
  rw [extendPartition_blockCard_inl]

theorem restrictPartition_blockCountWithin (fine coarse : SheetPartition d)
    (σ : Fin d ≃ Fin m ⊕ N)
    (hFine : ∀ n j, fine.Rel (σ.symm (.inr n)) j → j = σ.symm (.inr n))
    (hCoarse : ∀ n j, coarse.Rel (σ.symm (.inr n)) j → j = σ.symm (.inr n)) (a : Fin m) :
    (restrictPartition fine σ hFine).blockCountWithin (restrictPartition coarse σ hCoarse) a =
      fine.blockCountWithin coarse (σ.symm (.inl a)) := by
  conv_rhs => rw [← extendPartition_restrictPartition fine σ hFine,
    ← extendPartition_restrictPartition coarse σ hCoarse]
  rw [extendPartition_blockCountWithin_inl]

/-- Relabelling commutes with extension, by the permutation that fixes the new sheets. -/
def extendPerm (α : Equiv.Perm (Fin m)) (σ₁ σ₂ : Fin d ≃ Fin m ⊕ N) : Equiv.Perm (Fin d) :=
  σ₁.trans ((Equiv.sumCongr α (Equiv.refl N)).trans σ₂.symm)

@[simp] theorem extendPerm_inl (α : Equiv.Perm (Fin m)) (σ₁ σ₂ : Fin d ≃ Fin m ⊕ N) (a : Fin m) :
    extendPerm α σ₁ σ₂ (σ₁.symm (.inl a)) = σ₂.symm (.inl (α a)) := by
  simp [extendPerm]

@[simp] theorem extendPerm_inr (α : Equiv.Perm (Fin m)) (σ₁ σ₂ : Fin d ≃ Fin m ⊕ N) (n : N) :
    extendPerm α σ₁ σ₂ (σ₁.symm (.inr n)) = σ₂.symm (.inr n) := by
  simp [extendPerm]

@[simp] theorem extendPerm_symm_inl (α : Equiv.Perm (Fin m)) (σ₁ σ₂ : Fin d ≃ Fin m ⊕ N)
    (a : Fin m) : (extendPerm α σ₁ σ₂).symm (σ₂.symm (.inl a)) = σ₁.symm (.inl (α.symm a)) := by
  simp [extendPerm, Equiv.sumCongr_symm]

@[simp] theorem extendPerm_symm_inr (α : Equiv.Perm (Fin m)) (σ₁ σ₂ : Fin d ≃ Fin m ⊕ N)
    (n : N) : (extendPerm α σ₁ σ₂).symm (σ₂.symm (.inr n)) = σ₁.symm (.inr n) := by
  simp [extendPerm, Equiv.sumCongr_symm]

theorem extendPartition_relabel (P : SheetPartition m) (α : Equiv.Perm (Fin m))
    (σ₁ σ₂ : Fin d ≃ Fin m ⊕ N) :
    extendPartition (P.relabel α) σ₂ = (extendPartition P σ₁).relabel (extendPerm α σ₁ σ₂) := by
  refine SheetPartition.ext_repr _ _ (funext fun i ↦ ?_)
  rcases sheet_cases σ₂ i with ⟨a, rfl⟩ | ⟨n, rfl⟩
  · change _ = extendPerm α σ₁ σ₂ ((extendPartition P σ₁).repr ((extendPerm α σ₁ σ₂).symm _))
    simp only [extendPerm_symm_inl, extendPartition_repr_inl, extendPerm_inl]
    simp [SheetPartition.relabel]
  · change _ = extendPerm α σ₁ σ₂ ((extendPartition P σ₁).repr ((extendPerm α σ₁ σ₂).symm _))
    simp only [extendPerm_symm_inr, extendPartition_repr_inr, extendPerm_inr]

end Counts

/-! ## 5.  The dictionaries of an extension -/

section ExtendDict

variable {T : CFGraph} {d m : ℕ} {N : Type*} (D : GluingDatum T m) (σ : Fin d ≃ Fin m ⊕ N)

/-- An old source vertex of the extension. -/
def oldSV (X : D.SourceVertex) : (extendSheets D σ).SourceVertex :=
  ⟨(X.1.1, σ.symm (.inl X.1.2)), by
    show (extendPartition (D.vertexPartition X.1.1) σ).repr (σ.symm (.inl X.1.2)) = _
    rw [extendPartition_repr_inl, X.2]⟩

/-- The source vertex of the new sheet `n` over `v`. -/
def newSV (v : T.V) (n : N) : (extendSheets D σ).SourceVertex :=
  ⟨(v, σ.symm (.inr n)), by
    show (extendPartition (D.vertexPartition v) σ).repr (σ.symm (.inr n)) = _
    rw [extendPartition_repr_inr]⟩

/-- An old source edge of the extension. -/
def oldSE (F : D.SourceEdge) : (extendSheets D σ).SourceEdge :=
  ⟨(F.1.1, σ.symm (.inl F.1.2)), by
    show (extendPartition (D.edgePartition F.1.1) σ).repr (σ.symm (.inl F.1.2)) = _
    rw [extendPartition_repr_inl, F.2]⟩

/-- The source edge of the new sheet `n` over `e`. -/
def newSE (e : T.edges) (n : N) : (extendSheets D σ).SourceEdge :=
  ⟨(e, σ.symm (.inr n)), by
    show (extendPartition (D.edgePartition e) σ).repr (σ.symm (.inr n)) = _
    rw [extendPartition_repr_inr]⟩

variable {D σ}

theorem oldSV_injective : Function.Injective (oldSV D σ) := by
  intro X Y h
  have h1 := congrArg (fun Z : (extendSheets D σ).SourceVertex ↦ Z.1.1) h
  have h2 := congrArg (fun Z : (extendSheets D σ).SourceVertex ↦ σ Z.1.2) h
  simp only [oldSV, Equiv.apply_symm_apply, Sum.inl.injEq] at h1 h2
  exact Subtype.ext (Prod.ext h1 h2)

theorem oldSE_injective : Function.Injective (oldSE D σ) := by
  intro X Y h
  have h1 := congrArg (fun Z : (extendSheets D σ).SourceEdge ↦ Z.1.1) h
  have h2 := congrArg (fun Z : (extendSheets D σ).SourceEdge ↦ σ Z.1.2) h
  simp only [oldSE, Equiv.apply_symm_apply, Sum.inl.injEq] at h1 h2
  exact Subtype.ext (Prod.ext h1 h2)

theorem oldSV_ne_newSV (X : D.SourceVertex) (v : T.V) (n : N) : oldSV D σ X ≠ newSV D σ v n := by
  intro h
  have := congrArg (fun Z : (extendSheets D σ).SourceVertex ↦ σ Z.1.2) h
  simp [oldSV, newSV] at this

theorem oldSE_ne_newSE (F : D.SourceEdge) (e : T.edges) (n : N) :
    oldSE D σ F ≠ newSE D σ e n := by
  intro h
  have := congrArg (fun Z : (extendSheets D σ).SourceEdge ↦ σ Z.1.2) h
  simp [oldSE, newSE] at this

@[simp] theorem newSV_inj {v w : T.V} {n n' : N} :
    newSV D σ v n = newSV D σ w n' ↔ v = w ∧ n = n' := by
  constructor
  · intro h
    have h1 := congrArg (fun Z : (extendSheets D σ).SourceVertex ↦ Z.1.1) h
    have h2 := congrArg (fun Z : (extendSheets D σ).SourceVertex ↦ σ Z.1.2) h
    simp only [newSV, Equiv.apply_symm_apply, Sum.inr.injEq] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem newSE_inj {e f : T.edges} {n n' : N} :
    newSE D σ e n = newSE D σ f n' ↔ e = f ∧ n = n' := by
  constructor
  · intro h
    have h1 := congrArg (fun Z : (extendSheets D σ).SourceEdge ↦ Z.1.1) h
    have h2 := congrArg (fun Z : (extendSheets D σ).SourceEdge ↦ σ Z.1.2) h
    simp only [newSE, Equiv.apply_symm_apply, Sum.inr.injEq] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Every source vertex of an extension is old or new. -/
theorem extend_sourceVertex_cases (X : (extendSheets D σ).SourceVertex) :
    (∃ Y, oldSV D σ Y = X) ∨ ∃ n, newSV D σ X.1.1 n = X := by
  rcases sheet_cases σ X.1.2 with ⟨a, ha⟩ | ⟨n, hn⟩
  · refine Or.inl ⟨⟨(X.1.1, a), ?_⟩, Subtype.ext (Prod.ext rfl ha)⟩
    have h := X.2
    change (extendPartition _ σ).repr X.1.2 = X.1.2 at h
    rw [← ha, extendPartition_repr_inl] at h
    simpa using h
  · exact Or.inr ⟨n, Subtype.ext (Prod.ext rfl hn)⟩

/-- Every source edge of an extension is old or new. -/
theorem extend_sourceEdge_cases (E : (extendSheets D σ).SourceEdge) :
    (∃ F, oldSE D σ F = E) ∨ ∃ n, newSE D σ E.1.1 n = E := by
  rcases sheet_cases σ E.1.2 with ⟨a, ha⟩ | ⟨n, hn⟩
  · refine Or.inl ⟨⟨(E.1.1, a), ?_⟩, Subtype.ext (Prod.ext rfl ha)⟩
    have h := E.2
    change (extendPartition _ σ).repr E.1.2 = E.1.2 at h
    rw [← ha, extendPartition_repr_inl] at h
    simpa using h
  · exact Or.inr ⟨n, Subtype.ext (Prod.ext rfl hn)⟩

variable (D σ) in
/-- **The source-vertex dictionary of an extension.** -/
noncomputable def extendSVEquiv : D.SourceVertex ⊕ (T.V × N) ≃ (extendSheets D σ).SourceVertex :=
  Equiv.ofBijective (Sum.elim (oldSV D σ) fun q ↦ newSV D σ q.1 q.2) (by
    constructor
    · rintro (X | ⟨v, n⟩) (Y | ⟨w, n'⟩) h
      · exact congrArg Sum.inl (oldSV_injective h)
      · exact absurd h (oldSV_ne_newSV _ _ _)
      · exact absurd h.symm (oldSV_ne_newSV _ _ _)
      · obtain ⟨rfl, rfl⟩ := newSV_inj.mp h; rfl
    · intro X
      rcases extend_sourceVertex_cases X with ⟨Y, rfl⟩ | ⟨n, hn⟩
      · exact ⟨.inl Y, rfl⟩
      · exact ⟨.inr (X.1.1, n), hn⟩)

variable (D σ) in
/-- **The source-edge dictionary of an extension.** -/
noncomputable def extendSEEquiv : D.SourceEdge ⊕ (T.edges × N) ≃ (extendSheets D σ).SourceEdge :=
  Equiv.ofBijective (Sum.elim (oldSE D σ) fun q ↦ newSE D σ q.1 q.2) (by
    constructor
    · rintro (X | ⟨v, n⟩) (Y | ⟨w, n'⟩) h
      · exact congrArg Sum.inl (oldSE_injective h)
      · exact absurd h (oldSE_ne_newSE _ _ _)
      · exact absurd h.symm (oldSE_ne_newSE _ _ _)
      · obtain ⟨rfl, rfl⟩ := newSE_inj.mp h; rfl
    · intro E
      rcases extend_sourceEdge_cases E with ⟨F, rfl⟩ | ⟨n, hn⟩
      · exact ⟨.inl F, rfl⟩
      · exact ⟨.inr (E.1.1, n), hn⟩)

@[simp] theorem extendSVEquiv_inl (X : D.SourceVertex) :
    extendSVEquiv D σ (.inl X) = oldSV D σ X := rfl

@[simp] theorem extendSVEquiv_inr (v : T.V) (n : N) :
    extendSVEquiv D σ (.inr (v, n)) = newSV D σ v n := rfl

@[simp] theorem extendSEEquiv_inl (F : D.SourceEdge) :
    extendSEEquiv D σ (.inl F) = oldSE D σ F := rfl

@[simp] theorem extendSEEquiv_inr (e : T.edges) (n : N) :
    extendSEEquiv D σ (.inr (e, n)) = newSE D σ e n := rfl

theorem extend_sourceEndpoint_inl (v : T.V) (a : Fin m) :
    (extendSheets D σ).sourceEndpoint v (σ.symm (.inl a)) = oldSV D σ (D.sourceEndpoint v a) := by
  apply Subtype.ext
  change (v, (extendPartition _ σ).repr _) = (v, σ.symm (.inl ((D.vertexPartition v).repr a)))
  rw [extendPartition_repr_inl]

theorem extend_sourceEndpoint_inr (v : T.V) (n : N) :
    (extendSheets D σ).sourceEndpoint v (σ.symm (.inr n)) = newSV D σ v n := by
  apply Subtype.ext
  change (v, (extendPartition _ σ).repr _) = (v, σ.symm (.inr n))
  rw [extendPartition_repr_inr]

@[simp] theorem extend_sourceEnds_oldSE (F : D.SourceEdge) :
    (extendSheets D σ).sourceEnds (oldSE D σ F) =
      (oldSV D σ (D.sourceEnds F).1, oldSV D σ (D.sourceEnds F).2) := by
  change ((extendSheets D σ).sourceEndpoint _ (σ.symm (.inl F.1.2)),
    (extendSheets D σ).sourceEndpoint _ (σ.symm (.inl F.1.2))) = _
  rw [extend_sourceEndpoint_inl, extend_sourceEndpoint_inl]
  rfl

@[simp] theorem extend_sourceEnds_newSE (e : T.edges) (n : N) :
    (extendSheets D σ).sourceEnds (newSE D σ e n) =
      (newSV D σ (e : T.V × T.V).1 n, newSV D σ (e : T.V × T.V).2 n) := by
  change ((extendSheets D σ).sourceEndpoint _ (σ.symm (.inr n)),
    (extendSheets D σ).sourceEndpoint _ (σ.symm (.inr n))) = _
  rw [extend_sourceEndpoint_inr, extend_sourceEndpoint_inr]
  rfl

theorem extend_incident_oldSE_oldSV (F : D.SourceEdge) (X : D.SourceVertex) :
    Incident (extendSheets D σ) (oldSE D σ F) (oldSV D σ X) ↔ Incident D F X := by
  unfold Incident
  rw [extend_sourceEnds_oldSE]
  simp only [oldSV_injective.eq_iff]

theorem extend_not_incident_oldSE_newSV (F : D.SourceEdge) (v : T.V) (n : N) :
    ¬ Incident (extendSheets D σ) (oldSE D σ F) (newSV D σ v n) := by
  unfold Incident
  rw [extend_sourceEnds_oldSE]
  rintro (h | h) <;> exact oldSV_ne_newSV _ _ _ h

theorem extend_not_incident_newSE_oldSV (e : T.edges) (n : N) (X : D.SourceVertex) :
    ¬ Incident (extendSheets D σ) (newSE D σ e n) (oldSV D σ X) := by
  unfold Incident
  rw [extend_sourceEnds_newSE]
  rintro (h | h) <;> exact oldSV_ne_newSV _ _ _ h.symm

theorem extend_incident_newSE_newSV (e : T.edges) (n n' : N) (v : T.V) :
    Incident (extendSheets D σ) (newSE D σ e n) (newSV D σ v n') ↔
      n = n' ∧ ((e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v) := by
  unfold Incident
  rw [extend_sourceEnds_newSE]
  simp only [newSV_inj]
  tauto

@[simp] theorem extend_sourceEdgeIndex_oldSE (F : D.SourceEdge) :
    (extendSheets D σ).sourceEdgeIndex (oldSE D σ F) = D.sourceEdgeIndex F :=
  extendPartition_blockCard_inl _ σ _

@[simp] theorem extend_sourceEdgeIndex_newSE (e : T.edges) (n : N) :
    (extendSheets D σ).sourceEdgeIndex (newSE D σ e n) = 1 :=
  extendPartition_blockCard_inr _ σ _

@[simp] theorem extend_blockCard_oldSV (X : D.SourceVertex) :
    ((extendSheets D σ).vertexPartition (oldSV D σ X).1.1).blockCard (oldSV D σ X).1.2 =
      (D.vertexPartition X.1.1).blockCard X.1.2 :=
  extendPartition_blockCard_inl _ σ _

@[simp] theorem extend_blockCard_newSV (v : T.V) (n : N) :
    ((extendSheets D σ).vertexPartition (newSV D σ v n).1.1).blockCard (newSV D σ v n).1.2 = 1 :=
  extendPartition_blockCard_inr _ σ _

/-- The local ramification at an old vertex is unchanged. -/
theorem extend_localRamification_oldSV (X : D.SourceVertex) :
    (extendSheets D σ).localRamification X.1.1 ⟨(oldSV D σ X).1.2, (oldSV D σ X).2⟩ =
      D.localRamification X.1.1 ⟨X.1.2, X.2⟩ := by
  unfold GluingDatum.localRamification
  change (∑ e ∈ GluingDatum.incidentEdges X.1.1,
      ((extendPartition (D.edgePartition e) σ).blockCountWithin
        (extendPartition (D.vertexPartition X.1.1) σ) (σ.symm (.inl X.1.2)) : ℤ)) - 2 -
      ((extendPartition (D.vertexPartition X.1.1) σ).blockCard (σ.symm (.inl X.1.2)) : ℤ) *
        _ = _
  simp only [extendPartition_blockCountWithin_inl, extendPartition_blockCard_inl]

/-- The local ramification at a new vertex is `0`. -/
theorem extend_localRamification_newSV (v : T.V) (n : N) :
    (extendSheets D σ).localRamification v ⟨(newSV D σ v n).1.2, (newSV D σ v n).2⟩ = 0 := by
  unfold GluingDatum.localRamification
  change (∑ e ∈ GluingDatum.incidentEdges v,
      ((extendPartition (D.edgePartition e) σ).blockCountWithin
        (extendPartition (D.vertexPartition v) σ) (σ.symm (.inr n)) : ℤ)) - 2 -
      ((extendPartition (D.vertexPartition v) σ).blockCard (σ.symm (.inr n)) : ℤ) * _ = _
  simp only [extendPartition_blockCountWithin_inr, extendPartition_blockCard_inr]
  simp

/-- **Riemann--Hurwitz is inherited by an extension.** -/
theorem riemannHurwitz_extendSheets (h : D.RiemannHurwitz) :
    (extendSheets D σ).RiemannHurwitz := by
  intro v i
  change (∑ e ∈ GluingDatum.incidentEdges v,
      ((extendPartition (D.edgePartition e) σ).blockCountWithin
        (extendPartition (D.vertexPartition v) σ) i : ℤ)) - 2 ≥
      ((extendPartition (D.vertexPartition v) σ).blockCard i : ℤ) * _
  rcases sheet_cases σ i with ⟨a, rfl⟩ | ⟨n, rfl⟩
  · simp only [extendPartition_blockCountWithin_inl, extendPartition_blockCard_inl]
    exact h v a
  · simp only [extendPartition_blockCountWithin_inr, extendPartition_blockCard_inr]
    simp

/-! ### Counts and genus -/

theorem genus_sourceGraph_eq {k : ℕ} (E : GluingDatum T k) :
    genus E.sourceGraph = (Fintype.card E.SourceEdge : ℤ) - Fintype.card E.SourceVertex + 1 := by
  unfold genus GluingDatum.sourceGraph
  simp only [Multiset.card_map, Finset.card_val, Finset.card_univ]

variable (D σ) in
theorem card_sourceVertex_extendSheets [Fintype N] :
    Fintype.card (extendSheets D σ).SourceVertex =
      Fintype.card D.SourceVertex + Fintype.card T.V * Fintype.card N := by
  rw [← Fintype.card_congr (extendSVEquiv D σ), Fintype.card_sum, Fintype.card_prod]

variable (D σ) in
theorem card_sourceEdge_extendSheets [Fintype N] :
    Fintype.card (extendSheets D σ).SourceEdge =
      Fintype.card D.SourceEdge + Fintype.card T.edges * Fintype.card N := by
  classical
  rw [← Fintype.card_congr (extendSEEquiv D σ), Fintype.card_sum, Fintype.card_prod]

variable (D σ) in
/-- **The genus of an extension**: each new sheet adds a copy of the target. -/
theorem genus_extendSheets [Fintype N] :
    genus (extendSheets D σ).sourceGraph =
      genus D.sourceGraph +
        (Fintype.card N : ℤ) * ((Fintype.card T.edges : ℤ) - Fintype.card T.V) := by
  rw [genus_sourceGraph_eq, genus_sourceGraph_eq, card_sourceVertex_extendSheets,
    card_sourceEdge_extendSheets]
  push_cast
  ring

end ExtendDict

/-! ## 6.  The dictionaries of a deletion -/

section RestrictDict

variable {T : CFGraph} {d m : ℕ} {N : Type*} {D : GluingDatum T d} {σ : Fin d ≃ Fin m ⊕ N}
  {hLone : ∀ n, IsLone D (σ.symm (.inr n))} {hm : 0 < m}

/-- A source vertex of the deletion, read in `D`. -/
def inclSV (X : (restrictSheets D σ hLone hm).SourceVertex) : D.SourceVertex :=
  ⟨(X.1.1, σ.symm (.inl X.1.2)), by
    show (D.vertexPartition X.1.1).repr (σ.symm (.inl X.1.2)) = _
    rw [← restrictSheets_vertex_repr (hLone := hLone) (hm := hm)]
    exact congrArg (fun a ↦ σ.symm (.inl a)) X.2⟩

/-- A source edge of the deletion, read in `D`. -/
def inclSE (E : (restrictSheets D σ hLone hm).SourceEdge) : D.SourceEdge :=
  ⟨(E.1.1, σ.symm (.inl E.1.2)), by
    show (D.edgePartition E.1.1).repr (σ.symm (.inl E.1.2)) = _
    rw [← restrictSheets_edge_repr (hLone := hLone) (hm := hm)]
    exact congrArg (fun a ↦ σ.symm (.inl a)) E.2⟩

variable (hLone) in
/-- The source vertex of the deleted sheet `n` over `v`. -/
def loneSV (v : T.V) (n : N) : D.SourceVertex :=
  ⟨(v, σ.symm (.inr n)), (hLone n).repr_vertex v⟩

variable (hLone) in
/-- The source edge of the deleted sheet `n` over `e`. -/
def loneSE (e : T.edges) (n : N) : D.SourceEdge :=
  ⟨(e, σ.symm (.inr n)), (hLone n).repr_edge e⟩

@[simp] theorem inclSV_fst (X : (restrictSheets D σ hLone hm).SourceVertex) :
    (inclSV X).1.1 = X.1.1 := rfl

@[simp] theorem inclSE_fst (E : (restrictSheets D σ hLone hm).SourceEdge) :
    (inclSE E).1.1 = E.1.1 := rfl

theorem inclSV_injective : Function.Injective (inclSV (hLone := hLone) (hm := hm)) := by
  intro X Y h
  have h1 := congrArg (fun Z : D.SourceVertex ↦ Z.1.1) h
  have h2 := congrArg (fun Z : D.SourceVertex ↦ σ Z.1.2) h
  simp only [inclSV, Equiv.apply_symm_apply, Sum.inl.injEq] at h1 h2
  exact Subtype.ext (Prod.ext h1 h2)

theorem inclSE_injective : Function.Injective (inclSE (hLone := hLone) (hm := hm)) := by
  intro X Y h
  have h1 := congrArg (fun Z : D.SourceEdge ↦ Z.1.1) h
  have h2 := congrArg (fun Z : D.SourceEdge ↦ σ Z.1.2) h
  simp only [inclSE, Equiv.apply_symm_apply, Sum.inl.injEq] at h1 h2
  exact Subtype.ext (Prod.ext h1 h2)

@[simp] theorem inclSV_inj {X Y : (restrictSheets D σ hLone hm).SourceVertex} :
    inclSV X = inclSV Y ↔ X = Y := inclSV_injective.eq_iff

@[simp] theorem inclSE_inj {X Y : (restrictSheets D σ hLone hm).SourceEdge} :
    inclSE X = inclSE Y ↔ X = Y := inclSE_injective.eq_iff

theorem inclSV_ne_loneSV (X : (restrictSheets D σ hLone hm).SourceVertex) (v : T.V) (n : N) :
    inclSV X ≠ loneSV hLone v n := by
  intro h
  have := congrArg (fun Z : D.SourceVertex ↦ σ Z.1.2) h
  simp [inclSV, loneSV] at this

theorem inclSE_ne_loneSE (E : (restrictSheets D σ hLone hm).SourceEdge) (e : T.edges) (n : N) :
    inclSE E ≠ loneSE hLone e n := by
  intro h
  have := congrArg (fun Z : D.SourceEdge ↦ σ Z.1.2) h
  simp [inclSE, loneSE] at this

@[simp] theorem loneSV_inj {v w : T.V} {n n' : N} :
    loneSV hLone v n = loneSV hLone w n' ↔ v = w ∧ n = n' := by
  constructor
  · intro h
    have h1 := congrArg (fun Z : D.SourceVertex ↦ Z.1.1) h
    have h2 := congrArg (fun Z : D.SourceVertex ↦ σ Z.1.2) h
    simp only [loneSV, Equiv.apply_symm_apply, Sum.inr.injEq] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

@[simp] theorem loneSE_inj {e f : T.edges} {n n' : N} :
    loneSE hLone e n = loneSE hLone f n' ↔ e = f ∧ n = n' := by
  constructor
  · intro h
    have h1 := congrArg (fun Z : D.SourceEdge ↦ Z.1.1) h
    have h2 := congrArg (fun Z : D.SourceEdge ↦ σ Z.1.2) h
    simp only [loneSE, Equiv.apply_symm_apply, Sum.inr.injEq] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- A source vertex of `D` with an old sheet, read in the deletion. -/
def restrictSV (X : D.SourceVertex) (a : Fin m) (ha : σ.symm (.inl a) = X.1.2) :
    (restrictSheets D σ hLone hm).SourceVertex :=
  ⟨(X.1.1, a), by
    apply (oldEmb σ).injective
    simp only [oldEmb_apply]
    rw [restrictSheets_vertex_repr, ha]
    exact X.2⟩

theorem inclSV_restrictSV (X : D.SourceVertex) (a : Fin m) (ha : σ.symm (.inl a) = X.1.2) :
    inclSV (restrictSV (hLone := hLone) (hm := hm) X a ha) = X :=
  Subtype.ext (Prod.ext rfl ha)

/-- A source edge of `D` with an old sheet, read in the deletion. -/
def restrictSE (E : D.SourceEdge) (a : Fin m) (ha : σ.symm (.inl a) = E.1.2) :
    (restrictSheets D σ hLone hm).SourceEdge :=
  ⟨(E.1.1, a), by
    apply (oldEmb σ).injective
    simp only [oldEmb_apply]
    rw [restrictSheets_edge_repr, ha]
    exact E.2⟩

theorem inclSE_restrictSE (E : D.SourceEdge) (a : Fin m) (ha : σ.symm (.inl a) = E.1.2) :
    inclSE (restrictSE (hLone := hLone) (hm := hm) E a ha) = E :=
  Subtype.ext (Prod.ext rfl ha)

/-- Every source vertex of `D` is a vertex of the deletion or a lone vertex. -/
theorem restrict_sourceVertex_cases (X : D.SourceVertex) :
    (∃ Y : (restrictSheets D σ hLone hm).SourceVertex, inclSV Y = X) ∨
      ∃ n, loneSV hLone X.1.1 n = X := by
  rcases sheet_cases σ X.1.2 with ⟨a, ha⟩ | ⟨n, hn⟩
  · exact Or.inl ⟨restrictSV X a ha, inclSV_restrictSV X a ha⟩
  · exact Or.inr ⟨n, Subtype.ext (Prod.ext rfl hn)⟩

/-- Every source edge of `D` is an edge of the deletion or a lone edge. -/
theorem restrict_sourceEdge_cases (E : D.SourceEdge) :
    (∃ F : (restrictSheets D σ hLone hm).SourceEdge, inclSE F = E) ∨
      ∃ n, loneSE hLone E.1.1 n = E := by
  rcases sheet_cases σ E.1.2 with ⟨a, ha⟩ | ⟨n, hn⟩
  · exact Or.inl ⟨restrictSE E a ha, inclSE_restrictSE E a ha⟩
  · exact Or.inr ⟨n, Subtype.ext (Prod.ext rfl hn)⟩

variable (D σ hLone hm) in
/-- **The source-vertex dictionary of a deletion.** -/
noncomputable def restrictSVEquiv :
    (restrictSheets D σ hLone hm).SourceVertex ⊕ (T.V × N) ≃ D.SourceVertex :=
  Equiv.ofBijective (Sum.elim inclSV fun q ↦ loneSV hLone q.1 q.2) (by
    constructor
    · rintro (X | ⟨v, n⟩) (Y | ⟨w, n'⟩) h
      · exact congrArg Sum.inl (inclSV_injective h)
      · exact absurd h (inclSV_ne_loneSV _ _ _)
      · exact absurd h.symm (inclSV_ne_loneSV _ _ _)
      · obtain ⟨rfl, rfl⟩ := (loneSV_inj (hLone := hLone)).mp h; rfl
    · intro X
      rcases restrict_sourceVertex_cases (σ := σ) (hLone := hLone) (hm := hm) X with
        ⟨Y, hY⟩ | ⟨n, hn⟩
      · exact ⟨.inl Y, hY⟩
      · exact ⟨.inr (X.1.1, n), hn⟩)

variable (D σ hLone hm) in
/-- **The source-edge dictionary of a deletion.** -/
noncomputable def restrictSEEquiv :
    (restrictSheets D σ hLone hm).SourceEdge ⊕ (T.edges × N) ≃ D.SourceEdge :=
  Equiv.ofBijective (Sum.elim inclSE fun q ↦ loneSE hLone q.1 q.2) (by
    constructor
    · rintro (X | ⟨v, n⟩) (Y | ⟨w, n'⟩) h
      · exact congrArg Sum.inl (inclSE_injective h)
      · exact absurd h (inclSE_ne_loneSE _ _ _)
      · exact absurd h.symm (inclSE_ne_loneSE _ _ _)
      · obtain ⟨rfl, rfl⟩ := (loneSE_inj (hLone := hLone)).mp h; rfl
    · intro E
      rcases restrict_sourceEdge_cases (σ := σ) (hLone := hLone) (hm := hm) E with
        ⟨F, hF⟩ | ⟨n, hn⟩
      · exact ⟨.inl F, hF⟩
      · exact ⟨.inr (E.1.1, n), hn⟩)

@[simp] theorem restrictSVEquiv_inl (X : (restrictSheets D σ hLone hm).SourceVertex) :
    restrictSVEquiv D σ hLone hm (.inl X) = inclSV X := rfl

@[simp] theorem restrictSVEquiv_inr (v : T.V) (n : N) :
    restrictSVEquiv D σ hLone hm (.inr (v, n)) = loneSV hLone v n := rfl

@[simp] theorem restrictSEEquiv_inl (E : (restrictSheets D σ hLone hm).SourceEdge) :
    restrictSEEquiv D σ hLone hm (.inl E) = inclSE E := rfl

@[simp] theorem restrictSEEquiv_inr (e : T.edges) (n : N) :
    restrictSEEquiv D σ hLone hm (.inr (e, n)) = loneSE hLone e n := rfl

theorem restrict_sourceEndpoint_inl (v : T.V) (a : Fin m) :
    D.sourceEndpoint v (σ.symm (.inl a)) =
      inclSV ((restrictSheets D σ hLone hm).sourceEndpoint v a) := by
  apply Subtype.ext
  change (v, (D.vertexPartition v).repr (σ.symm (.inl a))) =
    (v, σ.symm (.inl (((restrictSheets D σ hLone hm).vertexPartition v).repr a)))
  rw [restrictSheets_vertex_repr]

theorem restrict_sourceEndpoint_inr (v : T.V) (n : N) :
    D.sourceEndpoint v (σ.symm (.inr n)) = loneSV hLone v n := by
  apply Subtype.ext
  change (v, (D.vertexPartition v).repr (σ.symm (.inr n))) = (v, σ.symm (.inr n))
  rw [(hLone n).repr_vertex]

@[simp] theorem sourceEnds_inclSE (E : (restrictSheets D σ hLone hm).SourceEdge) :
    D.sourceEnds (inclSE E) =
      (inclSV ((restrictSheets D σ hLone hm).sourceEnds E).1,
        inclSV ((restrictSheets D σ hLone hm).sourceEnds E).2) := by
  change (D.sourceEndpoint _ (σ.symm (.inl E.1.2)), D.sourceEndpoint _ (σ.symm (.inl E.1.2))) = _
  rw [restrict_sourceEndpoint_inl (hm := hm), restrict_sourceEndpoint_inl (hm := hm)]
  rfl

@[simp] theorem sourceEnds_loneSE (e : T.edges) (n : N) :
    D.sourceEnds (loneSE hLone e n) =
      (loneSV hLone (e : T.V × T.V).1 n, loneSV hLone (e : T.V × T.V).2 n) := by
  change (D.sourceEndpoint _ (σ.symm (.inr n)), D.sourceEndpoint _ (σ.symm (.inr n))) = _
  rw [restrict_sourceEndpoint_inr, restrict_sourceEndpoint_inr]
  rfl

theorem incident_inclSE_inclSV (E : (restrictSheets D σ hLone hm).SourceEdge)
    (X : (restrictSheets D σ hLone hm).SourceVertex) :
    Incident D (inclSE E) (inclSV X) ↔ Incident (restrictSheets D σ hLone hm) E X := by
  unfold Incident
  rw [sourceEnds_inclSE]
  simp only [inclSV_inj]

theorem not_incident_inclSE_loneSV (E : (restrictSheets D σ hLone hm).SourceEdge) (v : T.V)
    (n : N) : ¬ Incident D (inclSE E) (loneSV hLone v n) := by
  unfold Incident
  rw [sourceEnds_inclSE]
  rintro (h | h) <;> exact inclSV_ne_loneSV _ _ _ h

theorem not_incident_loneSE_inclSV (e : T.edges) (n : N)
    (X : (restrictSheets D σ hLone hm).SourceVertex) :
    ¬ Incident D (loneSE hLone e n) (inclSV X) := by
  unfold Incident
  rw [sourceEnds_loneSE]
  rintro (h | h) <;> exact inclSV_ne_loneSV _ _ _ h.symm

theorem incident_loneSE_loneSV (e : T.edges) (n n' : N) (v : T.V) :
    Incident D (loneSE hLone e n) (loneSV hLone v n') ↔
      n = n' ∧ ((e : T.V × T.V).1 = v ∨ (e : T.V × T.V).2 = v) := by
  unfold Incident
  rw [sourceEnds_loneSE]
  simp only [loneSV_inj]
  tauto

@[simp] theorem sourceEdgeIndex_inclSE (E : (restrictSheets D σ hLone hm).SourceEdge) :
    D.sourceEdgeIndex (inclSE E) = (restrictSheets D σ hLone hm).sourceEdgeIndex E :=
  (restrictPartition_blockCard _ σ (fun n j h ↦ (hLone n).edge _ j h) _).symm

@[simp] theorem sourceEdgeIndex_loneSE (e : T.edges) (n : N) :
    D.sourceEdgeIndex (loneSE hLone e n) = 1 :=
  (hLone n).blockCard_edge e

@[simp] theorem blockCard_inclSV (X : (restrictSheets D σ hLone hm).SourceVertex) :
    (D.vertexPartition (inclSV X).1.1).blockCard (inclSV X).1.2 =
      ((restrictSheets D σ hLone hm).vertexPartition X.1.1).blockCard X.1.2 :=
  (restrictPartition_blockCard _ σ (fun n j h ↦ hLone n _ j h) _).symm

@[simp] theorem blockCard_loneSV (v : T.V) (n : N) :
    (D.vertexPartition (loneSV hLone v n).1.1).blockCard (loneSV hLone v n).1.2 = 1 :=
  (hLone n).blockCard_vertex v

theorem restrictSheets_blockCountWithin (e : T.edges) (v : T.V) (a : Fin m) :
    ((restrictSheets D σ hLone hm).edgePartition e).blockCountWithin
        ((restrictSheets D σ hLone hm).vertexPartition v) a =
      (D.edgePartition e).blockCountWithin (D.vertexPartition v) (σ.symm (.inl a)) :=
  restrictPartition_blockCountWithin _ _ σ (fun n j h ↦ (hLone n).edge e j h)
    (fun n j h ↦ hLone n v j h) a

theorem restrictSheets_blockCard (v : T.V) (a : Fin m) :
    ((restrictSheets D σ hLone hm).vertexPartition v).blockCard a =
      (D.vertexPartition v).blockCard (σ.symm (.inl a)) :=
  restrictPartition_blockCard _ σ (fun n j h ↦ hLone n v j h) a

/-- The local ramification at a kept vertex is unchanged by the deletion. -/
theorem localRamification_inclSV (X : (restrictSheets D σ hLone hm).SourceVertex) :
    D.localRamification X.1.1 ⟨(inclSV X).1.2, (inclSV X).2⟩ =
      (restrictSheets D σ hLone hm).localRamification X.1.1 ⟨X.1.2, X.2⟩ := by
  unfold GluingDatum.localRamification
  simp only [restrictSheets_blockCountWithin, restrictSheets_blockCard]
  rfl

/-- The local ramification at a lone vertex is `0`. -/
theorem localRamification_loneSV (v : T.V) (n : N) :
    D.localRamification v ⟨(loneSV hLone v n).1.2, (loneSV hLone v n).2⟩ = 0 := by
  unfold GluingDatum.localRamification
  have hB : ∀ e, (D.edgePartition e).blockCountWithin (D.vertexPartition v)
      (σ.symm (.inr n)) = 1 := by
    intro e
    classical
    unfold SheetPartition.blockCountWithin
    rw [SheetPartition.block_eq_singleton_of_blockCard_eq_one _ _ ((hLone n).blockCard_vertex v)]
    simp
  change (∑ e ∈ GluingDatum.incidentEdges v, ((D.edgePartition e).blockCountWithin
      (D.vertexPartition v) (σ.symm (.inr n)) : ℤ)) - 2 -
    ((D.vertexPartition v).blockCard (σ.symm (.inr n)) : ℤ) * _ = 0
  simp only [hB, (hLone n).blockCard_vertex v]
  simp

/-- **Riemann--Hurwitz is inherited by a deletion.** -/
theorem riemannHurwitz_restrictSheets (h : D.RiemannHurwitz) :
    (restrictSheets D σ hLone hm).RiemannHurwitz := by
  intro v a
  simp only [restrictSheets_blockCountWithin, restrictSheets_blockCard]
  exact h v _

variable (D σ hLone hm) in
theorem card_sourceVertex_restrictSheets [Fintype N] :
    Fintype.card D.SourceVertex =
      Fintype.card (restrictSheets D σ hLone hm).SourceVertex +
        Fintype.card T.V * Fintype.card N := by
  rw [← Fintype.card_congr (restrictSVEquiv D σ hLone hm), Fintype.card_sum, Fintype.card_prod]

variable (D σ hLone hm) in
theorem card_sourceEdge_restrictSheets [Fintype N] :
    Fintype.card D.SourceEdge =
      Fintype.card (restrictSheets D σ hLone hm).SourceEdge +
        Fintype.card T.edges * Fintype.card N := by
  classical
  rw [← Fintype.card_congr (restrictSEEquiv D σ hLone hm), Fintype.card_sum, Fintype.card_prod]

variable (D σ hLone hm) in
/-- **The genus of a deletion**: each deleted sheet removes a copy of the target. -/
theorem genus_restrictSheets [Fintype N] :
    genus D.sourceGraph =
      genus (restrictSheets D σ hLone hm).sourceGraph +
        (Fintype.card N : ℤ) * ((Fintype.card T.edges : ℤ) - Fintype.card T.V) := by
  rw [genus_sourceGraph_eq, genus_sourceGraph_eq, card_sourceVertex_restrictSheets D σ hLone hm,
    card_sourceEdge_restrictSheets D σ hLone hm]
  push_cast
  ring

/-! ### Walks in a deletion -/

include hLone in
theorem not_isNew_of_incident {E : D.SourceEdge} {X : D.SourceVertex} (hI : Incident D E X)
    (hX : ¬ IsNew σ X.1.2) : ¬ IsNew σ E.1.2 := by
  intro hE
  obtain ⟨n, hn⟩ := (isNew_iff σ _).mp hE
  have hRel := ((incident_iff_target_mem_and_rel D E X).mp hI).2
  rw [← hn] at hRel
  have := hLone n _ _ ((SheetPartition.rel_iff _ _ _).mpr hRel.symm)
  exact hX ((isNew_iff σ _).mpr ⟨n, this.symm⟩)

include hLone in
theorem not_isNew_of_incident' {E : D.SourceEdge} {X : D.SourceVertex} (hI : Incident D E X)
    (hE : ¬ IsNew σ E.1.2) : ¬ IsNew σ X.1.2 := by
  intro hX
  obtain ⟨n, hn⟩ := (isNew_iff σ _).mp hX
  have hRel := ((incident_iff_target_mem_and_rel D E X).mp hI).2
  rw [← hn] at hRel
  have := hLone n _ _ hRel
  exact hE ((isNew_iff σ _).mpr ⟨n, this.symm⟩)

theorem inclSV_isOld (X : (restrictSheets D σ hLone hm).SourceVertex) :
    ¬ IsNew σ (inclSV X).1.2 := not_isNew_inl σ _

theorem exists_inclSV_of_old {X : D.SourceVertex} (hX : ¬ IsNew σ X.1.2) :
    ∃ X' : (restrictSheets D σ hLone hm).SourceVertex, inclSV X' = X := by
  rcases restrict_sourceVertex_cases (σ := σ) (hLone := hLone) (hm := hm) X with h | ⟨n, hn⟩
  · exact h
  · exact absurd (hn ▸ isNew_inr σ n) hX

theorem exists_inclSE_of_old {E : D.SourceEdge} (hE : ¬ IsNew σ E.1.2) :
    ∃ E' : (restrictSheets D σ hLone hm).SourceEdge, inclSE E' = E := by
  rcases restrict_sourceEdge_cases (σ := σ) (hLone := hLone) (hm := hm) E with h | ⟨n, hn⟩
  · exact h
  · exact absurd (hn ▸ isNew_inr σ n) hE

/-- **A walk of `D` between two kept vertices is a walk of the deletion**: new sheets are lone,
so a walk can never step onto them. -/
theorem reach_of_reach_inclSV {X Y : (restrictSheets D σ hLone hm).SourceVertex}
    (h : DraismaVargas.LocalCases.DanglingDescent.Reach D.sourceGraph (inclSV X) (inclSV Y)) :
    DraismaVargas.LocalCases.DanglingDescent.Reach (restrictSheets D σ hLone hm).sourceGraph X Y := by
  have key := DraismaVargas.LocalCases.DanglingDescent.reach_propagate
    (motive := fun Z : D.SourceVertex ↦ ∃ Z' : (restrictSheets D σ hLone hm).SourceVertex,
      inclSV Z' = Z ∧ DraismaVargas.LocalCases.DanglingDescent.Reach (restrictSheets D σ hLone hm).sourceGraph X Z')
    ⟨X, rfl, DraismaVargas.LocalCases.DanglingDescent.reach_refl _ _⟩ (fun a b hab ha ↦ by
      obtain ⟨a', rfl, ha'⟩ := ha
      obtain ⟨E, hEnds⟩ := exists_sourceEnds_of_num_edges_pos D hab
      have hEa : Incident D E (inclSV a') := by
        rcases hEnds with h | h
        · exact Or.inl (congrArg Prod.fst h)
        · exact Or.inr (congrArg Prod.snd h)
      have hEb : Incident D E b := by
        rcases hEnds with h | h
        · exact Or.inr (congrArg Prod.snd h)
        · exact Or.inl (congrArg Prod.fst h)
      have hEold := not_isNew_of_incident (hLone := hLone) hEa (inclSV_isOld a')
      have hbold := not_isNew_of_incident' (hLone := hLone) hEb hEold
      obtain ⟨b', rfl⟩ := exists_inclSV_of_old (hLone := hLone) (hm := hm) hbold
      obtain ⟨E', rfl⟩ := exists_inclSE_of_old (hLone := hLone) (hm := hm) hEold
      refine ⟨b', rfl, DraismaVargas.LocalCases.DanglingDescent.reach_trans ha' ?_⟩
      have h1 := (incident_inclSE_inclSV E' a').mp hEa
      have h2 := (incident_inclSE_inclSV E' b').mp hEb
      by_cases hab' : a' = b'
      · rw [hab']; exact DraismaVargas.LocalCases.DanglingDescent.reach_refl _ _
      · refine DraismaVargas.LocalCases.DanglingDescent.reach_single
          (num_edges_pos_of_sourceEnds _ (edge := E') ?_)
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd (h1.symm.trans h2) hab'
        · exact Or.inl (Prod.ext h1 h2)
        · exact Or.inr (Prod.ext h2 h1)
        · exact absurd (h1.symm.trans h2) hab') h
  obtain ⟨Y', hY', hR⟩ := key
  rw [inclSV_injective hY'] at hR
  exact hR

end RestrictDict

/-! ## 7.  Isomorphisms -/

section Iso

variable {T₁ T₂ : CFGraph} {d m : ℕ} {N : Type*}

/-- **An isomorphism of the old data extends**, by the identity on the new sheets. -/
def extendSheetsIso {D₁ : GluingDatum T₁ m} {D₂ : GluingDatum T₂ m}
    (Φ : GeometricDatumIso D₁ D₂) (σ₁ σ₂ : Fin d ≃ Fin m ⊕ N) :
    GeometricDatumIso (extendSheets D₁ σ₁) (extendSheets D₂ σ₂) where
  targetVertex := Φ.targetVertex
  targetEdge := Φ.targetEdge
  ends := Φ.ends
  vertexPerm v := extendPerm (Φ.vertexPerm v) σ₁ σ₂
  edgePerm e := extendPerm (Φ.edgePerm e) σ₁ σ₂
  vertexPartition v := by
    rw [extendSheets_vertexPartition, Φ.vertexPartition, extendPartition_relabel _ _ σ₁ σ₂]
    rfl
  edgePartition e := by
    rw [extendSheets_edgePartition, Φ.edgePartition, extendPartition_relabel _ _ σ₁ σ₂]
    rfl
  compatible e v hv i := by
    change (extendPartition (D₁.vertexPartition v) σ₁).Rel _ i
    rcases sheet_cases σ₁ i with ⟨a, rfl⟩ | ⟨n, rfl⟩
    · rw [extendPerm_inl, extendPerm_symm_inl, extendPartition_rel_inl_inl]
      exact Φ.compatible e v hv a
    · rw [extendPerm_inr, extendPerm_symm_inr]
      exact SheetPartition.rel_repr_left _ _ |>.symm.trans (SheetPartition.rel_repr_left _ _)

variable {D₁ : GluingDatum T₁ m} {D₂ : GluingDatum T₂ m} (Φ : GeometricDatumIso D₁ D₂)
  (σ₁ σ₂ : Fin d ≃ Fin m ⊕ N)

@[simp] theorem extendSheetsIso_targetVertex :
    (extendSheetsIso Φ σ₁ σ₂).targetVertex = Φ.targetVertex := rfl

@[simp] theorem extendSheetsIso_targetEdge :
    (extendSheetsIso Φ σ₁ σ₂).targetEdge = Φ.targetEdge := rfl

theorem sourceVertexEquiv_oldSV (X : D₁.SourceVertex) :
    (extendSheetsIso Φ σ₁ σ₂).sourceVertexEquiv (oldSV D₁ σ₁ X) =
      oldSV D₂ σ₂ (Φ.sourceVertexEquiv X) := by
  apply Subtype.ext
  change (Φ.targetVertex X.1.1, extendPerm (Φ.vertexPerm X.1.1) σ₁ σ₂ (σ₁.symm (.inl X.1.2))) =
    (Φ.targetVertex X.1.1, σ₂.symm (.inl (Φ.vertexPerm X.1.1 X.1.2)))
  rw [extendPerm_inl]

theorem sourceVertexEquiv_newSV (v : T₁.V) (n : N) :
    (extendSheetsIso Φ σ₁ σ₂).sourceVertexEquiv (newSV D₁ σ₁ v n) =
      newSV D₂ σ₂ (Φ.targetVertex v) n := by
  apply Subtype.ext
  change (Φ.targetVertex v, extendPerm (Φ.vertexPerm v) σ₁ σ₂ (σ₁.symm (.inr n))) =
    (Φ.targetVertex v, σ₂.symm (.inr n))
  rw [extendPerm_inr]

theorem sourceEdgeEquiv_oldSE (F : D₁.SourceEdge) :
    (extendSheetsIso Φ σ₁ σ₂).sourceEdgeEquiv (oldSE D₁ σ₁ F) =
      oldSE D₂ σ₂ (Φ.sourceEdgeEquiv F) := by
  apply Subtype.ext
  change (Φ.targetEdge F.1.1, extendPerm (Φ.edgePerm F.1.1) σ₁ σ₂ (σ₁.symm (.inl F.1.2))) =
    (Φ.targetEdge F.1.1, σ₂.symm (.inl (Φ.edgePerm F.1.1 F.1.2)))
  rw [extendPerm_inl]

theorem sourceEdgeEquiv_newSE (e : T₁.edges) (n : N) :
    (extendSheetsIso Φ σ₁ σ₂).sourceEdgeEquiv (newSE D₁ σ₁ e n) =
      newSE D₂ σ₂ (Φ.targetEdge e) n := by
  apply Subtype.ext
  change (Φ.targetEdge e, extendPerm (Φ.edgePerm e) σ₁ σ₂ (σ₁.symm (.inr n))) =
    (Φ.targetEdge e, σ₂.symm (.inr n))
  rw [extendPerm_inr]

end Iso

section IsoRestrict

variable {d m : ℕ} {N N' : Type*}

theorem elim_spec (σ : Fin d ≃ Fin m ⊕ N) (x : Fin d) (hx : ¬ IsNew σ x) (a : Fin m) :
    σ.symm (.inl (Sum.elim id (fun _ ↦ a) (σ x))) = x := by
  rcases h : σ x with b | n
  · simp only [Sum.elim_inl, id_eq]
    rw [← h, Equiv.symm_apply_apply]
  · exact absurd (by simp [IsNew, h]) hx

/-- **The old part of a permutation carrying new sheets to new sheets.** -/
def oldPerm (π : Equiv.Perm (Fin d)) (σ₁ : Fin d ≃ Fin m ⊕ N) (σ₂ : Fin d ≃ Fin m ⊕ N')
    (h : ∀ i, IsNew σ₂ (π i) ↔ IsNew σ₁ i) : Equiv.Perm (Fin m) where
  toFun a := Sum.elim id (fun _ ↦ a) (σ₂ (π (σ₁.symm (.inl a))))
  invFun b := Sum.elim id (fun _ ↦ b) (σ₁ (π.symm (σ₂.symm (.inl b))))
  left_inv a := by
    have h1 : ¬ IsNew σ₂ (π (σ₁.symm (.inl a))) := by rw [h]; exact not_isNew_inl σ₁ a
    have hb := elim_spec σ₂ _ h1 a
    show Sum.elim id (fun _ ↦ _) (σ₁ (π.symm (σ₂.symm (.inl (Sum.elim id (fun _ ↦ a)
      (σ₂ (π (σ₁.symm (.inl a))))))))) = a
    rw [hb, Equiv.symm_apply_apply, Equiv.apply_symm_apply]
    rfl
  right_inv b := by
    have h1 : ¬ IsNew σ₁ (π.symm (σ₂.symm (.inl b))) := by
      rw [← h, Equiv.apply_symm_apply]; exact not_isNew_inl σ₂ b
    have ha := elim_spec σ₁ _ h1 b
    show Sum.elim id (fun _ ↦ _) (σ₂ (π (σ₁.symm (.inl (Sum.elim id (fun _ ↦ b)
      (σ₁ (π.symm (σ₂.symm (.inl b))))))))) = b
    rw [ha, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl

theorem oldPerm_spec (π : Equiv.Perm (Fin d)) (σ₁ : Fin d ≃ Fin m ⊕ N) (σ₂ : Fin d ≃ Fin m ⊕ N')
    (h : ∀ i, IsNew σ₂ (π i) ↔ IsNew σ₁ i) (a : Fin m) :
    σ₂.symm (.inl (oldPerm π σ₁ σ₂ h a)) = π (σ₁.symm (.inl a)) :=
  elim_spec σ₂ _ (by rw [h]; exact not_isNew_inl σ₁ a) a

theorem oldPerm_symm_spec (π : Equiv.Perm (Fin d)) (σ₁ : Fin d ≃ Fin m ⊕ N)
    (σ₂ : Fin d ≃ Fin m ⊕ N')
    (h : ∀ i, IsNew σ₂ (π i) ↔ IsNew σ₁ i) (b : Fin m) :
    σ₁.symm (.inl ((oldPerm π σ₁ σ₂ h).symm b)) = π.symm (σ₂.symm (.inl b)) := by
  apply π.injective
  rw [← oldPerm_spec π σ₁ σ₂ h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

variable {T₁ T₂ : CFGraph} {D₁ : GluingDatum T₁ d} {D₂ : GluingDatum T₂ d}
  {σ₁ : Fin d ≃ Fin m ⊕ N} {σ₂ : Fin d ≃ Fin m ⊕ N'}
  {h₁ : ∀ n, IsLone D₁ (σ₁.symm (.inr n))} {h₂ : ∀ n, IsLone D₂ (σ₂.symm (.inr n))}
  {hm₁ hm₂ : 0 < m}

/-- **An isomorphism carrying new sheets to new sheets restricts** to the deletions. -/
def restrictSheetsIso (Φ : GeometricDatumIso D₁ D₂)
    (hV : ∀ v i, IsNew σ₂ (Φ.vertexPerm v i) ↔ IsNew σ₁ i)
    (hE : ∀ e i, IsNew σ₂ (Φ.edgePerm e i) ↔ IsNew σ₁ i) :
    GeometricDatumIso (restrictSheets D₁ σ₁ h₁ hm₁) (restrictSheets D₂ σ₂ h₂ hm₂) where
  targetVertex := Φ.targetVertex
  targetEdge := Φ.targetEdge
  ends := Φ.ends
  vertexPerm v := oldPerm (Φ.vertexPerm v) σ₁ σ₂ (hV v)
  edgePerm e := oldPerm (Φ.edgePerm e) σ₁ σ₂ (hE e)
  vertexPartition v := by
    refine SheetPartition.ext_repr _ _ (funext fun b ↦ (oldEmb σ₂).injective ?_)
    simp only [oldEmb_apply]
    rw [restrictSheets_vertex_repr]
    change _ = σ₂.symm (.inl (oldPerm (Φ.vertexPerm v) σ₁ σ₂ (hV v)
      (((restrictSheets D₁ σ₁ h₁ hm₁).vertexPartition v).repr
        ((oldPerm (Φ.vertexPerm v) σ₁ σ₂ (hV v)).symm b))))
    rw [oldPerm_spec, restrictSheets_vertex_repr, oldPerm_symm_spec, Φ.vertexPartition]
    rfl
  edgePartition e := by
    refine SheetPartition.ext_repr _ _ (funext fun b ↦ (oldEmb σ₂).injective ?_)
    simp only [oldEmb_apply]
    rw [restrictSheets_edge_repr]
    change _ = σ₂.symm (.inl (oldPerm (Φ.edgePerm e) σ₁ σ₂ (hE e)
      (((restrictSheets D₁ σ₁ h₁ hm₁).edgePartition e).repr
        ((oldPerm (Φ.edgePerm e) σ₁ σ₂ (hE e)).symm b))))
    rw [oldPerm_spec, restrictSheets_edge_repr, oldPerm_symm_spec, Φ.edgePartition]
    rfl
  compatible e v hv a := by
    rw [restrictSheets_vertex_rel_iff, oldPerm_symm_spec, oldPerm_spec]
    exact Φ.compatible e v hv _

variable (Φ : GeometricDatumIso D₁ D₂) (hV : ∀ v i, IsNew σ₂ (Φ.vertexPerm v i) ↔ IsNew σ₁ i)
  (hE : ∀ e i, IsNew σ₂ (Φ.edgePerm e i) ↔ IsNew σ₁ i)

theorem inclSV_restrictSheetsIso (X : (restrictSheets D₁ σ₁ h₁ hm₁).SourceVertex) :
    inclSV ((restrictSheetsIso (h₂ := h₂) (hm₂ := hm₂) Φ hV hE).sourceVertexEquiv X) =
      Φ.sourceVertexEquiv (inclSV X) := by
  apply Subtype.ext
  change (Φ.targetVertex X.1.1, σ₂.symm (.inl (oldPerm (Φ.vertexPerm X.1.1) σ₁ σ₂ (hV _) X.1.2))) =
    (Φ.targetVertex X.1.1, Φ.vertexPerm X.1.1 (σ₁.symm (.inl X.1.2)))
  rw [oldPerm_spec]

theorem inclSE_restrictSheetsIso (E : (restrictSheets D₁ σ₁ h₁ hm₁).SourceEdge) :
    inclSE ((restrictSheetsIso (h₂ := h₂) (hm₂ := hm₂) Φ hV hE).sourceEdgeEquiv E) =
      Φ.sourceEdgeEquiv (inclSE E) := by
  apply Subtype.ext
  change (Φ.targetEdge E.1.1, σ₂.symm (.inl (oldPerm (Φ.edgePerm E.1.1) σ₁ σ₂ (hE _) E.1.2))) =
    (Φ.targetEdge E.1.1, Φ.edgePerm E.1.1 (σ₁.symm (.inl E.1.2)))
  rw [oldPerm_spec]

end IsoRestrict

end DraismaVargas.Count.MarkedCountGeneral.Sheets
