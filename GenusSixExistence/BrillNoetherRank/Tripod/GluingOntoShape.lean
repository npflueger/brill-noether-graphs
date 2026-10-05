import GenusSixExistence.BrillNoetherRank.Tripod.GluingOntoTarget
import GenusSixExistence.BrillNoetherRank.Tripod.GluingOntoOpen
import DraismaVargas.Infrastructure.PartitionNormalization
import GenusSixExistence.BrillNoetherRank.Tripod.ClawShape

/-!
# The shape of an open glued member

The proof of `GluingOnto.exists_glueShape`, the shape half of the onto step of the gluing
bijection, split into what is read off the member and a construction. Prose proof:
`Research/genus-six-brill-noether-rank.md`, §4.8 (The parameter count) and §5.5 (The bijection,
the onto step); section and statement numbers in this file refer to that note.

1. **The dichotomy facts** (`nonempty_gluedFacts`, from `Dichotomy`): a glued member has
   three leg edges `leg k` at the marks over three leaf edges `lam k = [w k, v k]` with `v k` a
   leaf, `w k = φ(k)` trivalent, the `w k` distinct, and `φ(c)` not a leaf (`GluedFacts`).
2. **The sheet shape** (`sheetShape`): the Y-sheet. With `y` the sheet of the centre and `σ k`
   the sheet of `leg k`, `y` is a singleton block over every target vertex and edge off the arms
   (Y′ has local degree one over `T̂`), the arms are discrete, and the tip `v k` glues exactly
   `σ k` to `y` (`YSheet`, `ySheet_shape`). The pieces: the arms (`arm_discrete`, Part I
   `rem-leaves-min-change`), the tips from `σ k ∼ y` (`tip_of_turn`), and at `w k` the blocks of
   its two `T̂`-edges (`pass_of_arm`, Riemann--Hurwitz with `r = 0` at the trivalent `w k`); in
   section `YProof`, `ySheet_singleton` (`y` a singleton block off the arms: the Y-sheet stays in
   `Y′`, whose vertices off the leaves are single sheets by the leg-index lemma, Lemma 4.8, for a
   glued member) and `hairpin_turn` (`σ k ≠ y`, and `σ k ∼ y` at the tip: along leg `k` the
   edges in the Y-sheet change only at the fold over `v k`).
3. **The construction** (`exists_shape`): from 1 and 2, `T`, `D`, `π` and
   `Ξ : glueDatum D π ≅ φ.data` carrying the marks, the centre and the legs (`ShapeLabels`). The
   target is `OntoTarget.exists_targetShape`; the datum is `φ.data` transported to `π.T₆`
   (`GluingTransport.transport`), with the Y-sheet moved to `Fin.last` by one global swap,
   restricted to the old sheets over `T₃` (`lastRestrict`) and un-refined at the three marks
   (`unrefineDatum`); the isomorphism is blockwise (`isoOfSameBlocks`).
4. **Connectedness and placement** (`connected_nonDangling_of_shape`, section `ConnProof`): any
   such shape has `D` connected and `π` non-dangling. The old sheets reach a
   mark, the marks are joined through the old sheets by the G-edges of the connected marked core
   (the new sheet lies in `Y′`, so no G-edge enters it), and a mark over a dangling edge of `D`
   would have glued valency one.
-/

open DraismaVargas.Infrastructure
open DraismaVargas.Count
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open DraismaVargas.LocalCases.FullDimensionalSource (FullDimensionalSourcePresentation)
open Utilities.Certificate.ExplicitPotential (Core)
open DraismaVargas.Count.SegmentWalls (Frame)

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

open TargetExpansion
open GenusSixExistence.Tripod.Gadget
open GenusSixExistence.Tripod.Classification

namespace Onto

/-! ## 1. Sheet partitions with a singleton last sheet -/

namespace LastSheet

variable {d : ℕ}

/-- **Forget the last sheet.** A sheet whose block's representative is the last sheet is kept as a
singleton; when the last sheet is a singleton block (`LastSingleton`) this does not happen. -/
def restrictLast (P : SheetPartition (d + 1)) : SheetPartition d where
  repr i := if h : P.repr i.castSucc = Fin.last d then i else (P.repr i.castSucc).castPred h
  repr_idem i := by
    by_cases h : P.repr i.castSucc = Fin.last d
    · simp only [dif_pos h]
    · simp only [dif_neg h]
      have h2 : P.repr ((P.repr i.castSucc).castPred h).castSucc = P.repr i.castSucc := by
        rw [Fin.castSucc_castPred, P.repr_idem]
      rw [dif_neg (by rw [h2]; exact h)]
      exact Fin.castPred_inj.mpr h2

/-- The last sheet is a block on its own. -/
def LastSingleton (P : SheetPartition (d + 1)) : Prop :=
  ∀ i, P.Rel i (Fin.last d) ↔ i = Fin.last d

theorem LastSingleton.repr_last {P : SheetPartition (d + 1)} (h : LastSingleton P) :
    P.repr (Fin.last d) = Fin.last d :=
  (h _).mp (P.rel_repr_left _)

theorem LastSingleton.repr_castSucc_ne {P : SheetPartition (d + 1)} (h : LastSingleton P)
    (i : Fin d) : P.repr i.castSucc ≠ Fin.last d := by
  intro h'
  have hrel : P.Rel i.castSucc (Fin.last d) := by
    show P.repr i.castSucc = P.repr (Fin.last d)
    rw [h', h.repr_last]
  exact Fin.castSucc_ne_last i ((h _).mp hrel)

theorem restrictLast_repr {P : SheetPartition (d + 1)} (h : LastSingleton P) (i : Fin d) :
    ((restrictLast P).repr i).castSucc = P.repr i.castSucc := by
  show (if h' : P.repr i.castSucc = Fin.last d then i else
    (P.repr i.castSucc).castPred h').castSucc = _
  rw [dif_neg (h.repr_castSucc_ne i), Fin.castSucc_castPred]

theorem restrictLast_rel {P : SheetPartition (d + 1)} (h : LastSingleton P) (i j : Fin d) :
    (restrictLast P).Rel i j ↔ P.Rel i.castSucc j.castSucc := by
  rw [SheetPartition.rel_iff, SheetPartition.rel_iff, ← restrictLast_repr h,
    ← restrictLast_repr h, Fin.castSucc_inj]

theorem extendNew_restrictLast {P : SheetPartition (d + 1)} (h : LastSingleton P) :
    SheetOps.extendNew (restrictLast P) = P := by
  apply SheetPartition.ext_repr
  funext x
  induction x using Fin.lastCases with
  | last => rw [SheetOps.extendNew_repr_last, h.repr_last]
  | cast i => rw [SheetOps.extendNew_repr_castSucc, restrictLast_repr h]

theorem restrictLast_sameBlocks {P Q : SheetPartition (d + 1)} (hP : LastSingleton P)
    (hQ : LastSingleton Q) (h : P.SameBlocks Q) : (restrictLast P).SameBlocks (restrictLast Q) :=
  fun i j ↦ by rw [restrictLast_rel hP, restrictLast_rel hQ]; exact h _ _

theorem restrictLast_refines {P Q : SheetPartition (d + 1)} (hP : LastSingleton P)
    (hQ : LastSingleton Q) (h : P.Refines Q) : (restrictLast P).Refines (restrictLast Q) :=
  fun i j hij ↦ (restrictLast_rel hQ i j).mpr (h.rel ((restrictLast_rel hP i j).mp hij))

theorem extendNew_sameBlocks {P Q : SheetPartition d} (h : P.SameBlocks Q) :
    (SheetOps.extendNew P).SameBlocks (SheetOps.extendNew Q) := by
  intro x z
  induction x using Fin.lastCases with
  | last =>
    induction z using Fin.lastCases with
    | last => exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
    | cast j =>
      simp only [SheetPartition.rel_iff, SheetOps.extendNew_repr_last,
        SheetOps.extendNew_repr_castSucc]
      exact ⟨fun e ↦ absurd e.symm (Fin.castSucc_ne_last _),
        fun e ↦ absurd e.symm (Fin.castSucc_ne_last _)⟩
  | cast i =>
    induction z using Fin.lastCases with
    | last =>
      simp only [SheetPartition.rel_iff, SheetOps.extendNew_repr_last,
        SheetOps.extendNew_repr_castSucc]
      exact ⟨fun e ↦ absurd e (Fin.castSucc_ne_last _),
        fun e ↦ absurd e (Fin.castSucc_ne_last _)⟩
    | cast j =>
      simp only [SheetPartition.rel_iff, SheetOps.extendNew_repr_castSucc,
        Fin.castSucc_inj]
      exact h i j

theorem relabel_rel (P : SheetPartition d) (ρ : Equiv.Perm (Fin d)) (i j : Fin d) :
    (P.relabel ρ).Rel i j ↔ P.Rel (ρ.symm i) (ρ.symm j) := by
  have := P.relabel_rel_iff ρ (ρ.symm i) (ρ.symm j)
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at this

theorem relabel_sameBlocks {P Q : SheetPartition d} (h : P.SameBlocks Q) (ρ : Equiv.Perm (Fin d)) :
    (P.relabel ρ).SameBlocks (Q.relabel ρ) :=
  fun i j ↦ by rw [relabel_rel, relabel_rel]; exact h _ _

theorem lastSingleton_relabel {P : SheetPartition (d + 1)} {y : Fin (d + 1)}
    (h : ∀ i, P.Rel i y ↔ i = y) {ρ : Equiv.Perm (Fin (d + 1))} (hρ : ρ y = Fin.last d) :
    LastSingleton (P.relabel ρ) := by
  intro i
  rw [relabel_rel, ← hρ, Equiv.symm_apply_apply, h, Equiv.symm_apply_eq]

end LastSheet

open LastSheet

/-! ## 2. Isomorphisms from blockwise agreement -/

section Blockwise

variable {S : CFGraph} {d : ℕ}

theorem sourceEndpoint_eq_of_rel (E : GluingDatum S d) (v : S.V) {i j : Fin d}
    (h : (E.vertexPartition v).Rel i j) : E.sourceEndpoint v i = E.sourceEndpoint v j :=
  Subtype.ext (Prod.ext rfl h)

theorem sourceEdge_eq_of_rel (E : GluingDatum S d) (e : S.edges) {i j : Fin d}
    (h : (E.edgePartition e).Rel i j) : E.sourceEdge e i = E.sourceEdge e j :=
  Subtype.ext (Prod.ext rfl h)

/-- **Two data with the same blocks everywhere are isomorphic**, over the identity of the
target, by the within-block normalizations (`PartitionNormalization.permutation`). -/
def isoOfSameBlocks (E F : GluingDatum S d)
    (hV : ∀ v, (E.vertexPartition v).SameBlocks (F.vertexPartition v))
    (hE : ∀ e, (E.edgePartition e).SameBlocks (F.edgePartition e)) : GeometricDatumIso E F where
  targetVertex := Equiv.refl _
  targetEdge := Equiv.refl _
  ends _ := Or.inl rfl
  vertexPerm v := PartitionNormalization.permutation _ _ (hV v)
  edgePerm e := PartitionNormalization.permutation _ _ (hE e)
  vertexPartition v := (PartitionNormalization.relabel_eq _ _ (hV v)).symm
  edgePartition e := (PartitionNormalization.relabel_eq _ _ (hE e)).symm
  compatible e v hv i := by
    have hr : (E.edgePartition e).Refines (E.vertexPartition v) := by
      rcases hv with h | h
      · rw [← h]; exact E.refines_left e
      · rw [← h]; exact E.refines_right e
    exact (PartitionNormalization.permutation_symm_rel _ _ (hV v) _).trans
      (hr.rel (PartitionNormalization.permutation_rel _ _ (hE e) i))

theorem isoOfSameBlocks_sourceEndpoint (E F : GluingDatum S d) (hV hE) (v : S.V) (i : Fin d) :
    (isoOfSameBlocks E F hV hE).sourceVertexEquiv (E.sourceEndpoint v i) =
      F.sourceEndpoint v i :=
  (sourceEndpoint_map (isoOfSameBlocks E F hV hE) v i).trans
    (sourceEndpoint_eq_of_rel F v ((hV v _ _).mp
      (PartitionNormalization.permutation_rel _ _ (hV v) i)))

theorem isoOfSameBlocks_sourceEdge (E F : GluingDatum S d) (hV hE) (e : S.edges) (i : Fin d) :
    (isoOfSameBlocks E F hV hE).sourceEdgeEquiv (E.sourceEdge e i) = F.sourceEdge e i :=
  (sourceEdge_map (isoOfSameBlocks E F hV hE) e i).trans
    (sourceEdge_eq_of_rel F e ((hE e _ _).mp
      (PartitionNormalization.permutation_rel _ _ (hE e) i)))

end Blockwise

/-! ## 3. Un-refining a datum at a passage -/

section Unrefine

variable {S : CFGraph} {d : ℕ}

/-- **Every source vertex over `w` is a passage**: each target edge at `w` carries the blocks of
`w`. -/
def Passage (E : GluingDatum S d) (w : S.V) : Prop :=
  ∀ e ∈ GluingDatum.incidentEdges w, (E.edgePartition e).SameBlocks (E.vertexPartition w)

variable {X : CFGraph} (t : X.edges)

theorem subdivOcc_some_fst (e : X.edges) :
    ((subdivOcc X t (some e) : (subdivTarget X t).edges) :
      (subdivTarget X t).V × (subdivTarget X t).V).1 = subdivOld X t (e : X.V × X.V).1 := by
  by_cases he : e = t
  · subst he; rw [subdivOcc_some_self]
  · rw [subdivOcc_some_of_ne X he]

theorem subdivOcc_some_snd_of_ne {e : X.edges} (he : e ≠ t) :
    ((subdivOcc X t (some e) : (subdivTarget X t).edges) :
      (subdivTarget X t).V × (subdivTarget X t).V).2 = subdivOld X t (e : X.V × X.V).2 := by
  rw [subdivOcc_some_of_ne X he]

theorem some_mem_fresh : subdivOcc X t (some t) ∈ GluingDatum.incidentEdges (subdivFresh X t) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
  rw [subdivOcc_some_self]

theorem none_mem_fresh : subdivOcc X t none ∈ GluingDatum.incidentEdges (subdivFresh X t) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ?_⟩
  rw [subdivOcc_none]

theorem none_mem_snd :
    subdivOcc X t none ∈ GluingDatum.incidentEdges (subdivOld X t (t : X.V × X.V).2) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩
  rw [subdivOcc_none]

variable {t}

/-- The two halves of `t` carry one block structure. -/
theorem halves_sameBlocks {E : GluingDatum (subdivTarget X t) d}
    (hP : Passage E (subdivFresh X t)) :
    (E.edgePartition (subdivOcc X t (some t))).SameBlocks (E.edgePartition (subdivOcc X t none)) :=
  (hP _ (some_mem_fresh t)).trans (hP _ (none_mem_fresh t)).symm

/-- **Un-refine at a passage**: the datum over `X` read on the old vertices and on the first
halves. -/
def unrefineDatum (E : GluingDatum (subdivTarget X t) d) (hP : Passage E (subdivFresh X t)) :
    GluingDatum X d where
  degree_pos := E.degree_pos
  vertexPartition u := E.vertexPartition (subdivOld X t u)
  edgePartition e := E.edgePartition (subdivOcc X t (some e))
  refines_left e := by
    have h := E.refines_left (subdivOcc X t (some e))
    rw [subdivOcc_some_fst] at h
    exact h
  refines_right e := by
    by_cases he : e = t
    · rw [he]
      have h := E.refines_left (subdivOcc X t none)
      rw [subdivOcc_none] at h
      exact (halves_sameBlocks hP).refines_iff_left.mpr h
    · have h := E.refines_right (subdivOcc X t (some e))
      rw [subdivOcc_some_snd_of_ne t he] at h
      exact h

theorem unrefine_vertex_sameBlocks (E : GluingDatum (subdivTarget X t) d)
    (hP : Passage E (subdivFresh X t)) (v : (subdivTarget X t).V) :
    ((refineDatum (unrefineDatum E hP) t).vertexPartition v).SameBlocks (E.vertexPartition v) := by
  rcases v with u | ⟨⟩
  · exact SheetPartition.SameBlocks.refl _
  · exact hP _ (some_mem_fresh t)

theorem unrefine_edge_sameBlocks (E : GluingDatum (subdivTarget X t) d)
    (hP : Passage E (subdivFresh X t)) (ε : (subdivTarget X t).edges) :
    ((refineDatum (unrefineDatum E hP) t).edgePartition ε).SameBlocks (E.edgePartition ε) := by
  obtain ⟨o, rfl⟩ := (subdivOcc X t).surjective ε
  rcases o with _ | e
  · rw [refineDatum_edgePartition_none]
    exact halves_sameBlocks hP
  · rw [refineDatum_edgePartition_some]
    exact SheetPartition.SameBlocks.refl _

/-- **Passages descend** to the un-refined datum. -/
theorem unrefine_passage (E : GluingDatum (subdivTarget X t) d)
    (hP : Passage E (subdivFresh X t)) (u : X.V) (h : Passage E (subdivOld X t u)) :
    Passage (unrefineDatum E hP) u := by
  intro e he
  have he' := (Finset.mem_filter.mp he).2
  show (E.edgePartition (subdivOcc X t (some e))).SameBlocks
    (E.vertexPartition (subdivOld X t u))
  by_cases het : e = t
  · subst het
    by_cases h1 : (e : X.V × X.V).1 = u
    · refine h _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ?_⟩)
      rw [subdivOcc_some_self, h1]
    · have h2 : (e : X.V × X.V).2 = u := he'.resolve_left h1
      have hn := h _ (h2 ▸ none_mem_snd e)
      exact (halves_sameBlocks hP).trans hn
  · refine h _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩)
    rw [subdivOcc_some_of_ne X het]
    rcases he' with h1 | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])

/-- Refinement preserves blockwise agreement. -/
theorem refine_sameBlocks_vertex {D D' : GluingDatum X d}
    (hV : ∀ v, (D.vertexPartition v).SameBlocks (D'.vertexPartition v))
    (hE : ∀ e, (D.edgePartition e).SameBlocks (D'.edgePartition e)) (t : X.edges)
    (v : (subdivTarget X t).V) :
    ((refineDatum D t).vertexPartition v).SameBlocks ((refineDatum D' t).vertexPartition v) := by
  rcases v with u | ⟨⟩
  · exact hV u
  · exact hE t

theorem refine_sameBlocks_edge {D D' : GluingDatum X d}
    (hE : ∀ e, (D.edgePartition e).SameBlocks (D'.edgePartition e)) (t : X.edges)
    (ε : (subdivTarget X t).edges) :
    ((refineDatum D t).edgePartition ε).SameBlocks ((refineDatum D' t).edgePartition ε) := by
  obtain ⟨o, rfl⟩ := (subdivOcc X t).surjective ε
  rcases o with _ | e
  · rw [refineDatum_edgePartition_none, refineDatum_edgePartition_none]; exact hE t
  · rw [refineDatum_edgePartition_some, refineDatum_edgePartition_some]; exact hE e

end Unrefine

/-! ## 4. Restricting a datum over the glued target to the old sheets over `T₃` -/

section Restrict

variable {T : CFGraph} {d : ℕ} (π : Placement T d)

/-- **The old sheets over `T₃`** of a datum over `π.T₆` whose last sheet is a singleton block
there. -/
def lastRestrict (hd : 0 < d) (F : GluingDatum π.T₆ (d + 1))
    (hV : ∀ u, LastSingleton (F.vertexPartition (π.lift₃ u)))
    (hE : ∀ e, LastSingleton (F.edgePartition (π.liftE₃ e))) : GluingDatum π.T₃ d where
  degree_pos := hd
  vertexPartition u := restrictLast (F.vertexPartition (π.lift₃ u))
  edgePartition e := restrictLast (F.edgePartition (π.liftE₃ e))
  refines_left e := by
    have h := F.refines_left (π.liftE₃ e)
    rw [π.liftE₃_ends] at h
    exact restrictLast_refines (hE e) (hV _) h
  refines_right e := by
    have h := F.refines_right (π.liftE₃ e)
    rw [π.liftE₃_ends] at h
    exact restrictLast_refines (hE e) (hV _) h

end Restrict

/-! ## 5. What the dichotomy gives -/

section Facts

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}

/-- **The shape of the target of a glued member, and its legs** (§4.8). -/
structure GluedFacts (φ : FibreMember (tripodCore core s) y (3 + 2)) where
  /-- The leaf at the end of arm `k`. -/
  v : Fin 3 → φ.target.V
  /-- The inner end of arm `k`, the image of mark `k`. -/
  w : Fin 3 → φ.target.V
  /-- Arm `k`, the lost leaf edge `[w k, v k]`. -/
  lam : Fin 3 → φ.target.edges
  /-- The edge of leg `k` at mark `k`. -/
  leg : Fin 3 → NonDanglingEdge φ.data
  leg_row : ∀ k, φ.ident.row (leg k).stablePath = legSlot p k
  leg_incident : ∀ k, Incident φ.data (leg k).1 (TripodFrame.markSource (Frame.of φ) k)
  leg_target : ∀ k, (leg k).1.1.1 = lam k
  lam_key : ∀ k, GluingTransport.edgeKey φ.target (lam k) = s(w k, v k)
  v_leaf : ∀ k, vertex_degree φ.target (v k) = 1
  w_degree : ∀ k, vertex_degree φ.target (w k) = 3
  w_injective : Function.Injective w
  mark_target : ∀ k, (TripodFrame.markSource (Frame.of φ) k).1.1 = w k
  centre_ne : ∀ k, TripodFrame.centreTarget (Frame.of φ) ≠ v k

/-- **The dichotomy facts** (Theorem 4.7(a), Lemmas 4.4 and 4.5; §4.8), from
`Dichotomy`: a glued member is not a claw (`not_isGlued_of_isClaw`); its lost edges are the three
leg leaf edges (`isLost_iff_detour`); the inner end of each is trivalent (`exists_triEdges`), so it
is the end at the mark, and these ends are distinct. -/
theorem nonempty_gluedFacts (φ : FibreMember (tripodCore core s) y (3 + 2))
    (hGlued : MemberIsGlued φ) : Nonempty (GluedFacts φ) := by
  classical
  set κ := Frame.of φ with hκ
  have hG : ∀ k : Fin 3, ∃ e : NonDanglingEdge κ.data, κ.ident.row e.stablePath = legSlot p k ∧
      Incident κ.data e.1 (TripodFrame.markSource κ k) ∧ IsLeafEdge κ.target e.1.1.1 := hGlued
  choose ℓ hrow hinc hleaf using hG
  have hc : TripodFrame.centreTarget κ ∈ TripodFrame.gImage κ := by
    by_contra h
    exact Dichotomy.not_isGlued_of_isClaw κ h (fun k ↦ ⟨ℓ k, hrow k, hinc k, hleaf k⟩)
  have hLost := Dichotomy.isLost_iff_detour κ ℓ hrow hleaf
  have hLeafLost : ∀ t, Dichotomy.IsLost κ t → IsLeafEdge κ.target t := by
    intro t ht
    obtain ⟨k, rfl⟩ := (hLost t).mp ht
    exact hleaf k
  have hlamLost : ∀ k, Dichotomy.IsLost κ (ℓ k).1.1.1 := fun k ↦ (hLost _).mpr ⟨k, rfl⟩
  choose w a b hwt hTri ha hb using fun k ↦
    Dichotomy.exists_triEdges κ hc hLeafLost (hlamLost k)
  have hdeg3 : ∀ k, vertex_degree κ.target (w k) = 3 := fun k ↦ by
    rw [← Dichotomy.card_incidentEdges_eq_vertex_degree, (hTri k).card]; rfl
  -- the mark is over the inner end
  have hmark : ∀ k, (TripodFrame.markSource κ k).1.1 = w k := by
    intro k
    have hend := Dichotomy.incident_target (hinc k)
    have hnl := Dichotomy.vertex_degree_ne_one_of_three_le κ.fullDim _
      (Dichotomy.three_le_markSource κ k)
    by_contra hne
    have hne3 : vertex_degree κ.target (w k) ≠ 1 := by rw [hdeg3]; norm_num
    rcases hleaf k with h | h <;> rcases hend with h' | h' <;> rcases hwt k with h'' | h''
    · exact hnl (h' ▸ h)
    · exact hnl (h' ▸ h)
    · exact hne3 (h'' ▸ h)
    · exact hne (h'.symm.trans h'')
    · exact hne (h'.symm.trans h'')
    · exact hne3 (h'' ▸ h)
    · exact hnl (h' ▸ h)
    · exact hnl (h' ▸ h)
  -- the other end is the leaf
  let v : Fin 3 → κ.target.V := fun k ↦
    if ((ℓ k).1.1.1 : κ.target.V × κ.target.V).1 = w k then
      ((ℓ k).1.1.1 : κ.target.V × κ.target.V).2
    else ((ℓ k).1.1.1 : κ.target.V × κ.target.V).1
  have hkey : ∀ k, GluingTransport.edgeKey κ.target (ℓ k).1.1.1 = s(w k, v k) := by
    intro k
    unfold GluingTransport.edgeKey
    simp only [v]
    split_ifs with h
    · rw [h]
    · rw [(hwt k).resolve_left h, Sym2.eq_swap]
  have hvleaf : ∀ k, vertex_degree κ.target (v k) = 1 := by
    intro k
    have hne3 : vertex_degree κ.target (w k) ≠ 1 := by rw [hdeg3]; norm_num
    simp only [v]
    split_ifs with h
    · rcases hleaf k with h' | h'
      · exact absurd (h ▸ h') hne3
      · exact h'
    · rcases hleaf k with h' | h'
      · exact h'
      · exact absurd ((hwt k).resolve_left h ▸ h') hne3
  -- the inner ends are distinct
  have hlamInj : Function.Injective fun k ↦ (ℓ k).1.1.1 := fun i j h ↦
    Dichotomy.leg_eq_of_isLeafEdge κ (ℓ i) (ℓ j) (hrow i) (hrow j) (hleaf i) h.symm
  have hwInj : Function.Injective w := by
    intro i j hij
    have hmem : (ℓ i).1.1.1 ∈ GluingDatum.incidentEdges (w j) := by
      rw [← hij]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwt i⟩
    rcases ((hTri j).mem_iff _).mp hmem with h | h | h
    · exact hlamInj h
    · exact absurd (h ▸ hlamLost i) (ha j)
    · exact absurd (h ▸ hlamLost i) (hb j)
  have hcentre : ∀ k, TripodFrame.centreTarget κ ≠ v k := by
    intro k h
    have hnl := Dichotomy.vertex_degree_ne_one_of_three_le κ.fullDim _
      (Dichotomy.three_le_centreSource κ)
    exact hnl (by
      show vertex_degree κ.target (TripodFrame.centreTarget κ) = 1
      rw [h]; exact hvleaf k)
  exact ⟨{
    v := v
    w := w
    lam := fun k ↦ (ℓ k).1.1.1
    leg := ℓ
    leg_row := hrow
    leg_incident := hinc
    leg_target := fun _ ↦ rfl
    lam_key := hkey
    v_leaf := hvleaf
    w_degree := hdeg3
    w_injective := hwInj
    mark_target := hmark
    centre_ne := hcentre }⟩

end Facts

/-! ## 6. The Y-sheet -/

section Sheets

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}

/-- The sheet of the centre: in a glued member, the sheet of `Y′` over `T̂`. -/
def ySheet (φ : FibreMember (tripodCore core s) y (3 + 2)) : Fin (3 + 2) :=
  (Dichotomy.centreSource (Frame.of φ)).1.2

/-- The sheet of the edge of leg `k` at mark `k`. -/
def GluedFacts.sheet {φ : FibreMember (tripodCore core s) y (3 + 2)} (G : GluedFacts φ)
    (k : Fin 3) : Fin (3 + 2) :=
  (G.leg k).1.1.2

/-- **The sheet shape of a glued member** (§5.5, the onto step): `Y′` is a
copy of `T̂` in the centre's sheet `y` together with three hairpins. Over every target vertex and
edge off the arms, `y` is a block on its own; each arm is discrete; at the tip `v k` the only
glued pair is the sheet `σ k` of leg `k` with `y`; and at the inner end `w k` every block is a
passage between its two `T̂`-edges. -/
structure SheetShape {φ : FibreMember (tripodCore core s) y (3 + 2)} (G : GluedFacts φ) : Prop where
  sheet_ne : ∀ k, G.sheet k ≠ ySheet φ
  vertex_y : ∀ x, (∀ k, x ≠ G.v k) → ∀ i,
    (φ.data.vertexPartition x).Rel i (ySheet φ) ↔ i = ySheet φ
  edge_y : ∀ e, (∀ k, e ≠ G.lam k) → ∀ i,
    (φ.data.edgePartition e).Rel i (ySheet φ) ↔ i = ySheet φ
  arm : ∀ k i j, (φ.data.edgePartition (G.lam k)).Rel i j ↔ i = j
  tip : ∀ k i j, (φ.data.vertexPartition (G.v k)).Rel i j ↔
    i = j ∨ (i = G.sheet k ∧ j = ySheet φ) ∨ (i = ySheet φ ∧ j = G.sheet k)
  pass : ∀ k e, e ∈ GluingDatum.incidentEdges (G.w k) → e ≠ G.lam k →
    (φ.data.edgePartition e).SameBlocks (φ.data.vertexPartition (G.w k))

/-- **The Y-sheet of a glued member**: `SheetShape` without the passage clause, which follows
(`pass_of_arm`). -/
structure YSheet {φ : FibreMember (tripodCore core s) y (3 + 2)} (G : GluedFacts φ) : Prop where
  sheet_ne : ∀ k, G.sheet k ≠ ySheet φ
  vertex_y : ∀ x, (∀ k, x ≠ G.v k) → ∀ i,
    (φ.data.vertexPartition x).Rel i (ySheet φ) ↔ i = ySheet φ
  edge_y : ∀ e, (∀ k, e ≠ G.lam k) → ∀ i,
    (φ.data.edgePartition e).Rel i (ySheet φ) ↔ i = ySheet φ
  arm : ∀ k i j, (φ.data.edgePartition (G.lam k)).Rel i j ↔ i = j
  tip : ∀ k i j, (φ.data.vertexPartition (G.v k)).Rel i j ↔
    i = j ∨ (i = G.sheet k ∧ j = ySheet φ) ∨ (i = ySheet φ ∧ j = G.sheet k)

/-- **The arms are discrete** (Part I `rem-leaves-min-change`): every source edge over the leaf edge
`lam k` has index one (`LeafFibre.sourceEdgeIndex_eq_one_above_leaf`), so every block over it is a
single sheet. -/
theorem arm_discrete {φ : FibreMember (tripodCore core s) y (3 + 2)} (G : GluedFacts φ)
    (k : Fin 3) (i j : Fin (3 + 2)) :
    (φ.data.edgePartition (G.lam k)).Rel i j ↔ i = j := by
  classical
  set P := φ.data.edgePartition (G.lam k) with hP
  have hv : IsLeafVertex φ.target (G.v k) := Dichotomy.isLeafVertex_of_vertex_degree (G.v_leaf k)
  have hmem : G.lam k ∈ GluingDatum.incidentEdges (G.v k) := by
    have hk := G.lam_key k
    unfold GluingTransport.edgeKey at hk
    rcases Sym2.eq_iff.mp hk with ⟨-, h⟩ | ⟨h, -⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩
  have hleaf := eq_leafEdge_of_mem hv hmem
  have hone : P.blockCard i = 1 := by
    have h1 := LeafFibre.sourceEdgeIndex_eq_one_above_leaf φ.fullDim hv
      (edge := φ.data.sourceEdge (G.lam k) i) hleaf
    have hb : P.blockCard (P.repr i) = P.blockCard i := by
      unfold SheetPartition.blockCard
      rw [SheetPartition.block_eq_of_rel _ (P.rel_repr_left i)]
    rw [← hb]
    exact h1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hone
  have hia : i = a := Finset.mem_singleton.mp (ha ▸ P.self_mem_block i)
  constructor
  · intro h
    have hj : j ∈ P.block i := (P.mem_block_iff i j).mpr h
    rw [ha, Finset.mem_singleton] at hj
    exact hia.trans hj.symm
  · rintro rfl
    rfl

/-! ### The proof of the Y-sheet (§5.5, Lemma 4.8)

`Y′` is read as the source vertices that retract (along dangling edges) onto a surviving vertex on
the tripod side, the centre or a vertex interior to a leg (`YType`). It meets the rest only at the
leg edges at the marks (`eq_leg_of_cut`, from the incidences of `Γ̃`), so the sheet of the centre,
followed along the target edges that are not arms, stays in `Y′` (`yType_ySheet`). By the
leg-index lemma (Lemma 4.8) for a glued member (`legEdge_index`, the column trick of
`ClawShape.index_step` with the arms as the lost edges) every surviving edge of `Y′` has index one,
so off the three leaves every vertex of `Y′` is a single sheet (`blockCard_eq_one_of_yType`). This
is `ySheet_singleton`. Along leg `k` the edges in the Y-sheet include the last one but not the first
(`sheet_ne_ySheet`), and where this changes the leg is at its fold over `v k` (`tip_rel`); this is
`hairpin_turn`. The jump rule and the value `k₀ = 1` are not needed. -/

namespace YProof

variable {φ : FibreMember (tripodCore core s) y (3 + 2)} (G : GluedFacts φ)

theorem lam_mem_v (k : Fin 3) : G.lam k ∈ GluingDatum.incidentEdges (G.v k) := by
  have hk := G.lam_key k
  unfold GluingTransport.edgeKey at hk
  rcases Sym2.eq_iff.mp hk with ⟨-, h⟩ | ⟨h, -⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩

theorem v_isLeaf (k : Fin 3) : IsLeafVertex φ.target (G.v k) :=
  Dichotomy.isLeafVertex_of_vertex_degree (G.v_leaf k)

theorem lam_eq_leafEdge (k : Fin 3) : G.lam k = leafEdge (v_isLeaf G k) :=
  eq_leafEdge_of_mem (v_isLeaf G k) (lam_mem_v G k)

/-- The ends of arm `k` are `w k` and `v k`. -/
theorem lam_ends (k : Fin 3) {x : φ.target.V} (hx : G.lam k ∈ GluingDatum.incidentEdges x) :
    x = G.w k ∨ x = G.v k := by
  have hk := G.lam_key k
  unfold GluingTransport.edgeKey at hk
  rcases (Finset.mem_filter.mp hx).2 with h | h <;>
    rcases Sym2.eq_iff.mp hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (h.symm.trans h1)
  · exact Or.inr (h.symm.trans h1)
  · exact Or.inr (h.symm.trans h2)
  · exact Or.inl (h.symm.trans h2)

theorem w_ne_v (j k : Fin 3) : G.w j ≠ G.v k := fun h ↦ by
  have h1 := G.w_degree j
  rw [h, G.v_leaf k] at h1
  omega

/-- The only target edge at the leaf `v k` is the arm. -/
theorem eq_lam_of_mem_v {k : Fin 3} {t : φ.target.edges}
    (ht : t ∈ GluingDatum.incidentEdges (G.v k)) : t = G.lam k :=
  (eq_leafEdge_of_mem (v_isLeaf G k) ht).trans (lam_eq_leafEdge G k).symm

theorem lam_isLeafEdge (k : Fin 3) : IsLeafEdge φ.target (G.lam k) := by
  rcases (Finset.mem_filter.mp (lam_mem_v G k)).2 with h | h
  · exact Or.inl (h ▸ G.v_leaf k)
  · exact Or.inr (h ▸ G.v_leaf k)

theorem lam_isLost (k : Fin 3) : Dichotomy.IsLost (Frame.of φ) (G.lam k) := by
  have h := Dichotomy.isLost_of_leg_isLeafEdge (Frame.of φ) k (G.leg k) (G.leg_row k)
    (by rw [G.leg_target k]; exact lam_isLeafEdge G k)
  rwa [G.leg_target k] at h

theorem lam_injective : Function.Injective G.lam := by
  intro i j h
  apply Dichotomy.leg_eq_of_isLeafEdge (Frame.of φ) (G.leg i) (G.leg j) (G.leg_row i)
    (G.leg_row j)
  · rw [G.leg_target i]; exact lam_isLeafEdge G i
  · rw [G.leg_target i, G.leg_target j, h]

/-- **A leg edge over a leaf edge lies over the arm of its own leg** (Lemma 4.4 with the
lost-edge bound): it would otherwise be a fourth lost edge. -/
theorem legEdge_target_of_isLeafEdge {j : Fin 3} (e : NonDanglingEdge φ.data)
    (hrow : φ.ident.row e.stablePath = legSlot p j) (hleaf : IsLeafEdge φ.target e.1.1.1) :
    e.1.1.1 = G.lam j := by
  by_cases h : ∃ i, e.1.1.1 = G.lam i
  · obtain ⟨i, hi⟩ := h
    have hij := Dichotomy.leg_eq_of_isLeafEdge (Frame.of φ) (G.leg i) e (G.leg_row i) hrow
      (by rw [G.leg_target i]; exact lam_isLeafEdge G i) (by rw [hi, G.leg_target i])
    rw [hi, hij]
  · push Not at h
    exfalso
    exact Dichotomy.false_of_fourth_lost (Frame.of φ) G.leg G.leg_row
      (fun k ↦ by rw [G.leg_target k]; exact lam_isLeafEdge G k)
      (Dichotomy.isLost_of_leg_isLeafEdge (Frame.of φ) j e hrow hleaf)
      (fun k ↦ by rw [G.leg_target k]; exact h k)

/-- A target edge at a divalent vertex is not an arm (the ends of an arm have valency three and
one). -/
theorem ne_lam_of_divalent {u : φ.target.V} (hDiv : (GluingDatum.incidentEdges u).card = 2)
    {t : φ.target.edges} (ht : t ∈ GluingDatum.incidentEdges u) (j : Fin 3) : t ≠ G.lam j := by
  rintro rfl
  have hc := Dichotomy.card_incidentEdges_eq_vertex_degree φ.target u
  rw [hDiv] at hc
  rcases lam_ends G j ht with rfl | rfl
  · rw [G.w_degree j] at hc; omega
  · rw [G.v_leaf j] at hc; omega

theorem leg_index (k : Fin 3) : φ.data.sourceEdgeIndex (G.leg k).1 = 1 :=
  LeafFibre.sourceEdgeIndex_eq_one_above_leaf φ.fullDim (v_isLeaf G k)
    ((G.leg_target k).trans (lam_eq_leafEdge G k))

include G in
/-- **Leg indices, the local step, for a glued member** (as `ClawShape.index_step`): an index change
along a leg at a vertex `A` makes `u = φ(A)` divalent with `A` its only ramified block; the two
columns at `u` then agree on every G-row, and neither is an arm, against the column trick. -/
theorem index_step {k : Fin 3} {f g : NonDanglingEdge φ.data} (hfg : Consecutive φ.data f g)
    (hf : φ.ident.row f.stablePath = legSlot p k) (hf1 : φ.data.sourceEdgeIndex f.1 = 1) :
    φ.data.sourceEdgeIndex g.1 = 1 := by
  classical
  obtain ⟨hne, A, hfA, hgA, hA2⟩ := hfg
  have hg : φ.ident.row g.stablePath = legSlot p k := by
    rw [← stablePath_eq_of_consecutive ⟨hne, A, hfA, hgA, hA2⟩]
    exact hf
  have hgu := ((incident_iff_target_mem_and_rel φ.data g.1 A).mp hgA).1
  by_cases hLeafU : IsLeafVertex φ.target A.1.1
  · exact LeafFibre.sourceEdgeIndex_eq_one_above_leaf φ.fullDim hLeafU
      (eq_leafEdge_of_mem hLeafU hgu)
  have hcard : 2 ≤ (GluingDatum.incidentEdges A.1.1).card := by
    have h0 : 0 < (GluingDatum.incidentEdges A.1.1).card := Finset.card_pos.mpr ⟨_, hgu⟩
    have h1 : (GluingDatum.incidentEdges A.1.1).card ≠ 1 := hLeafU
    omega
  have hr1 := DivalentSourceLocal.localRamification_le_one_of_nonleaf φ.data φ.fullDim.valid A
    (φ.fullDim.changeMinimal _) hcard
  have hr0 := φ.data.localRamification_nonneg A.1.1 (φ.fullDim.valid.2 _) ⟨A.1.2, A.2⟩
  have hfgne : f.1 ≠ g.1 := fun h ↦ hne (Subtype.ext h)
  have hPair : nonDanglingIncident φ.data A = {f.1, g.1} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨f.2, hfA⟩
      · exact (mem_nonDanglingIncident _ _ _).mpr ⟨g.2, hgA⟩
    · rw [card_nonDanglingIncident, hA2, Finset.card_pair hfgne]
  have hSum := Dichotomy.sum_index_nonDanglingIncident φ.fullDim.danglingEdgeNoGlue A
  rw [hPair, Finset.sum_pair hfgne, hA2, hf1] at hSum
  have hgLe : φ.data.sourceEdgeIndex g.1 ≤ (φ.data.vertexPartition A.1.1).blockCard A.1.2 :=
    StableLocalProperties.sourceEdgeIndex_le_blockCard φ.data A ⟨g.1, hgA⟩
  have hgPos := GluingDatum.sourceEdgeIndex_pos φ.data g.1
  by_contra hg1
  have hrA : φ.data.localRamification A.1.1 ⟨A.1.2, A.2⟩ = 1 := by
    push_cast at hSum
    omega
  have hch := IndexPattern.localRamification_le_targetChange φ.fullDim (wall := A.1.1)
    ⟨A.1.2, A.2⟩
  rw [IndexPattern.targetChange_eq_three_sub_valency φ.fullDim] at hch
  have hDiv : (GluingDatum.incidentEdges A.1.1).card = 2 := by omega
  have hChange : φ.data.targetChange A.1.1 = 1 := by
    rw [IndexPattern.targetChange_eq_three_sub_valency φ.fullDim, hDiv]
    norm_num
  have hOthers : ∀ block : (φ.data.vertexPartition A.1.1).Blocks, block ≠ ⟨A.1.2, A.2⟩ →
      φ.data.localRamification A.1.1 block = 0 := by
    intro block hNe
    have hNonneg : ∀ b : (φ.data.vertexPartition A.1.1).Blocks,
        0 ≤ φ.data.localRamification A.1.1 b := fun b ↦
      φ.data.localRamification_nonneg A.1.1 (φ.fullDim.valid.2 _) b
    have hSplit := Finset.sum_erase_add
      (Finset.univ : Finset (φ.data.vertexPartition A.1.1).Blocks)
      (fun b ↦ φ.data.localRamification A.1.1 b)
      (Finset.mem_univ (⟨A.1.2, A.2⟩ : (φ.data.vertexPartition A.1.1).Blocks))
    have hEraseSum : (∑ b ∈ (Finset.univ :
        Finset (φ.data.vertexPartition A.1.1).Blocks).erase ⟨A.1.2, A.2⟩,
        φ.data.localRamification A.1.1 b) = 0 := by
      have hTot : (∑ b : (φ.data.vertexPartition A.1.1).Blocks,
          φ.data.localRamification A.1.1 b) = 1 := hChange
      rw [hrA] at hSplit
      omega
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ hNonneg b)).mp hEraseSum block
      (Finset.mem_erase.mpr ⟨hNe, Finset.mem_univ _⟩)
  obtain ⟨u₁, u₂, hu12, hU⟩ := Finset.card_eq_two.mp hDiv
  have hu₁ : u₁ ∈ GluingDatum.incidentEdges A.1.1 := by rw [hU]; simp
  have hu₂ : u₂ ∈ GluingDatum.incidentEdges A.1.1 := by rw [hU]; simp
  have hCols : ∀ r, IsGSlot ((Frame.of φ).slot r) →
      (Frame.of φ).matrix r (φ.fullDim.labelling.targetEdge.symm u₁) =
        (Frame.of φ).matrix r (φ.fullDim.labelling.targetEdge.symm u₂) := by
    intro r hr
    refine ClawShape.matrix_eq_of_divalent_of_row (Frame.of φ) hDiv hu12 hu₁ hu₂ r ?_
    intro f' hS hRow hf'u
    apply hOthers
    intro hEq
    have hRepr : (φ.data.vertexPartition A.1.1).repr f'.1.2 = A.1.2 := congrArg Subtype.val hEq
    have hInc : Incident φ.data f' A := by
      refine (incident_iff_target_mem_and_rel φ.data f' A).mpr ⟨hf'u, ?_⟩
      show (φ.data.vertexPartition A.1.1).repr A.1.2 = (φ.data.vertexPartition A.1.1).repr f'.1.2
      rw [hRepr, A.2]
    have hmem : f' ∈ nonDanglingIncident φ.data A := (mem_nonDanglingIncident _ _ _).mpr ⟨hS, hInc⟩
    rw [hPair] at hmem
    have hrowk : φ.ident.row (NonDanglingEdge.stablePath ⟨f', hS⟩) = legSlot p k := by
      rcases Finset.mem_insert.mp hmem with h | h
      · rw [show (⟨f', hS⟩ : NonDanglingEdge φ.data) = f from Subtype.ext h]
        exact hf
      · rw [show (⟨f', hS⟩ : NonDanglingEdge φ.data) = g from
          Subtype.ext (Finset.mem_singleton.mp h)]
        exact hg
    have hslot : (Frame.of φ).slot r = φ.ident.row (NonDanglingEdge.stablePath ⟨f', hS⟩) :=
      ((Dichotomy.ident_row_eq_slot (Frame.of φ) ⟨f', hS⟩).trans (congrArg (Frame.of φ).slot hRow)).symm
    rw [hslot, hrowk] at hr
    exact legSlot_not_isGSlot k hr
  exact Dichotomy.false_of_matrix_eq (Frame.of φ) G.lam (lam_injective G) (lam_isLost G)
    (a := u₁) (b := u₂) (fun j ↦ ne_lam_of_divalent G hDiv hu₁ j) hu12 hCols

include G in
/-- **Leg indices for a glued member** (Lemma 4.8): every surviving edge of every leg has index
one. The index is constant along the leg (`index_step`) and is one on the edge at the mark, which
lies over the arm (`leg_index`). -/
theorem legEdge_index {k : Fin 3} (e : NonDanglingEdge φ.data)
    (he : φ.ident.row e.stablePath = legSlot p k) : φ.data.sourceEdgeIndex e.1 = 1 := by
  have hClosed : ∀ f g : NonDanglingEdge φ.data, Consecutive φ.data f g →
      (φ.ident.row f.stablePath = legSlot p k ∧ φ.data.sourceEdgeIndex f.1 = 1) →
      (φ.ident.row g.stablePath = legSlot p k ∧ φ.data.sourceEdgeIndex g.1 = 1) := by
    rintro f g hfg ⟨hf, hf1⟩
    refine ⟨?_, index_step G hfg hf hf1⟩
    rw [← stablePath_eq_of_consecutive hfg]
    exact hf
  have hEqv : Relation.EqvGen (Consecutive φ.data) (G.leg k) e :=
    (stablePath_eq_iff _ _).mp (φ.ident.row.injective ((G.leg_row k).trans he.symm))
  exact ((eqvGen_iff_of_closed hClosed hEqv).mp ⟨G.leg_row k, leg_index G k⟩).2


/-! ### `Y′`: the source vertices retracting onto the tripod -/

/-- **A surviving vertex on the tripod side**: not a mark, and on a surviving leg edge (so the
centre, or a vertex interior to a leg). -/
def TripodSide (φ : FibreMember (tripodCore core s) y (3 + 2)) (X : φ.data.SourceVertex) : Prop :=
  (∀ k, X ≠ TripodFrame.markSource (Frame.of φ) k) ∧
    ∃ e : NonDanglingEdge φ.data, Incident φ.data e.1 X ∧ ¬ IsGSlot (φ.ident.row e.stablePath)

/-- **A source vertex of `Y′`**: it retracts (along dangling edges) onto a surviving vertex on the
tripod side. -/
def YType (φ : FibreMember (tripodCore core s) y (3 + 2)) (A : φ.data.SourceVertex) : Prop :=
  ∃ X : φ.data.SourceVertex, 0 < nonDanglingValency φ.data X ∧ TripodSide φ X ∧
    PendantRetraction.retractVertex A = PendantRetraction.retractVertex X

theorem pos_of_incident {A : φ.data.SourceVertex} (e : NonDanglingEdge φ.data)
    (h : Incident φ.data e.1 A) : 0 < nonDanglingValency φ.data A := by
  rw [← card_nonDanglingIncident]
  exact Finset.card_pos.mpr ⟨e.1, (mem_nonDanglingIncident _ _ _).mpr ⟨e.2, h⟩⟩

/-- Every surviving edge at a vertex on the tripod side is a leg edge. -/
theorem TripodSide.not_isGSlot {X : φ.data.SourceVertex} (h : TripodSide φ X)
    (f : NonDanglingEdge φ.data) (hf : Incident φ.data f.1 X) :
    ¬ IsGSlot (φ.ident.row f.stablePath) := by
  obtain ⟨hm, e, he, heG⟩ := h
  by_cases hXc : X = Dichotomy.centreSource (Frame.of φ)
  · rw [hXc] at hf
    exact Dichotomy.not_isGSlot_of_incident_centre (Frame.of φ) f hf
  · intro hfG
    exact heG (Dichotomy.isGSlot_of_incident_of_ne (Frame.of φ) hXc hm hf hfG he)

include G in
/-- **`Y′` meets `G′` only at the leg edges at the marks**: a surviving edge from the tripod side
to a vertex off it is the edge of a leg at its mark. -/
theorem eq_leg_of_cut {f : NonDanglingEdge φ.data} {X X' : φ.data.SourceVertex}
    (hX : Incident φ.data f.1 X) (hX' : Incident φ.data f.1 X')
    (hT : TripodSide φ X) (hT' : ¬ TripodSide φ X') : ∃ k, f = G.leg k := by
  have hfG := hT.not_isGSlot f hX
  have hm : ∃ k, X' = TripodFrame.markSource (Frame.of φ) k := by
    by_contra h
    push Not at h
    exact hT' ⟨h, f, hX', hfG⟩
  obtain ⟨k, rfl⟩ := hm
  have hrow : φ.ident.row f.stablePath = legSlot p k :=
    (Dichotomy.isGSlot_or_eq_legSlot_of_incident_mark (Frame.of φ) k f hX').resolve_left hfG
  exact ⟨k, Dichotomy.legEdge_unique_at_mark (Frame.of φ) k hX' (G.leg_incident k) hrow
    (G.leg_row k)⟩

include G in
/-- **`Y′` is closed off the leg edges at the marks.** -/
theorem yType_of_incident {f : φ.data.SourceEdge} {A A' : φ.data.SourceVertex}
    (hA : Incident φ.data f A) (hA' : Incident φ.data f A') (hY : YType φ A)
    (hf : ∀ k, f ≠ (G.leg k).1) : YType φ A' := by
  by_cases hAA : A = A'
  · rw [← hAA]; exact hY
  obtain ⟨X, hXpos, hXT, hXr⟩ := hY
  by_cases hD : IsDangling φ.data f
  · refine ⟨X, hXpos, hXT, ?_⟩
    have hEnds : φ.data.sourceEnds f = (A, A') ∨ φ.data.sourceEnds f = (A', A) := by
      rcases hA with h1 | h1 <;> rcases hA' with h2 | h2
      · exact absurd (h1.symm.trans h2) hAA
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h2 h1)
      · exact absurd (h1.symm.trans h2) hAA
    have hstep : PendantRetraction.DanglingStep A A' := ⟨f, hD, hEnds⟩
    rw [← hXr]
    exact (Quotient.sound (Relation.ReflTransGen.single hstep)).symm
  · have hApos := pos_of_incident ⟨f, hD⟩ hA
    have hA'pos := pos_of_incident ⟨f, hD⟩ hA'
    have hAX : A = X := PendantRetraction.surviving_vertex_unique hApos hXpos hXr
    subst hAX
    by_cases hT' : TripodSide φ A'
    · exact ⟨A', hA'pos, hT', rfl⟩
    · obtain ⟨k, hk⟩ := eq_leg_of_cut G (f := ⟨f, hD⟩) hA hA' hXT hT'
      exact absurd (congrArg Subtype.val hk) (hf k)

theorem yType_centre : YType φ (Dichotomy.centreSource (Frame.of φ)) := by
  have h3 := Dichotomy.three_le_centreSource (Frame.of φ)
  have hpos : 0 < nonDanglingValency φ.data (Dichotomy.centreSource (Frame.of φ)) :=
    Nat.lt_of_lt_of_le (by norm_num) h3
  obtain ⟨e, he⟩ := Dichotomy.exists_nonDanglingEdge_incident _ hpos
  exact ⟨_, hpos, ⟨fun k ↦ ClawShape.centreSource_ne_markSource (Frame.of φ) k, e, he,
    Dichotomy.not_isGSlot_of_incident_centre (Frame.of φ) e he⟩, rfl⟩

theorem not_yType_mark (k : Fin 3) : ¬ YType φ (TripodFrame.markSource (Frame.of φ) k) := by
  rintro ⟨X, hXpos, hXT, hXr⟩
  have hpos : 0 < nonDanglingValency φ.data (TripodFrame.markSource (Frame.of φ) k) :=
    Nat.lt_of_lt_of_le (by norm_num) (Dichotomy.three_le_markSource (Frame.of φ) k)
  exact hXT.1 k (PendantRetraction.surviving_vertex_unique hpos hXpos hXr).symm

/-- Every target vertex carries an edge (the target is a connected tree with an edge). -/
theorem incidentEdges_nonempty (x : φ.target.V) : (GluingDatum.incidentEdges x).Nonempty := by
  classical
  have hnt := φ.fullDim.nontrivial_target
  obtain ⟨z, hz⟩ := exists_ne x
  obtain ⟨a, ha, b, hb, hab⟩ := φ.fullDim.targetConnected {x} ⟨x, z, Finset.mem_singleton_self x,
    by simpa using hz⟩
  rw [Finset.mem_singleton] at ha
  subst ha
  rw [← GluingTransport.card_edgeKey_fiber] at hab
  obtain ⟨⟨e, he⟩⟩ := Fintype.card_pos_iff.mp hab
  unfold GluingTransport.edgeKey at he
  refine ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨-, h⟩
  · exact Or.inl h
  · exact Or.inr h

include G in
/-- **The vertices of `Y′` off the three leaves `v k` are single sheets**: the surviving edges
there are leg edges of index one (Lemma 4.8), so `r = 2|A| - 2 ≤ 1` off the leaves; over another
leaf a surviving vertex on a leg would be a fold of that leg over a second leaf
(`legEdge_target_of_isLeafEdge`). -/
theorem blockCard_eq_one_of_yType {A : φ.data.SourceVertex} (hY : YType φ A)
    (hv : ∀ k, A.1.1 ≠ G.v k) : (φ.data.vertexPartition A.1.1).blockCard A.1.2 = 1 := by
  classical
  -- a surviving edge at `A` is a leg edge
  have hLegRow : ∀ g : NonDanglingEdge φ.data, Incident φ.data g.1 A →
      ∃ j, φ.ident.row g.stablePath = legSlot p j := by
    intro g hgA
    obtain ⟨X, hXpos, hXT, hXr⟩ := hY
    have hAX := PendantRetraction.surviving_vertex_unique (pos_of_incident g hgA) hXpos hXr
    subst hAX
    rcases Dichotomy.isGSlot_or_eq_legSlot (φ.ident.row g.stablePath) with hG | hj
    · exact absurd hG (hXT.not_isGSlot g hgA)
    · exact hj
  by_cases hLeaf : IsLeafVertex φ.target A.1.1
  · rcases LeafFibre.dichotomy φ.fullDim hLeaf ⟨A.1.2, A.2⟩ with ⟨-, h1, -⟩ | ⟨-, -, -, e, he⟩
    · exact h1
    · exfalso
      obtain ⟨j, hj⟩ := hLegRow ⟨e.1, he⟩ e.2
      have hmem := ((incident_iff_target_mem_and_rel φ.data e.1 A).mp e.2).1
      have hdeg : vertex_degree φ.target A.1.1 = 1 := by
        have := Dichotomy.card_incidentEdges_eq_vertex_degree φ.target A.1.1
        rw [show (GluingDatum.incidentEdges A.1.1).card = 1 from hLeaf] at this
        omega
      have hLE : IsLeafEdge φ.target e.1.1.1 := by
        rcases (Finset.mem_filter.mp hmem).2 with h | h
        · exact Or.inl (by rw [h]; exact hdeg)
        · exact Or.inr (by rw [h]; exact hdeg)
      have ht := legEdge_target_of_isLeafEdge G ⟨e.1, he⟩ hj hLE
      have hmem' : G.lam j ∈ GluingDatum.incidentEdges A.1.1 := by
        rw [← ht]; exact hmem
      rcases lam_ends G j hmem' with h | h
      · have h1 := G.w_degree j
        rw [← h, hdeg] at h1
        omega
      · exact hv j h
  · have hcard : 2 ≤ (GluingDatum.incidentEdges A.1.1).card := by
      have h0 := (incidentEdges_nonempty A.1.1).card_pos
      have h1 : (GluingDatum.incidentEdges A.1.1).card ≠ 1 := hLeaf
      omega
    have hr1 := DivalentSourceLocal.localRamification_le_one_of_nonleaf φ.data φ.fullDim.valid A
      (φ.fullDim.changeMinimal _) hcard
    have hEdges : ∀ g ∈ nonDanglingIncident φ.data A, (φ.data.sourceEdgeIndex g : ℤ) = 1 := by
      intro g hg
      obtain ⟨hgS, hgA⟩ := (mem_nonDanglingIncident _ _ _).mp hg
      obtain ⟨j, hj⟩ := hLegRow ⟨g, hgS⟩ hgA
      rw [legEdge_index G ⟨g, hgS⟩ hj, Nat.cast_one]
    have hSum := Dichotomy.sum_index_nonDanglingIncident φ.fullDim.danglingEdgeNoGlue A
    rw [Finset.sum_congr rfl hEdges, Finset.sum_const, card_nonDanglingIncident, nsmul_eq_mul,
      mul_one] at hSum
    have hpos := SheetPartition.blockCard_pos (φ.data.vertexPartition A.1.1) A.1.2
    omega

/-! ### The Y-sheet stays in `Y′` off the leaves -/

include G in
/-- One step of a sheet along a target edge with neither end a leaf `v k`: the edge is not an
arm, so its source edge in that sheet is not a leg edge at a mark. -/
theorem yType_step₀ (t : φ.target.edges) (i : Fin (3 + 2))
    (h1 : ∀ k, (t : φ.target.V × φ.target.V).1 ≠ G.v k)
    (h2 : ∀ k, (t : φ.target.V × φ.target.V).2 ≠ G.v k)
    (hY : YType φ (φ.data.sourceEndpoint (t : φ.target.V × φ.target.V).1 i)) :
    YType φ (φ.data.sourceEndpoint (t : φ.target.V × φ.target.V).2 i) := by
  have hne : ∀ k, φ.data.sourceEdge t i ≠ (G.leg k).1 := by
    intro k h
    have ht : t = G.lam k := by
      rw [← G.leg_target k, ← h]
      rfl
    have ha : G.lam k ∈ GluingDatum.incidentEdges (t : φ.target.V × φ.target.V).1 := by
      rw [← ht]; exact Dichotomy.mem_incidentEdges_fst t
    have hb : G.lam k ∈ GluingDatum.incidentEdges (t : φ.target.V × φ.target.V).2 := by
      rw [← ht]; exact Dichotomy.mem_incidentEdges_snd t
    rcases lam_ends G k ha with ha | ha
    · rcases lam_ends G k hb with hb | hb
      · exact TargetGeodesic.Dart.coe_fst_ne_snd t (ha.trans hb.symm)
      · exact h2 k hb
    · exact h1 k ha
  exact yType_of_incident G (Or.inl (sourceEnds_sourceEdge_fst φ.data t i))
    (Or.inr (sourceEnds_sourceEdge_snd φ.data t i)) hY hne

include G in
theorem yType_step {x x' : φ.target.V} (t : φ.target.edges)
    (ht : s((t : φ.target.V × φ.target.V).1, (t : φ.target.V × φ.target.V).2) = s(x, x'))
    (hx : ∀ k, x ≠ G.v k) (hx' : ∀ k, x' ≠ G.v k) (i : Fin (3 + 2))
    (hY : YType φ (φ.data.sourceEndpoint x i)) : YType φ (φ.data.sourceEndpoint x' i) := by
  rcases Sym2.eq_iff.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · subst h1 h2
    exact yType_step₀ G t i hx hx' hY
  · subst h1 h2
    have hne : ∀ k, φ.data.sourceEdge t i ≠ (G.leg k).1 := fun k h ↦ by
      have ht' : t = G.lam k := by
        rw [← G.leg_target k, ← h]
        rfl
      have ha : G.lam k ∈ GluingDatum.incidentEdges (t : φ.target.V × φ.target.V).1 := by
        rw [← ht']; exact Dichotomy.mem_incidentEdges_fst t
      have hb : G.lam k ∈ GluingDatum.incidentEdges (t : φ.target.V × φ.target.V).2 := by
        rw [← ht']; exact Dichotomy.mem_incidentEdges_snd t
      rcases lam_ends G k ha with ha | ha
      · rcases lam_ends G k hb with hb | hb
        · exact TargetGeodesic.Dart.coe_fst_ne_snd t (ha.trans hb.symm)
        · exact hx k hb
      · exact hx' k ha
    exact yType_of_incident G (Or.inr (sourceEnds_sourceEdge_snd φ.data t i))
      (Or.inl (sourceEnds_sourceEdge_fst φ.data t i)) hY hne

include G in
/-- **The sheet of the centre lies in `Y′` over every target vertex other than the leaves
`v k`**: it does at `φ(c)`, and it propagates along every target edge that is not an arm
(`yType_step`), while `T` minus the three leaves is connected. -/
theorem yType_ySheet (x : φ.target.V) (hx : ∀ k, x ≠ G.v k) :
    YType φ (φ.data.sourceEndpoint x (ySheet φ)) := by
  classical
  let P : φ.target.V → Prop := fun z ↦ YType φ (φ.data.sourceEndpoint z (ySheet φ))
  let c := (Dichotomy.centreSource (Frame.of φ)).1.1
  have hPc : P c := by
    show YType φ (φ.data.sourceEndpoint c (ySheet φ))
    have : φ.data.sourceEndpoint c (ySheet φ) = Dichotomy.centreSource (Frame.of φ) :=
      GluingDatum.sourceEndpoint_self _ _
    rw [this]
    exact yType_centre
  have hcv : ∀ k, c ≠ G.v k := G.centre_ne
  let S : Finset φ.target.V := Finset.univ.filter fun z ↦
    ((∀ k, z ≠ G.v k) → P z) ∧ ∀ k, z = G.v k → P (G.w k)
  have hmemS : ∀ z, z ∈ S ↔ ((∀ k, z ≠ G.v k) → P z) ∧ ∀ k, z = G.v k → P (G.w k) := fun z ↦ by
    simp [S]
  have hS : ∀ z, z ∈ S := by
    by_contra hall
    push Not at hall
    obtain ⟨z, hz⟩ := hall
    have hcS : c ∈ S := (hmemS c).mpr ⟨fun _ ↦ hPc, fun k h ↦ absurd h (hcv k)⟩
    obtain ⟨a, ha, b, hb, hab⟩ := φ.fullDim.targetConnected S ⟨c, z, hcS, hz⟩
    rw [← GluingTransport.card_edgeKey_fiber] at hab
    obtain ⟨⟨e, he⟩⟩ := Fintype.card_pos_iff.mp hab
    unfold GluingTransport.edgeKey at he
    have ha' := (hmemS a).mp ha
    have hab' : a ≠ b := fun h ↦ hb (h ▸ ha)
    have hea : e ∈ GluingDatum.incidentEdges a := by
      rcases Sym2.eq_iff.mp he with ⟨h, -⟩ | ⟨-, h⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩
    have heb : e ∈ GluingDatum.incidentEdges b := by
      rcases Sym2.eq_iff.mp he with ⟨-, h⟩ | ⟨h, -⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩
    -- at a leaf `v k` the edge is the arm, whose other end is `w k`
    have hleaf : ∀ {a' b' : φ.target.V} (k : Fin 3), e ∈ GluingDatum.incidentEdges a' →
        e ∈ GluingDatum.incidentEdges b' → a' ≠ b' → a' = G.v k → b' = G.w k := by
      intro a' b' k ha'' hb'' hne hak
      rw [hak] at ha''
      have hek := eq_lam_of_mem_v G ha''
      rw [hek] at hb''
      rcases lam_ends G k hb'' with h | h
      · exact h
      · exact absurd (hak.trans h.symm) hne
    apply hb
    refine (hmemS b).mpr ⟨fun hbv ↦ ?_, fun k hbk ↦ ?_⟩
    · by_cases hav : ∃ k, a = G.v k
      · obtain ⟨k, hk⟩ := hav
        rw [hleaf k hea heb hab' hk]
        exact ha'.2 k hk
      · push Not at hav
        exact yType_step G e he hav hbv _ (ha'.1 hav)
    · have haw := hleaf k heb hea (Ne.symm hab') hbk
      rw [← haw]
      exact ha'.1 (fun j h ↦ w_ne_v G k j (haw.symm.trans h))
  exact ((hmemS x).mp (hS x)).1 hx

include G in
/-- **The Y-sheet is a block of its own over every target vertex other than the leaves
`v k`**: its source vertex there lies in `Y′`, so it is a single sheet. -/
theorem ySheet_vertex (x : φ.target.V) (hx : ∀ k, x ≠ G.v k) (i : Fin (3 + 2)) :
    (φ.data.vertexPartition x).Rel i (ySheet φ) ↔ i = ySheet φ := by
  have h1 := blockCard_eq_one_of_yType G (yType_ySheet G x hx) hx
  set P := φ.data.vertexPartition x with hPdef
  have hb : P.blockCard (ySheet φ) = 1 := by
    have : P.blockCard (P.repr (ySheet φ)) = P.blockCard (ySheet φ) := by
      unfold SheetPartition.blockCard
      rw [SheetPartition.block_eq_of_rel _ (P.rel_repr_left _)]
    rw [← this]
    exact h1
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hb
  have hya : ySheet φ = a := Finset.mem_singleton.mp (ha ▸ P.self_mem_block _)
  constructor
  · intro h
    have hi : i ∈ P.block (ySheet φ) := (P.mem_block_iff _ _).mpr h.symm
    rw [ha, Finset.mem_singleton] at hi
    exact hi.trans hya.symm
  · rintro rfl
    rfl

include G in
theorem ySheet_edge (e : φ.target.edges) (he : ∀ k, e ≠ G.lam k) (i : Fin (3 + 2)) :
    (φ.data.edgePartition e).Rel i (ySheet φ) ↔ i = ySheet φ := by
  have h1 : ∀ k, (e : φ.target.V × φ.target.V).1 ≠ G.v k := fun k h ↦ by
    apply he k
    apply eq_lam_of_mem_v G
    rw [← h]
    exact Dichotomy.mem_incidentEdges_fst e
  constructor
  · intro h
    exact (ySheet_vertex G _ h1 i).mp ((φ.data.refines_left e).rel h)
  · rintro rfl
    rfl

/-! ### The hairpins -/

include G in
theorem markSource_eq (k : Fin 3) :
    TripodFrame.markSource (Frame.of φ) k = φ.data.sourceEndpoint (G.w k) (G.sheet k) := by
  have key : ∀ a : φ.target.V, φ.data.sourceEndpoint a (G.sheet k) =
      TripodFrame.markSource (Frame.of φ) k →
      TripodFrame.markSource (Frame.of φ) k = φ.data.sourceEndpoint (G.w k) (G.sheet k) := by
    intro a ha
    have haw : a = G.w k := by rw [← G.mark_target k, ← ha]; rfl
    rw [← ha, haw]
  rcases G.leg_incident k with h | h
  · exact key _ h
  · exact key _ h

include G in
/-- **The leg leaves its mark off the Y-sheet**: the Y-sheet vertex over `w k` lies in `Y′`,
and the mark does not. -/
theorem sheet_ne_ySheet (k : Fin 3) : G.sheet k ≠ ySheet φ := by
  intro h
  have hY := yType_ySheet G (G.w k) (fun j ↦ w_ne_v G k j)
  rw [← h, ← markSource_eq G k] at hY
  exact not_yType_mark k hY

include G in
/-- **The hairpin of leg `k` turns into the Y-sheet at the tip.** Along leg `k`, the edges in the
Y-sheet include the last one (at the centre, a single sheet) but not the first (at the mark,
`sheet_ne_ySheet`). At a consecutive pair where this changes, the common vertex is not off the
leaves (there the Y-sheet is a single sheet, so it is inherited); so it is the fold over a leaf,
which is `v k`, and both the Y-sheet and the sheet of the first edge meet it. -/
theorem tip_rel (k : Fin 3) : (φ.data.vertexPartition (G.v k)).Rel (G.sheet k) (ySheet φ) := by
  classical
  have hne := sheet_ne_ySheet G k
  let Q : NonDanglingEdge φ.data → Prop := fun g ↦
    φ.ident.row g.stablePath = legSlot p k →
      (φ.data.edgePartition g.1.1.1).Rel g.1.1.2 (ySheet φ)
  have hQ0 : Q (ClawShape.lastEdge (Frame.of φ) k) := by
    intro _
    have hInc := ClawShape.lastEdge_incident (Frame.of φ) k
    have hrel := ((incident_iff_target_mem_and_rel φ.data _ _).mp hInc).2
    have hc : ∀ j, (Dichotomy.centreSource (Frame.of φ)).1.1 ≠ G.v j := G.centre_ne
    have h' : (ClawShape.lastEdge (Frame.of φ) k).1.1.2 = ySheet φ :=
      (ySheet_vertex G _ hc _).mp hrel.symm
    show (φ.data.edgePartition _).repr _ = (φ.data.edgePartition _).repr _
    rw [h']
  have hQ1 : ¬ Q (G.leg k) := by
    intro h
    have h' := h (G.leg_row k)
    have h'' : (φ.data.edgePartition (G.lam k)).Rel (G.sheet k) (ySheet φ) := by
      have := G.leg_target k
      unfold GluedFacts.sheet
      rw [← this]
      exact h'
    exact hne ((arm_discrete G k _ _).mp h'')
  have hEqv : Relation.EqvGen (Consecutive φ.data) (ClawShape.lastEdge (Frame.of φ) k) (G.leg k) :=
    (stablePath_eq_iff _ _).mp (φ.ident.row.injective
      ((ClawShape.lastEdge_row (Frame.of φ) k).trans (G.leg_row k).symm))
  have hbd : ∃ f g, Consecutive φ.data f g ∧ Q f ∧ ¬ Q g := by
    by_contra hno
    push Not at hno
    exact hQ1 ((eqvGen_iff_of_closed hno hEqv).mp hQ0)
  obtain ⟨f, g, hfg, hQf, hQg⟩ := hbd
  have hgrow : φ.ident.row g.stablePath = legSlot p k := by
    by_contra h
    exact hQg fun h' ↦ absurd h' h
  have hfrow : φ.ident.row f.stablePath = legSlot p k := by
    rw [stablePath_eq_of_consecutive hfg]
    exact hgrow
  have hfy := hQf hfrow
  have hgy : ¬ (φ.data.edgePartition g.1.1.1).Rel g.1.1.2 (ySheet φ) := fun h ↦ hQg fun _ ↦ h
  obtain ⟨-, A, hfA, hgA, hA2⟩ := hfg
  have hfA' := (incident_iff_target_mem_and_rel φ.data f.1 A).mp hfA
  have hgA' := (incident_iff_target_mem_and_rel φ.data g.1 A).mp hgA
  have hAy : (φ.data.vertexPartition A.1.1).Rel A.1.2 (ySheet φ) := by
    have hfy' : (φ.data.vertexPartition A.1.1).Rel f.1.1.2 (ySheet φ) := by
      rcases (Finset.mem_filter.mp hfA'.1).2 with h | h
      · rw [← h]; exact (φ.data.refines_left _).rel hfy
      · rw [← h]; exact (φ.data.refines_right _).rel hfy
    exact hfA'.2.trans hfy'
  by_cases hAv : ∃ j, A.1.1 = G.v j
  · obtain ⟨j, hj⟩ := hAv
    have hft : f.1.1.1 = G.lam j := eq_lam_of_mem_v G (by rw [← hj]; exact hfA'.1)
    have hfk : f.1.1.1 = G.lam k :=
      legEdge_target_of_isLeafEdge G f hfrow (by rw [hft]; exact lam_isLeafEdge G j)
    have hjk : j = k := lam_injective G (hft.symm.trans hfk)
    subst hjk
    have hLeaf := v_isLeaf G j
    have hAfold : A = LeafFibre.coreVertex φ.fullDim hLeaf := by
      by_contra hne'
      have := LeafFacetNoReturn.nonDanglingValency_eq_zero_of_ne_fold φ.data φ.fullDim
        (LeafFibre.coreVertex φ.fullDim hLeaf) A (by rw [hj]; rfl) hLeaf
        (LeafFibre.nonDanglingValency_coreVertex φ.fullDim hLeaf) hne'
      omega
    have hlegA : Incident φ.data (G.leg j).1 A := by
      rw [hAfold]
      exact LeafFibre.incident_coreVertex_of_mem_leafSurvivors φ.fullDim hLeaf
        ((LeafFibre.mem_leafSurvivors hLeaf).mpr
          ⟨(G.leg j).2, (G.leg_target j).trans (lam_eq_leafEdge G j)⟩)
    have hσ := ((incident_iff_target_mem_and_rel φ.data _ A).mp hlegA).2
    rw [← hj]
    exact hσ.symm.trans hAy
  · push Not at hAv
    have hAsing := ySheet_vertex G A.1.1 hAv
    have hAeq : A.1.2 = ySheet φ := (hAsing _).mp hAy
    have hgA'' : (φ.data.vertexPartition A.1.1).Rel (ySheet φ) g.1.1.2 := by
      rw [← hAeq]; exact hgA'.2
    have hgy' : g.1.1.2 = ySheet φ := (hAsing _).mp hgA''.symm
    exact (hgy (by
      show (φ.data.edgePartition g.1.1.1).repr g.1.1.2 =
        (φ.data.edgePartition g.1.1.1).repr (ySheet φ)
      rw [hgy'])).elim

end YProof

-- The hypotheses are those of `exists_glueShape`; the proof below uses none of them.
set_option linter.unusedVariables false in
/-- **The centre's sheet is a block on its own over `T̂`** (§5.5, with the jump rule,
Lemma 4.1: `δ_Y = 1` on `T̂`): over every target vertex other than the three leaves, and over every
target edge other than the three arms, the sheet `y` of the centre is a singleton block. -/
theorem ySheet_singleton (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (φ : FibreMember (tripodCore core s) y (3 + 2)) (hφ : φ.Open) (hGlued : MemberIsGlued φ)
    (G : GluedFacts φ) :
    (∀ x, (∀ k, x ≠ G.v k) → ∀ i,
      (φ.data.vertexPartition x).Rel i (ySheet φ) ↔ i = ySheet φ) ∧
    (∀ e, (∀ k, e ≠ G.lam k) → ∀ i,
      (φ.data.edgePartition e).Rel i (ySheet φ) ↔ i = ySheet φ) :=
  ⟨fun x hx i ↦ YProof.ySheet_vertex G x hx i, fun e he i ↦ YProof.ySheet_edge G e he i⟩

-- The hypotheses are those of `exists_glueShape`; the proof below uses none of them.
set_option linter.unusedVariables false in
/-- **Each hairpin turns into the centre's sheet** (§5.5): leg `k` leaves its
mark in a sheet `σ k` other than `y`, and at the tip `v k` the sheets `σ k` and `y` are glued. -/
theorem hairpin_turn (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (φ : FibreMember (tripodCore core s) y (3 + 2)) (hφ : φ.Open) (hGlued : MemberIsGlued φ)
    (G : GluedFacts φ) (k : Fin 3) :
    G.sheet k ≠ ySheet φ ∧ (φ.data.vertexPartition (G.v k)).Rel (G.sheet k) (ySheet φ) :=
  ⟨YProof.sheet_ne_ySheet G k, YProof.tip_rel G k⟩

/-- **The tip glues exactly `σ k` to `y`**: over a leaf the only block with two sheets is the fold
(`LeafFibre.other_block_data`, `LeafFibre.blockCard_coreBlock`), and `σ k ∼ y` is one. -/
theorem tip_of_turn {φ : FibreMember (tripodCore core s) y (3 + 2)} (G : GluedFacts φ)
    (k : Fin 3) (hne : G.sheet k ≠ ySheet φ)
    (hrel : (φ.data.vertexPartition (G.v k)).Rel (G.sheet k) (ySheet φ)) (i j : Fin (3 + 2)) :
    (φ.data.vertexPartition (G.v k)).Rel i j ↔
      i = j ∨ (i = G.sheet k ∧ j = ySheet φ) ∨ (i = ySheet φ ∧ j = G.sheet k) := by
  classical
  set P := φ.data.vertexPartition (G.v k) with hP
  have hv : IsLeafVertex φ.target (G.v k) := Dichotomy.isLeafVertex_of_vertex_degree (G.v_leaf k)
  have hcardRepr : ∀ a, P.blockCard (P.repr a) = P.blockCard a := fun a ↦ by
    unfold SheetPartition.blockCard
    rw [SheetPartition.block_eq_of_rel _ (P.rel_repr_left a)]
  -- a block with two sheets is the fold
  have htwo : ∀ a b, P.Rel a b → a ≠ b → P.toBlock a = LeafFibre.coreBlock φ.fullDim hv := by
    intro a b hab hab'
    by_contra hc
    have h1 : P.blockCard (P.repr a) = 1 := (LeafFibre.other_block_data φ.fullDim hv hc).2.1
    have h2 : 1 < P.blockCard a := Finset.one_lt_card.mpr
      ⟨a, P.self_mem_block a, b, (P.mem_block_iff a b).mpr hab, hab'⟩
    rw [hcardRepr] at h1
    omega
  -- the block of `σ k` is `{σ k, y}`
  have hσ := htwo _ _ hrel hne
  have hcardσ : P.blockCard (G.sheet k) = 2 := by
    rw [← hcardRepr]
    have := LeafFibre.blockCard_coreBlock φ.fullDim hv
    rw [← hσ] at this
    exact this
  have hblock : P.block (G.sheet k) = {G.sheet k, ySheet φ} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact P.self_mem_block _
      · rw [Finset.mem_singleton.mp hx]
        exact (P.mem_block_iff _ _).mpr hrel
    · rw [Finset.card_pair hne]
      exact hcardσ.le
  constructor
  · intro h
    by_cases hij : i = j
    · exact Or.inl hij
    · right
      have hi : P.Rel (G.sheet k) i := by
        have := congrArg Subtype.val ((htwo _ _ h hij).trans hσ.symm)
        exact this.symm
      have hiM : i ∈ P.block (G.sheet k) := (P.mem_block_iff _ _).mpr hi
      have hjM : j ∈ P.block (G.sheet k) := (P.mem_block_iff _ _).mpr (hi.trans h)
      rw [hblock, Finset.mem_insert, Finset.mem_singleton] at hiM hjM
      rcases hiM with hi' | hi' <;> rcases hjM with hj' | hj'
      · exact absurd (hi'.trans hj'.symm) hij
      · exact Or.inl ⟨hi', hj'⟩
      · exact Or.inr ⟨hi', hj'⟩
      · exact absurd (hi'.trans hj'.symm) hij
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact hrel
    · exact hrel.symm

/-- **The tips** (§5.5): `σ k ≠ y`, and the only glued pair at `v k` is
`{σ k, y}`. -/
theorem tip_pair (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (φ : FibreMember (tripodCore core s) y (3 + 2)) (hφ : φ.Open) (hGlued : MemberIsGlued φ)
    (G : GluedFacts φ) (k : Fin 3) :
    G.sheet k ≠ ySheet φ ∧ ∀ i j, (φ.data.vertexPartition (G.v k)).Rel i j ↔
      i = j ∨ (i = G.sheet k ∧ j = ySheet φ) ∨ (i = ySheet φ ∧ j = G.sheet k) :=
  have h := hairpin_turn hcubic hconn hgenus hpos hlong φ hφ hGlued G k
  ⟨h.1, tip_of_turn G k h.1 h.2⟩

/-- **An open glued member at long legs has a Y-sheet** (§5.5, with the jump rule, Lemma 4.1,
and §4.8), from the three statements above. -/
theorem ySheet_shape (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (φ : FibreMember (tripodCore core s) y (3 + 2)) (hφ : φ.Open) (hGlued : MemberIsGlued φ)
    (G : GluedFacts φ) : YSheet G :=
  have hY := ySheet_singleton hcubic hconn hgenus hpos hlong φ hφ hGlued G
  have hT := tip_pair hcubic hconn hgenus hpos hlong φ hφ hGlued G
  ⟨fun k ↦ (hT k).1, hY.1, hY.2, arm_discrete G, fun k ↦ (hT k).2⟩

/-- **At the inner end of an arm every block is a passage** (§4.8): `w k` is
trivalent, so every block over it is unramified (`localRamification_eq_zero_of_trivalent_target`);
the discrete arm contributes the block's size, so each of the two other edges has exactly one
block inside it (`block_eq_of_refines_of_blockCountWithin_eq_one`). -/
theorem pass_of_arm {φ : FibreMember (tripodCore core s) y (3 + 2)} (G : GluedFacts φ)
    (harm : ∀ k i j, (φ.data.edgePartition (G.lam k)).Rel i j ↔ i = j) (k : Fin 3)
    (e : φ.target.edges) (he : e ∈ GluingDatum.incidentEdges (G.w k)) (hne : e ≠ G.lam k) :
    (φ.data.edgePartition e).SameBlocks (φ.data.vertexPartition (G.w k)) := by
  classical
  set P := φ.data.vertexPartition (G.w k) with hP
  set S := GluingDatum.incidentEdges (G.w k) with hSdef
  have hcard : S.card = 3 := by
    have := Dichotomy.card_incidentEdges_eq_vertex_degree φ.target (G.w k)
    rw [G.w_degree] at this
    exact_mod_cast this
  have hlam : G.lam k ∈ S := by
    have hk := G.lam_key k
    unfold GluingTransport.edgeKey at hk
    rcases Sym2.eq_iff.mp hk with ⟨h, -⟩ | ⟨-, h⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩
  -- the arm is literally discrete
  have hdisc : φ.data.edgePartition (G.lam k) = SheetPartition.discrete (3 + 2) := by
    apply SheetPartition.ext_repr
    funext i
    have h1 := (harm k _ _).mp ((φ.data.edgePartition (G.lam k)).rel_repr_left i)
    exact h1
  -- the count at one block
  have hcount : ∀ r : Fin (3 + 2), P.repr r = r →
      (φ.data.edgePartition e).blockCountWithin P r = 1 := by
    intro r hr
    have h0 := SlopesGeometric.localRamification_eq_zero_of_trivalent_target φ.data
      φ.fullDim.valid (G.w k) (φ.fullDim.changeMinimal _) hcard ⟨r, hr⟩
    unfold GluingDatum.localRamification at h0
    rw [← hSdef, hcard, ← Finset.add_sum_erase S _ hlam, hdisc,
      blockCountWithin_discrete] at h0
    have hS2 : (S.erase (G.lam k)).card = 2 := by rw [Finset.card_erase_of_mem hlam, hcard]
    have he' : e ∈ S.erase (G.lam k) := Finset.mem_erase.mpr ⟨hne, he⟩
    have hsplit := Finset.add_sum_erase (S.erase (G.lam k))
      (fun f ↦ ((φ.data.edgePartition f).blockCountWithin P r : ℤ)) he'
    have hrest : ((S.erase (G.lam k)).erase e).card • (1 : ℤ) ≤
        ∑ f ∈ (S.erase (G.lam k)).erase e, ((φ.data.edgePartition f).blockCountWithin P r : ℤ) :=
      Finset.card_nsmul_le_sum _ _ _ fun f _ ↦ by
        exact_mod_cast SheetPartition.blockCountWithin_pos _ _ _
    rw [Finset.card_erase_of_mem he', hS2] at hrest
    have hpos := SheetPartition.blockCountWithin_pos (φ.data.edgePartition e) P r
    have hrest' : (1 : ℤ) ≤ ∑ f ∈ (S.erase (G.lam k)).erase e,
        ((φ.data.edgePartition f).blockCountWithin P r : ℤ) := by simpa using hrest
    have : ((φ.data.edgePartition e).blockCountWithin P r : ℤ) = 1 := by
      have h0' := h0
      rw [← hsplit] at h0'
      push_cast at h0'
      linarith
    exact_mod_cast this
  have hrefine : (φ.data.edgePartition e).Refines P := by
    rcases (Finset.mem_filter.mp he).2 with h | h
    · rw [hP, ← h]; exact φ.data.refines_left e
    · rw [hP, ← h]; exact φ.data.refines_right e
  intro i j
  refine ⟨fun h ↦ hrefine.rel h, fun h ↦ ?_⟩
  set r := P.repr i with hr
  have hblock := SheetPartition.block_eq_of_refines_of_blockCountWithin_eq_one _ P hrefine r
    (hcount r (P.repr_idem i))
  have hi : i ∈ (φ.data.edgePartition e).block r := by
    rw [hblock, SheetPartition.mem_block_iff]
    exact P.rel_repr_left i
  have hj : j ∈ (φ.data.edgePartition e).block r := by
    rw [hblock, SheetPartition.mem_block_iff]
    exact (P.rel_repr_left i).trans h
  rw [SheetPartition.mem_block_iff] at hi hj
  exact hi.symm.trans hj

/-- **The sheet shape**, from the Y-sheet and `pass_of_arm`. -/
theorem sheetShape (hcubic : core.Cubic) (hconn : core.Connected) (hgenus : p + 1 - n = 6)
    (hpos : ∀ i, 0 < y i) (hlong : LongLegs s y)
    (φ : FibreMember (tripodCore core s) y (3 + 2)) (hφ : φ.Open) (hGlued : MemberIsGlued φ)
    (G : GluedFacts φ) : SheetShape G :=
  have hY := ySheet_shape hcubic hconn hgenus hpos hlong φ hφ hGlued G
  ⟨hY.sheet_ne, hY.vertex_y, hY.edge_y, hY.arm, hY.tip, pass_of_arm G hY.arm⟩

end Sheets

/-! ## 7. The construction -/

section Construction

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}

theorem mem_incidentEdges_edgeEquiv_symm {X Y : CFGraph} (τ : Utilities.CFGraphIso X Y)
    (e : Y.edges) (a : X.V) :
    (GluingTransport.edgeEquiv τ).symm e ∈ GluingDatum.incidentEdges a ↔
      e ∈ GluingDatum.incidentEdges (τ.vertexEquiv a) := by
  simp only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases GluingTransport.edgeEquiv_symm_ends τ e with h | h <;> rw [h] <;>
    simp only [Equiv.apply_eq_iff_eq]
  exact or_comm

/-- **The construction** (§5.5): from the sheet shape, the glued datum of
the old sheets over the un-refined, arm-less target, isomorphic to `φ.data`, with the marks, the
centre and the legs in place. -/
theorem exists_shape (φ : FibreMember (tripodCore core s) y (3 + 2)) (G : GluedFacts φ)
    (hS : SheetShape G) :
    ∃ (T : CFGraph.{0}) (D : GluingDatum T (2 + 2)) (π : Placement T (2 + 2)),
      ∃ Ξ : GeometricDatumIso (glueDatum D π) φ.data, ShapeLabels s D π φ.ident Ξ := by
  classical
  set yS : Fin (2 + 2 + 1) := ySheet φ with hyS
  let ρ : Equiv.Perm (Fin (2 + 2 + 1)) := Equiv.swap yS (Fin.last (2 + 2))
  have hρy : ρ yS = Fin.last (2 + 2) := Equiv.swap_apply_left _ _
  have hρl : ρ.symm (Fin.last (2 + 2)) = yS := by rw [Equiv.symm_apply_eq, hρy]
  have hρσ : ∀ k, ρ (G.sheet k) ≠ Fin.last (2 + 2) := fun k h ↦
    hS.sheet_ne k (ρ.injective (h.trans hρy.symm))
  let σ' : Fin 3 → Fin (2 + 2) := fun k ↦ (ρ (G.sheet k)).castPred (hρσ k)
  have hσ' : ∀ k, (σ' k).castSucc = ρ (G.sheet k) := fun k ↦ Fin.castSucc_castPred _ _
  have hvw : ∀ k, 0 < num_edges φ.target (G.w k) (G.v k) := by
    intro k
    rw [← GluingTransport.card_edgeKey_fiber]
    exact Fintype.card_pos_iff.mpr ⟨⟨G.lam k, G.lam_key k⟩⟩
  obtain ⟨T, π, τ, hsheet, hτw, hτv⟩ := OntoTarget.exists_targetShape φ.fullDim.targetConnected
    φ.fullDim.targetGenus G.v G.w G.v_leaf G.w_degree hvw G.w_injective σ'
  -- the target edges
  let τE := GluingTransport.edgeEquiv τ
  have hle6 : ∀ a b : π.T₆.V, num_edges π.T₆ a b ≤ 1 := fun a b ↦ by
    rw [← τ.symm.map_num_edges]
    exact IteratedContraction.num_edges_le_one_of_genus_zero_of_connected _
      φ.fullDim.targetConnected φ.fullDim.targetGenus _ _
  have hτlam : ∀ k, τE (G.lam k) = π.armEdge k := by
    intro k
    have h1 : GluingTransport.edgeKey π.T₆ (τE (G.lam k)) = s(π.markTarget k, π.tipTarget k) := by
      rw [GluingTransport.edgeEquiv_key]
      have := G.lam_key k
      unfold GluingTransport.edgeKey at this
      unfold GluingTransport.mappedEdgeKey
      rw [← hτw k, ← hτv k]
      rcases Sym2.eq_iff.mp this with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · rw [h₁, h₂]
      · rw [h₁, h₂, Sym2.eq_swap]
    have h2 : GluingTransport.edgeKey π.T₆ (π.armEdge k) = s(π.markTarget k, π.tipTarget k) := by
      unfold GluingTransport.edgeKey
      rw [π.armEdge_ends]
    have hsub : Subsingleton {e : π.T₆.edges //
        GluingTransport.edgeKey π.T₆ e = s(π.markTarget k, π.tipTarget k)} := by
      apply Fintype.card_le_one_iff_subsingleton.mp
      rw [GluingTransport.card_edgeKey_fiber]
      exact hle6 _ _
    exact congrArg Subtype.val (hsub.elim ⟨_, h1⟩ ⟨_, h2⟩)
  have hτlam' : ∀ k, τE.symm (π.armEdge k) = G.lam k := fun k ↦ by
    rw [← hτlam k, Equiv.symm_apply_apply]
  have hτv' : ∀ k, τ.vertexEquiv.symm (π.tipTarget k) = G.v k := fun k ↦ by
    rw [← hτv k, Equiv.symm_apply_apply]
  have hτw' : ∀ k, τ.vertexEquiv.symm (π.lift₃ (π.markVertex₃ k)) = G.w k := fun k ↦ by
    rw [← π.markTarget_eq_lift₃, ← hτw k, Equiv.symm_apply_apply]
  have hlift : ∀ (u : π.T₃.V) k, τ.vertexEquiv.symm (π.lift₃ u) ≠ G.v k := fun u k h ↦
    π.lift₃_ne_tipTarget u k (by rw [← hτv k, ← h, Equiv.apply_symm_apply])
  have hliftE : ∀ (e : π.T₃.edges) k, τE.symm (π.liftE₃ e) ≠ G.lam k := fun e k h ↦
    π.liftE₃_ne_armEdge e k (by rw [← hτlam k, ← h, Equiv.apply_symm_apply])
  -- `φ.data` on `π.T₆`, with the Y-sheet last
  let F₁ : GluingDatum π.T₆ (2 + 2 + 1) := GluingTransport.transport τ φ.data
  let Ξ₁ : GeometricDatumIso φ.data F₁ := GeometricDatumIso.ofTargetIso τ φ.data
  let F₂ : GluingDatum π.T₆ (2 + 2 + 1) := Transport.DatumIso.globalRelabelDatum F₁ ρ
  let Ξ₂ : GeometricDatumIso F₁ F₂ :=
    GeometricDatumIso.ofStrict (Transport.DatumIso.ofGlobalPerm F₁ ρ)
  have hF₂V : ∀ x, F₂.vertexPartition x =
      (φ.data.vertexPartition (τ.vertexEquiv.symm x)).relabel ρ := fun _ ↦ rfl
  have hF₂E : ∀ e, F₂.edgePartition e = (φ.data.edgePartition (τE.symm e)).relabel ρ :=
    fun _ ↦ rfl
  have hLV : ∀ u, LastSingleton (F₂.vertexPartition (π.lift₃ u)) := fun u ↦
    lastSingleton_relabel (hS.vertex_y _ (hlift u)) hρy
  have hLE : ∀ e, LastSingleton (F₂.edgePartition (π.liftE₃ e)) := fun e ↦
    lastSingleton_relabel (hS.edge_y _ (hliftE e)) hρy
  -- the old sheets over `T₃`, passages at the marks
  let E₃ := lastRestrict π (by norm_num : 0 < 2 + 2) F₂ hLV hLE
  have hPass : ∀ k, Passage E₃ (π.markVertex₃ k) := by
    intro k e he
    show (restrictLast (F₂.edgePartition (π.liftE₃ e))).SameBlocks
      (restrictLast (F₂.vertexPartition (π.lift₃ (π.markVertex₃ k))))
    apply restrictLast_sameBlocks (hLE e) (hLV _)
    rw [hF₂E, hF₂V]
    apply relabel_sameBlocks
    have hmem : τE.symm (π.liftE₃ e) ∈ GluingDatum.incidentEdges (G.w k) := by
      rw [mem_incidentEdges_edgeEquiv_symm, hτw k]
      exact (π.mem_incidentEdges_lift₃ _ _).mpr (Or.inl ⟨e, he, rfl⟩)
    rw [hτw' k]
    exact hS.pass k _ hmem (hliftE e k)
  -- un-refine at the three marks
  have P₃ : Passage E₃ (subdivFresh π.T₂ π.edge₂) := hPass 2
  let E₂ := unrefineDatum E₃ P₃
  have P₂ : Passage E₂ (subdivFresh π.T₁ π.edge₁) := unrefine_passage E₃ P₃ _ (hPass 1)
  let E₁ := unrefineDatum E₂ P₂
  have P₁ : Passage E₁ (subdivFresh T π.edge₀) :=
    unrefine_passage E₂ P₂ _ (unrefine_passage E₃ P₃ _ (hPass 0))
  let D : GluingDatum T (2 + 2) := unrefineDatum E₁ P₁
  have hR₁V := unrefine_vertex_sameBlocks E₁ P₁
  have hR₁E := unrefine_edge_sameBlocks E₁ P₁
  have hR₂V : ∀ v, ((refineDatum (refineDatum D π.edge₀) π.edge₁).vertexPartition v).SameBlocks
      (E₂.vertexPartition v) := fun v ↦
    (refine_sameBlocks_vertex hR₁V hR₁E π.edge₁ v).trans (unrefine_vertex_sameBlocks E₂ P₂ v)
  have hR₂E : ∀ e, ((refineDatum (refineDatum D π.edge₀) π.edge₁).edgePartition e).SameBlocks
      (E₂.edgePartition e) := fun e ↦
    (refine_sameBlocks_edge hR₁E π.edge₁ e).trans (unrefine_edge_sameBlocks E₂ P₂ e)
  have hR₃V : ∀ v, ((refine₃ D π).vertexPartition v).SameBlocks (E₃.vertexPartition v) := fun v ↦
    (refine_sameBlocks_vertex hR₂V hR₂E π.edge₂ v).trans (unrefine_vertex_sameBlocks E₃ P₃ v)
  have hR₃E : ∀ e, ((refine₃ D π).edgePartition e).SameBlocks (E₃.edgePartition e) := fun e ↦
    (refine_sameBlocks_edge hR₂E π.edge₂ e).trans (unrefine_edge_sameBlocks E₃ P₃ e)
  -- the glued datum has the blocks of `F₂`
  have hGV : ∀ x, ((glueDatum D π).vertexPartition x).SameBlocks (F₂.vertexPartition x) := by
    intro x
    rcases π.T₆_vertex_cases x with ⟨u, rfl⟩ | ⟨k, rfl⟩
    · rw [glueDatum_vertexPartition_lift₃, ← extendNew_restrictLast (hLV u)]
      exact extendNew_sameBlocks (hR₃V u)
    · rw [glueDatum_vertexPartition_tipTarget, hsheet]
      intro i j
      rw [pair_rel_iff, hF₂V, relabel_rel, hτv' k, hS.tip k, hσ' k]
      obtain ⟨i', rfl⟩ := ρ.surjective i
      obtain ⟨j', rfl⟩ := ρ.surjective j
      rw [← hρy]
      simp only [Equiv.symm_apply_apply, ρ.injective.eq_iff]
      have hne := hS.sheet_ne k
      by_cases hi : i' = yS <;> by_cases hj : j' = yS
      · simp [hi, hj]
      · simp only [hi, hj, if_true, if_false, ρ.injective.eq_iff]
        constructor
        · intro h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
        · rintro (h | ⟨h, -⟩ | ⟨-, h⟩)
          · exact absurd h.symm hj
          · exact absurd h (Ne.symm hne)
          · exact h.symm
      · simp only [hi, hj, if_true, if_false, ρ.injective.eq_iff]
        constructor
        · intro h; exact Or.inr (Or.inl ⟨h, rfl⟩)
        · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
          · exact h.elim
          · exact h
          · exact absurd h hi
      · simp only [hi, hj, if_false, ρ.injective.eq_iff]
        tauto
  have hGE : ∀ ε, ((glueDatum D π).edgePartition ε).SameBlocks (F₂.edgePartition ε) := by
    intro ε
    rcases π.T₆_edge_cases ε with ⟨e, rfl⟩ | ⟨k, rfl⟩
    · rw [glueDatum_edgePartition_liftE₃, ← extendNew_restrictLast (hLE e)]
      exact extendNew_sameBlocks (hR₃E e)
    · rw [glueDatum_edgePartition_armEdge]
      intro i j
      rw [SheetPartition.discrete_rel_iff, hF₂E, relabel_rel, hτlam' k, hS.arm,
        ρ.symm.injective.eq_iff]
  -- the isomorphism, and the labels
  let Ξ₃ := isoOfSameBlocks (glueDatum D π) F₂ hGV hGE
  let Ξ : GeometricDatumIso (glueDatum D π) φ.data := Ξ₃.trans (Ξ₂.symm.trans Ξ₁.symm)
  have e2 : ∀ x i, Ξ₂.symm.sourceVertexEquiv (F₂.sourceEndpoint x i) =
      F₁.sourceEndpoint x (ρ.symm i) := fun x i ↦ sourceEndpoint_map Ξ₂.symm x i
  have e1 : ∀ x i, Ξ₁.symm.sourceVertexEquiv (F₁.sourceEndpoint x i) =
      φ.data.sourceEndpoint (τ.vertexEquiv.symm x) i := fun x i ↦ sourceEndpoint_map Ξ₁.symm x i
  have e2E : ∀ e i, Ξ₂.symm.sourceEdgeEquiv (F₂.sourceEdge e i) =
      F₁.sourceEdge e (ρ.symm i) := fun e i ↦ sourceEdge_map Ξ₂.symm e i
  have e1E : ∀ e i, Ξ₁.symm.sourceEdgeEquiv (F₁.sourceEdge e i) =
      φ.data.sourceEdge (τE.symm e) i := fun e i ↦ sourceEdge_map Ξ₁.symm e i
  refine ⟨T, D, π, Ξ, ⟨fun k ↦ ?_, ?_, fun k ↦ ⟨G.leg k, ?_, G.leg_row k⟩⟩⟩
  · -- the marks
    have hM : (φ.ident.vertex.symm (tripodMark n k)).1 =
        φ.data.sourceEndpoint (G.w k) (G.sheet k) := by
      have key : ∀ a : φ.target.V, φ.data.sourceEndpoint a (G.sheet k) =
          TripodFrame.markSource (Frame.of φ) k →
          TripodFrame.markSource (Frame.of φ) k = φ.data.sourceEndpoint (G.w k) (G.sheet k) := by
        intro a ha
        have haw : a = G.w k := by rw [← G.mark_target k, ← ha]; rfl
        rw [← ha, haw]
      rcases G.leg_incident k with h | h
      · exact key _ h
      · exact key _ h
    show _ = Ξ₁.symm.sourceVertexEquiv (Ξ₂.symm.sourceVertexEquiv (Ξ₃.sourceVertexEquiv
      ((glueDatum D π).sourceEndpoint (π.markTarget k) (π.sheet k).castSucc)))
    rw [isoOfSameBlocks_sourceEndpoint, e2, e1, π.markTarget_eq_lift₃, hτw', hsheet, hσ',
      Equiv.symm_apply_apply, hM]
  · -- the centre
    set C := (φ.ident.vertex.symm (centre n)).1 with hCdef
    have hC : C = φ.data.sourceEndpoint C.1.1 yS := Subtype.ext (Prod.ext rfl C.2.symm)
    have hct : ∀ k, C.1.1 ≠ G.v k := G.centre_ne
    have hB : Ξ.sourceVertexEquiv
        ((glueDatum D π).sourceEndpoint (τ.vertexEquiv C.1.1) (Fin.last (2 + 2))) = C := by
      show Ξ₁.symm.sourceVertexEquiv (Ξ₂.symm.sourceVertexEquiv (Ξ₃.sourceVertexEquiv
        ((glueDatum D π).sourceEndpoint (τ.vertexEquiv C.1.1) (Fin.last (2 + 2))))) = C
      rw [isoOfSameBlocks_sourceEndpoint, e2, e1, Equiv.symm_apply_apply, hρl]
      exact hC.symm
    rw [← hB, Equiv.symm_apply_apply]
    show ((glueDatum D π).vertexPartition (τ.vertexEquiv C.1.1)).repr (Fin.last (2 + 2)) =
      Fin.last (2 + 2)
    rcases π.T₆_vertex_cases (τ.vertexEquiv C.1.1) with ⟨u, hu⟩ | ⟨k, hk⟩
    · rw [hu, glueDatum_vertexPartition_lift₃, SheetOps.extendNew_repr_last]
    · exact absurd (by rw [← hτv' k, ← hk, Equiv.symm_apply_apply]) (hct k)
  · -- the legs
    show (G.leg k).1 = Ξ₁.symm.sourceEdgeEquiv (Ξ₂.symm.sourceEdgeEquiv (Ξ₃.sourceEdgeEquiv
      ((glueDatum D π).sourceEdge (π.armEdge k) (π.sheet k).castSucc)))
    rw [isoOfSameBlocks_sourceEdge, e2E, e1E, hτlam' k, hsheet, hσ', Equiv.symm_apply_apply]
    refine Subtype.ext (Prod.ext (G.leg_target k) ?_)
    show (G.leg k).1.1.2 = (φ.data.edgePartition (G.lam k)).repr (G.leg k).1.1.2
    rw [← G.leg_target k]
    exact (G.leg k).1.2.symm

end Construction

/-! ## 8. Connectedness and the placement

The proof of `connected_nonDangling_of_shape` (§5.5: the source of the deleted datum is a
modification of the connected `G̃`). Throughout, `Ξ : glueDatum D π ≅ φ.data` carries the marks, the
centre and the legs (`ShapeLabels`).

* **The old sheets reach a mark** (`fromMark_of_connected`, pure gluing combinatorics): the glued
  source is connected, and the old sheets meet the rest of it only through the hairpins, so every
  vertex of `refine₃ D π` is joined in `refine₃ D π` to a mark.
* **The new sheet is in `Y′`** (`yType_lastSheet`): it contains the centre and is joined by
  new-sheet edges, none of which meets a mark; so a surviving G-edge of `φ` is an old edge
  (`exists_liftSE_of_isGSlot`). By the connected marked core (`iff_branch_of_gSlot`, the source
  form of `Dichotomy.iff_of_mem_gImage`) the three marks are joined in `refine₃ D π`
  (`reachable_marks`). Hence `refine₃ D π`, and so `D` (`connected_of_refineDatum`), is connected.
* **The marks are on the core** (`nonDangling_of_shape`): over a dangling edge of `D` a mark would
  have no surviving old edge, and glued valency one instead of three. -/

namespace ConnProof

variable {T : CFGraph} {d : ℕ}

/-- **Un-refining keeps the source connected**: send a fresh vertex to the first end of the
subdivided edge. -/
theorem connected_of_refineDatum (D : GluingDatum T d) (t : T.edges)
    (h : (refineDatum D t).Connected) : D.Connected := by
  classical
  let pv : (subdivTarget T t).V → T.V := Sum.elim id fun _ ↦ (t : T.V × T.V).1
  let g : (refineDatum D t).SourceVertex → D.SourceVertex := fun z ↦
    D.sourceEndpoint (pv z.1.1) z.1.2
  have hg : ∀ (x : (subdivTarget T t).V) (i : Fin d),
      g ((refineDatum D t).sourceEndpoint x i) = D.sourceEndpoint (pv x) i := by
    intro x i
    rcases x with w | ⟨⟩
    · exact sourceEndpoint_eq_of_rel D w ((D.vertexPartition w).rel_repr_left i)
    · exact sourceEndpoint_eq_of_rel D _
        ((D.refines_left t).rel ((D.edgePartition t).rel_repr_left i))
  have hreach := reachable_of_sourceEdges (refineDatum D t) (srcGraph D) g (fun ε i ↦ by
    rw [hg, hg]
    obtain ⟨o, rfl⟩ := (subdivOcc T t).surjective ε
    rcases o with _ | e
    · rw [subdivOcc_none]
      exact (adj_sourceEndpoint D t i).symm.reachable
    · by_cases het : e = t
      · subst het
        rw [subdivOcc_some_self]
        exact SimpleGraph.Reachable.refl _
      · rw [subdivOcc_some_of_ne T het]
        exact (adj_sourceEndpoint D e i).reachable) h
  let x₀ : D.SourceVertex := Classical.choice D.sourceGraph.instNonempty
  refine connected_of_reachable D x₀ fun x ↦ ?_
  have := hreach (Refine.oldSV D t x₀) (Refine.oldSV D t x)
  have h1 : ∀ y : D.SourceVertex, g (Refine.oldSV D t y) = y := fun y ↦
    GluingDatum.sourceEndpoint_self D y
  rwa [h1, h1] at this

section Reach

variable (D : GluingDatum T d) (π : Placement T d)

/-- Reached from a mark in the refined source. -/
def FromMark (z : (refine₃ D π).SourceVertex) : Prop :=
  ∃ k, (srcGraph (refine₃ D π)).Reachable (markR₃ D π k) z

theorem fromMark_iff_of_adj {a b : (refine₃ D π).SourceVertex}
    (h : (srcGraph (refine₃ D π)).Adj a b) : FromMark D π a ↔ FromMark D π b :=
  ⟨fun ⟨k, hk⟩ ↦ ⟨k, hk.trans h.reachable⟩, fun ⟨k, hk⟩ ↦ ⟨k, hk.trans h.symm.reachable⟩⟩

/-- The glued source vertices reached from a mark: the old ones reached in `refine₃ D π`, the new
sheet, the hairpin tips, and the other tips over a reached old vertex. -/
def GReach (Z : (glueDatum D π).SourceVertex) : Prop :=
  (∃ x, Z = oldVertex₃ D π x ∧ FromMark D π x) ∨ (∃ v, Z = newVertex D π v) ∨
    (∃ k, Z = (glueDatum D π).sourceEndpoint (π.tipTarget k) (π.sheet k).castSucc) ∨
    ∃ k j, Z = (glueDatum D π).sourceEndpoint (π.tipTarget k) j.castSucc ∧
      FromMark D π ((refine₃ D π).sourceEndpoint (π.markVertex₃ k) j)

theorem gReach_old (x : (refine₃ D π).SourceVertex) :
    GReach D π (oldVertex₃ D π x) ↔ FromMark D π x := by
  constructor
  · rintro (⟨x', h, hx'⟩ | ⟨v, h⟩ | ⟨k, h⟩ | ⟨k, j, h, -⟩)
    · rw [oldVertex₃_injective D π h]; exact hx'
    · exact absurd h (oldVertex₃_ne_newVertex D π x v)
    · exact absurd h (oldVertex₃_ne_tip D π x k _)
    · exact absurd h (oldVertex₃_ne_tip D π x k _)
  · intro h
    exact Or.inl ⟨x, rfl, h⟩

theorem gReach_new (v : π.T₃.V) : GReach D π (newVertex D π v) := Or.inr (Or.inl ⟨v, rfl⟩)

theorem gReach_tip_last (k : Fin 3) :
    GReach D π ((glueDatum D π).sourceEndpoint (π.tipTarget k) (Fin.last d)) :=
  Or.inr (Or.inr (Or.inl ⟨k, tip_last_eq D π k⟩))

theorem rel_of_tip_eq {k k' : Fin 3} {a b : Fin (d + 1)}
    (h : (glueDatum D π).sourceEndpoint (π.tipTarget k) a =
      (glueDatum D π).sourceEndpoint (π.tipTarget k') b) :
    k = k' ∧ (SheetOps.pair (π.sheet k).castSucc (Fin.last d)).Rel a b := by
  have hk : k = k' := by
    by_contra hk
    exact tip_ne_tip D π hk a b h
  subst hk
  refine ⟨rfl, ?_⟩
  have := congrArg (fun z : (glueDatum D π).SourceVertex ↦ z.1.2) h
  rw [← glueDatum_vertexPartition_tipTarget D π k]
  exact this

theorem gReach_tip (k : Fin 3) (j : Fin d) :
    GReach D π ((glueDatum D π).sourceEndpoint (π.tipTarget k) j.castSucc) ↔
      FromMark D π ((refine₃ D π).sourceEndpoint (π.markVertex₃ k) j) := by
  constructor
  · rintro (⟨x', h, -⟩ | ⟨v, h⟩ | ⟨k', h⟩ | ⟨k', j', h, hj'⟩)
    · exact absurd h.symm (oldVertex₃_ne_tip D π x' k _)
    · exact absurd h.symm (newVertex_ne_tip D π v k _)
    · obtain ⟨rfl, hrel⟩ := rel_of_tip_eq D π h
      rw [pair_rel_iff, if_neg (Fin.castSucc_lt_last j).ne,
        if_neg (Fin.castSucc_lt_last _).ne, Fin.castSucc_inj] at hrel
      rw [hrel]
      exact ⟨k, SimpleGraph.Reachable.refl _⟩
    · obtain ⟨rfl, hrel⟩ := rel_of_tip_eq D π h
      rw [pair_rel_iff, if_neg (Fin.castSucc_lt_last j).ne,
        if_neg (Fin.castSucc_lt_last _).ne, Fin.castSucc_inj] at hrel
      rw [hrel]
      exact hj'
  · intro h
    exact Or.inr (Or.inr (Or.inr ⟨k, j, rfl, h⟩))

/-- `GReach` does not separate the two ends of any source edge of the glued datum. -/
theorem gReach_iff_edge (e : π.T₆.edges) (i : Fin (d + 1)) :
    GReach D π ((glueDatum D π).sourceEndpoint (e : π.T₆.V × π.T₆.V).1 i) ↔
      GReach D π ((glueDatum D π).sourceEndpoint (e : π.T₆.V × π.T₆.V).2 i) := by
  rcases π.T₆_edge_cases e with ⟨ε, rfl⟩ | ⟨k, rfl⟩
  · rw [π.liftE₃_ends]
    induction i using Fin.lastCases with
    | last => exact ⟨fun _ ↦ gReach_new D π _, fun _ ↦ gReach_new D π _⟩
    | cast j =>
      rw [← oldVertex₃_sourceEndpoint, ← oldVertex₃_sourceEndpoint, gReach_old, gReach_old]
      exact fromMark_iff_of_adj D π (adj_sourceEndpoint (refine₃ D π) ε j)
  · rw [π.armEdge_ends]
    induction i using Fin.lastCases with
    | last => exact ⟨fun _ ↦ gReach_tip_last D π k, fun _ ↦ gReach_new D π _⟩
    | cast j =>
      rw [π.markTarget_eq_lift₃, ← oldVertex₃_sourceEndpoint, gReach_old, gReach_tip]

/-- **Every vertex of the refined source is reached from a mark**, when the glued source is
connected: the old sheets meet the rest of the glued source only through the hairpins. -/
theorem fromMark_of_connected (hN : (glueDatum D π).Connected) (x : (refine₃ D π).SourceVertex) :
    FromMark D π x := by
  have h := reachable_of_sourceEdges (glueDatum D π) (⊥ : SimpleGraph Prop) (GReach D π)
    (fun e i ↦ by
      rw [SimpleGraph.reachable_bot]
      exact propext (gReach_iff_edge D π e i)) hN
    (oldVertex₃ D π x) (newVertex D π (π.markVertex₃ 0))
  rw [SimpleGraph.reachable_bot] at h
  have h' : GReach D π (oldVertex₃ D π x) := by
    rw [h]; exact gReach_new D π _
  exact (gReach_old D π x).mp h'

end Reach

/-! ### Source predicates along the G-slots -/

section SourceCut

theorem iff_of_incident_of_iff_src {S : CFGraph} {k : ℕ} {E : GluingDatum S k}
    {R : E.SourceVertex → Prop} {f : E.SourceEdge}
    (hf : R (E.sourceEnds f).1 ↔ R (E.sourceEnds f).2)
    {X Y : E.SourceVertex} (hX : Incident E f X) (hY : Incident E f Y) : R X ↔ R Y := by
  rcases hX with rfl | rfl <;> rcases hY with rfl | rfl
  · exact Iff.rfl
  · exact hf
  · exact hf.symm
  · exact Iff.rfl

/-- **A source predicate is constant along a stable path none of whose edges it separates.** -/
theorem iff_of_stablePath_eq_src {S : CFGraph} {k : ℕ} {E : GluingDatum S k}
    {R : E.SourceVertex → Prop} {L : StablePath E}
    (hL : ∀ a : NonDanglingEdge E, a.stablePath = L →
      (R (E.sourceEnds a.1).1 ↔ R (E.sourceEnds a.1).2))
    {a b : NonDanglingEdge E} (ha : a.stablePath = L) (hb : b.stablePath = L)
    {X Y : E.SourceVertex} (hX : Incident E a.1 X) (hY : Incident E b.1 Y) : R X ↔ R Y := by
  have hClosed : ∀ first second : NonDanglingEdge E, Consecutive E first second →
      (first.stablePath = L ∧ R (E.sourceEnds first.1).1) →
      (second.stablePath = L ∧ R (E.sourceEnds second.1).1) := by
    rintro first second hCons ⟨hfL, hfR⟩
    have hsL : second.stablePath = L := (stablePath_eq_of_consecutive hCons).symm.trans hfL
    obtain ⟨-, M, hfM, hsM, -⟩ := hCons
    refine ⟨hsL, ?_⟩
    have h1 := iff_of_incident_of_iff_src (hL first hfL) (incident_left E first.1) hfM
    have h2 := iff_of_incident_of_iff_src (hL second hsL) hsM (incident_left E second.1)
    exact h2.mp (h1.mp hfR)
  have hEqv := (stablePath_eq_iff a b).mp (ha.trans hb.symm)
  have hab := eqvGen_iff_of_closed
    (property := fun e ↦ e.stablePath = L ∧ R (E.sourceEnds e.1).1) hClosed hEqv
  have hX' := iff_of_incident_of_iff_src (hL a ha) hX (incident_left E a.1)
  have hY' := iff_of_incident_of_iff_src (hL b hb) (incident_left E b.1) hY
  constructor
  · intro hRX
    exact hY'.mp ((hab.mp ⟨ha, hX'.mp hRX⟩).2)
  · intro hRY
    exact hX'.mpr ((hab.mpr ⟨hb, hY'.mpr hRY⟩).2)

variable {n p degree : ℕ} {core : Core n p} {s : MarkSlots p}

/-- **A source predicate that no G-edge separates is constant on the branch vertices of the
marked core** (the source form of `Dichotomy.iff_of_mem_gImage`; connected `G̃`). -/
theorem iff_branch_of_gSlot (hconn : core.Connected) (κ : Frame (tripodCore core s) degree)
    {R : κ.data.SourceVertex → Prop}
    (hR : ∀ a : NonDanglingEdge κ.data, IsGSlot (κ.ident.row a.stablePath) →
      (R (κ.data.sourceEnds a.1).1 ↔ R (κ.data.sourceEnds a.1).2))
    (v w : Fin (n + 1 + 1 + 1)) :
    R (κ.ident.vertex.symm v.castSucc).1 ↔ R (κ.ident.vertex.symm w.castSucc).1 := by
  classical
  let β : Fin (n + 1 + 1 + 1) → κ.data.SourceVertex := fun v ↦ (κ.ident.vertex.symm v.castSucc).1
  have hSlot : ∀ i : Fin (p + 1 + 1 + 1),
      R (β ((markedCore core s).tail i)) ↔ R (β ((markedCore core s).head i)) := by
    intro i
    obtain ⟨a, haX, ha⟩ := Dichotomy.exists_incident_of_end κ (Fin.castAdd 3 i)
      ((markedCore core s).tail i).castSucc (Or.inl (Dichotomy.tripodCore_tail_castAdd i))
    obtain ⟨b, hbY, hb⟩ := Dichotomy.exists_incident_of_end κ (Fin.castAdd 3 i)
      ((markedCore core s).head i).castSucc (Or.inr (Dichotomy.tripodCore_head_castAdd i))
    refine iff_of_stablePath_eq_src (L := κ.ident.row.symm (Fin.castAdd 3 i)) ?_ ha hb haX hbY
    intro c hc
    apply hR c
    rw [hc, Equiv.apply_symm_apply]
    show (Fin.castAdd 3 i).val < p + 1 + 1 + 1
    exact i.isLt
  by_contra hvw
  let S : Finset (Fin (n + 1 + 1 + 1)) := Finset.univ.filter fun u ↦ R (β u)
  have hmem : ∀ u, u ∈ S ↔ R (β u) := fun u ↦ by simp [S]
  have hS : ∃ v w : Fin (n + 1 + 1 + 1), v ∈ S ∧ w ∉ S := by
    by_cases hv : R (β v)
    · refine ⟨v, w, (hmem v).mpr hv, fun hw ↦ hvw ⟨fun _ ↦ (hmem w).mp hw, fun _ ↦ hv⟩⟩
    · refine ⟨w, v, (hmem w).mpr ?_, fun h ↦ hv ((hmem v).mp h)⟩
      by_contra hw
      exact hvw ⟨fun h ↦ absurd h hv, fun h ↦ absurd h hw⟩
  obtain ⟨i, hi⟩ := Dichotomy.markedCore_connected hconn S hS
  rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 ((hmem _).mpr ((hSlot i).mp ((hmem _).mp h1)))
  · exact h2 ((hmem _).mpr ((hSlot i).mpr ((hmem _).mp h1)))

end SourceCut

/-! ### The shape: the new sheet lies in `Y′` -/

section ShapeConn

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
variable {φ : FibreMember (tripodCore core s) y (3 + 2)}

/-- **`Y′` is closed along every edge that meets no mark.** -/
theorem yType_of_incident_of_not_mark {f : φ.data.SourceEdge} {A A' : φ.data.SourceVertex}
    (hA : Incident φ.data f A) (hA' : Incident φ.data f A') (hY : YProof.YType φ A)
    (hf : ∀ k, ¬ Incident φ.data f (TripodFrame.markSource (Frame.of φ) k)) :
    YProof.YType φ A' := by
  by_cases hAA : A = A'
  · rw [← hAA]; exact hY
  obtain ⟨X, hXpos, hXT, hXr⟩ := hY
  by_cases hD : IsDangling φ.data f
  · refine ⟨X, hXpos, hXT, ?_⟩
    have hEnds : φ.data.sourceEnds f = (A, A') ∨ φ.data.sourceEnds f = (A', A) := by
      rcases hA with h1 | h1 <;> rcases hA' with h2 | h2
      · exact absurd (h1.symm.trans h2) hAA
      · exact Or.inl (Prod.ext h1 h2)
      · exact Or.inr (Prod.ext h2 h1)
      · exact absurd (h1.symm.trans h2) hAA
    have hstep : PendantRetraction.DanglingStep A A' := ⟨f, hD, hEnds⟩
    rw [← hXr]
    exact (Quotient.sound (Relation.ReflTransGen.single hstep)).symm
  · have hApos := YProof.pos_of_incident ⟨f, hD⟩ hA
    have hA'pos := YProof.pos_of_incident ⟨f, hD⟩ hA'
    have hAX : A = X := PendantRetraction.surviving_vertex_unique hApos hXpos hXr
    subst hAX
    by_cases hT' : YProof.TripodSide φ A'
    · exact ⟨A', hA'pos, hT', rfl⟩
    · exfalso
      have hfG := hXT.not_isGSlot ⟨f, hD⟩ hA
      have hm : ∃ k, A' = TripodFrame.markSource (Frame.of φ) k := by
        by_contra h
        push Not at h
        exact hT' ⟨h, ⟨f, hD⟩, hA', hfG⟩
      obtain ⟨k, rfl⟩ := hm
      exact hf k hA'

/-- A surviving edge at a vertex of `Y′` is a leg edge. -/
theorem not_isGSlot_of_yType {A : φ.data.SourceVertex} (hA : YProof.YType φ A)
    (f : NonDanglingEdge φ.data) (hf : Incident φ.data f.1 A) :
    ¬ IsGSlot (φ.ident.row f.stablePath) := by
  obtain ⟨X, hXpos, hXT, hXr⟩ := hA
  have := PendantRetraction.surviving_vertex_unique (YProof.pos_of_incident f hf) hXpos hXr
  subst this
  exact hXT.not_isGSlot f hf

variable {T : CFGraph.{0}} {D : GluingDatum T (2 + 2)} {π : Placement T (2 + 2)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data)

include Ξ in
theorem glue_connected : (glueDatum D π).Connected := Ξ.symm.connected φ.fullDim.valid.1

theorem markSourceVertex_eq (k : Fin 3) :
    π.markSourceVertex D k = oldVertex₃ D π (markR₃ D π k) :=
  (oldVertex₃_sourceEndpoint D π _ _).symm

/-- In the new sheet every edge of the glued target carries a single sheet. -/
theorem sheet_sourceEdge_last (e : π.T₆.edges) :
    ((glueDatum D π).sourceEdge e (Fin.last (2 + 2))).1.2 = Fin.last (2 + 2) := by
  rcases π.T₆_edge_cases e with ⟨ε, rfl⟩ | ⟨k, rfl⟩
  · show ((glueDatum D π).edgePartition (π.liftE₃ ε)).repr (Fin.last (2 + 2)) = _
    rw [glueDatum_edgePartition_liftE₃, SheetOps.extendNew_repr_last]
  · show ((glueDatum D π).edgePartition (π.armEdge k)).repr (Fin.last (2 + 2)) = _
    rw [glueDatum_edgePartition_armEdge]
    rfl

theorem not_incident_last_oldVertex₃ (e : π.T₆.edges) (x : (refine₃ D π).SourceVertex) :
    ¬ Incident (glueDatum D π) ((glueDatum D π).sourceEdge e (Fin.last (2 + 2)))
      (oldVertex₃ D π x) := by
  rw [incident_oldVertex₃_iff, sheet_sourceEdge_last]
  rintro ⟨-, h⟩
  obtain ⟨i', h', -⟩ := (extendNew_rel_castSucc_iff _ _ _).mp h
  exact (Fin.castSucc_lt_last i').ne h'.symm

variable (hS : ShapeLabels s D π φ.ident Ξ)
include hS

/-- **The new sheet lies in `Y′`**: it contains the centre (`ShapeLabels.centre`), and it is
connected over the glued target by source edges in the new sheet, none of which meets a mark
(the marks are in old sheets, `ShapeLabels.mark`). -/
theorem yType_lastSheet (x : π.T₆.V) :
    YProof.YType φ (Ξ.sourceVertexEquiv ((glueDatum D π).sourceEndpoint x (Fin.last (2 + 2)))) := by
  have hT6 : graph_connected π.T₆ := Ξ.symm.targetConnected_map φ.fullDim.targetConnected
  let P : π.T₆.V → Prop := fun x ↦
    YProof.YType φ (Ξ.sourceVertexEquiv ((glueDatum D π).sourceEndpoint x (Fin.last (2 + 2))))
  have hstep : ∀ e : π.T₆.edges, ∀ {a b : π.T₆.V},
      (a = (e : π.T₆.V × π.T₆.V).1 ∧ b = (e : π.T₆.V × π.T₆.V).2 ∨
        a = (e : π.T₆.V × π.T₆.V).2 ∧ b = (e : π.T₆.V × π.T₆.V).1) → P a → P b := by
    intro e a b hab ha
    set f := (glueDatum D π).sourceEdge e (Fin.last (2 + 2))
    have h1 : Incident (glueDatum D π) f
        ((glueDatum D π).sourceEndpoint (e : π.T₆.V × π.T₆.V).1 (Fin.last (2 + 2))) :=
      Or.inl (sourceEnds_sourceEdge_fst _ e _)
    have h2 : Incident (glueDatum D π) f
        ((glueDatum D π).sourceEndpoint (e : π.T₆.V × π.T₆.V).2 (Fin.last (2 + 2))) :=
      Or.inr (sourceEnds_sourceEdge_snd _ e _)
    have hnm : ∀ k, ¬ Incident φ.data (Ξ.sourceEdgeEquiv f) (TripodFrame.markSource (Frame.of φ) k) := by
      intro k h
      have hm : TripodFrame.markSource (Frame.of φ) k =
          Ξ.sourceVertexEquiv (oldVertex₃ D π (markR₃ D π k)) := by
        rw [← markSourceVertex_eq]
        exact hS.mark k
      rw [hm, Ξ.incident_map_iff] at h
      exact not_incident_last_oldVertex₃ e _ h
    rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact yType_of_incident_of_not_mark ((Ξ.incident_map_iff _ _).mpr h1)
        ((Ξ.incident_map_iff _ _).mpr h2) ha hnm
    · exact yType_of_incident_of_not_mark ((Ξ.incident_map_iff _ _).mpr h2)
        ((Ξ.incident_map_iff _ _).mpr h1) ha hnm
  -- the centre
  set Z := Ξ.sourceVertexEquiv.symm (Dichotomy.centreSource (Frame.of φ)) with hZ
  have hZlast : Z.1.2 = Fin.last (2 + 2) := hS.centre
  have hP0 : P Z.1.1 := by
    show YProof.YType φ (Ξ.sourceVertexEquiv ((glueDatum D π).sourceEndpoint Z.1.1 (Fin.last (2 + 2))))
    have : (glueDatum D π).sourceEndpoint Z.1.1 (Fin.last (2 + 2)) = Z := by
      rw [← hZlast]
      exact GluingDatum.sourceEndpoint_self _ Z
    have hC : Ξ.sourceVertexEquiv Z = Dichotomy.centreSource (Frame.of φ) :=
      Equiv.apply_symm_apply _ _
    rw [this, hC]
    exact YProof.yType_centre
  have h := reachable_of_targetEdges (⊥ : SimpleGraph Prop) P (fun e ↦ by
    rw [SimpleGraph.reachable_bot]
    exact propext ⟨hstep e (Or.inl ⟨rfl, rfl⟩), hstep e (Or.inr ⟨rfl, rfl⟩)⟩) hT6 Z.1.1 x
  rw [SimpleGraph.reachable_bot] at h
  show P x
  rw [← h]
  exact hP0

/-- **A surviving G-edge of the member is an old edge of the glued datum**: a new-sheet edge or an
arm of a hairpin meets a vertex of the new sheet or a hairpin tip, both in `Y′`
(`yType_lastSheet`), and the other arms dangle. -/
theorem exists_liftSE_of_isGSlot (a : NonDanglingEdge φ.data)
    (ha : IsGSlot (φ.ident.row a.stablePath)) :
    ∃ x, Ξ.sourceEdgeEquiv (liftSE D π x) = a.1 := by
  have hN := glue_connected Ξ
  set yN := Ξ.sourceEdgeEquiv.symm a.1 with hyN
  have hya : Ξ.sourceEdgeEquiv yN = a.1 := Equiv.apply_symm_apply _ _
  -- an edge at a vertex in the new sheet or at a hairpin tip is not a G-edge
  have hY : ∀ x : π.T₆.V, Incident (glueDatum D π) yN
      ((glueDatum D π).sourceEndpoint x (Fin.last (2 + 2))) → False := by
    intro x hx
    have hx' := (Ξ.incident_map_iff _ _).mpr hx
    rw [hya] at hx'
    exact not_isGSlot_of_yType (yType_lastSheet Ξ hS x) a hx' ha
  rcases sourceEdge_cases_glue D π yN with ⟨x, hx⟩ | ⟨ε, hε⟩ | ⟨k, j, hkj⟩
  · exact ⟨x, by rw [← hx, hya]⟩
  · exfalso
    apply hY (π.lift₃ (ε : π.T₃.V × π.T₃.V).1)
    rw [hε]
    exact (incident_newSE_newVertex D π ε _).mpr (Dichotomy.mem_incidentEdges_fst ε)
  · exfalso
    by_cases h1 : j = (π.sheet k).castSucc
    · apply hY (π.tipTarget k)
      rw [tip_last_eq, hkj, h1]
      exact (incident_tip_iff D π k _ _).mpr ⟨rfl, by
        rw [armSheetEdge_sheet]; exact (SheetPartition.rel_iff _ _ _).mpr rfl⟩
    by_cases h2 : j = Fin.last (2 + 2)
    · apply hY (π.tipTarget k)
      rw [hkj, h2]
      exact (incident_tip_iff D π k _ _).mpr ⟨rfl, by
        rw [armSheetEdge_sheet]; exact (SheetPartition.rel_iff _ _ _).mpr rfl⟩
    have hD := isDangling_armSheetEdge D π hN k j h1 h2
    rw [← hkj] at hD
    have := (Ξ.isDangling_map_iff hN yN).mpr hD
    rw [hya] at this
    exact a.2 this

end ShapeConn

/-! ### The marks are joined through the old sheets, so `D` is connected -/

theorem reachable_of_incident {S : CFGraph} {k : ℕ} {E : GluingDatum S k} {x : E.SourceEdge}
    {a b : E.SourceVertex} (ha : Incident E x a) (hb : Incident E x b) :
    (srcGraph E).Reachable a b := by
  have hadj := adj_sourceEndpoint E x.1.1 x.1.2
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact SimpleGraph.Reachable.refl _
  · exact hadj.reachable
  · exact hadj.symm.reachable
  · exact SimpleGraph.Reachable.refl _

theorem old_of_incident_liftSE {T : CFGraph} {d : ℕ} {D : GluingDatum T d} {π : Placement T d}
    {x : (refine₃ D π).SourceEdge} {Z : (glueDatum D π).SourceVertex}
    (h : Incident (glueDatum D π) (liftSE D π x) Z) :
    ∃ z, Z = oldVertex₃ D π z ∧ Incident (refine₃ D π) x z := by
  rcases sourceVertex_cases_glue D π Z with ⟨z, rfl⟩ | ⟨v, rfl⟩ | ⟨k, j, rfl⟩
  · exact ⟨z, rfl, (incident_liftSE_oldVertex₃ D π x z).mp h⟩
  · exact absurd h (not_incident_liftSE_newVertex D π x v)
  · exact absurd h (not_incident_liftSE_tip D π x k j)

section ShapeConn₂

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}
variable {φ : FibreMember (tripodCore core s) y (3 + 2)}
variable {T : CFGraph.{0}} {D : GluingDatum T (2 + 2)} {π : Placement T (2 + 2)}
  (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ)
include hS

/-- **The three marks are joined in `refine₃ D π`** (§5.5: the source of the deleted datum
is a modification of the connected `G̃`): no G-edge of the member separates the old sheets reached
from mark `0` (`exists_liftSE_of_isGSlot`), so by the connected marked core they contain every mark.
-/ theorem reachable_marks (hconn : core.Connected) (k : Fin 3) :
    (srcGraph (refine₃ D π)).Reachable (markR₃ D π 0) (markR₃ D π k) := by
  let R : φ.data.SourceVertex → Prop := fun X ↦ ∃ z, Ξ.sourceVertexEquiv (oldVertex₃ D π z) = X ∧
    (srcGraph (refine₃ D π)).Reachable (markR₃ D π 0) z
  have hR : ∀ a : NonDanglingEdge (Frame.of φ).data,
      IsGSlot ((Frame.of φ).ident.row a.stablePath) →
      (R ((Frame.of φ).data.sourceEnds a.1).1 ↔ R ((Frame.of φ).data.sourceEnds a.1).2) := by
    intro a ha
    obtain ⟨x, hx⟩ := exists_liftSE_of_isGSlot Ξ hS a ha
    have hend : ∀ X, Incident φ.data a.1 X →
        ∃ z, Ξ.sourceVertexEquiv (oldVertex₃ D π z) = X ∧ Incident (refine₃ D π) x z := by
      intro X hX
      have hX' : Incident (glueDatum D π) (liftSE D π x) (Ξ.sourceVertexEquiv.symm X) := by
        rw [← Ξ.incident_map_iff, hx, Equiv.apply_symm_apply]
        exact hX
      obtain ⟨z, hz, hxz⟩ := old_of_incident_liftSE hX'
      exact ⟨z, by rw [← hz, Equiv.apply_symm_apply], hxz⟩
    obtain ⟨z₁, hz₁, hx₁⟩ := hend _ (incident_left _ a.1)
    obtain ⟨z₂, hz₂, hx₂⟩ := hend _ (incident_right _ a.1)
    have h12 := reachable_of_incident hx₁ hx₂
    constructor
    · rintro ⟨z, hz, hr⟩
      have hzz : z = z₁ :=
        oldVertex₃_injective D π (Ξ.sourceVertexEquiv.injective (hz.trans hz₁.symm))
      subst hzz
      exact ⟨z₂, hz₂, hr.trans h12⟩
    · rintro ⟨z, hz, hr⟩
      have hzz : z = z₂ :=
        oldVertex₃_injective D π (Ξ.sourceVertexEquiv.injective (hz.trans hz₂.symm))
      subst hzz
      exact ⟨z₁, hz₁, hr.trans h12.symm⟩
  have hmark : ∀ j, (φ.ident.vertex.symm (markVertex n j).castSucc).1 =
      Ξ.sourceVertexEquiv (oldVertex₃ D π (markR₃ D π j)) := by
    intro j
    rw [← markSourceVertex_eq]
    exact hS.mark j
  obtain ⟨z, hz, hr⟩ := (iff_branch_of_gSlot hconn (Frame.of φ) hR (markVertex n 0)
    (markVertex n k)).mp ⟨markR₃ D π 0, (hmark 0).symm, SimpleGraph.Reachable.refl _⟩
  have hzk : z = markR₃ D π k :=
    oldVertex₃_injective D π (Ξ.sourceVertexEquiv.injective (hz.trans (hmark k)))
  rw [← hzk]
  exact hr

/-- **`D` is connected**: `refine₃ D π` is (every vertex is reached from a mark,
`fromMark_of_connected`, and the marks are joined, `reachable_marks`), and un-refining keeps it
(`connected_of_refineDatum`). -/
theorem connected_of_shape (hconn : core.Connected) : D.Connected := by
  have hN := glue_connected Ξ
  have h3 : (refine₃ D π).Connected := by
    refine connected_of_reachable _ (markR₃ D π 0) fun z ↦ ?_
    obtain ⟨k, hk⟩ := fromMark_of_connected D π hN z
    exact (reachable_marks Ξ hS hconn k).trans hk
  exact connected_of_refineDatum _ _ (connected_of_refineDatum _ _ (connected_of_refineDatum _ _ h3))

/-! ### The marks lie on the core of `D` -/

theorem nonDanglingValency_mark_glue (k : Fin 3) :
    nonDanglingValency (glueDatum D π) (oldVertex₃ D π (markR₃ D π k)) = 3 := by
  have hN := glue_connected Ξ
  have h := Ξ.nonDanglingValency_map hN (π.markSourceVertex D k)
  rw [← hS.mark k, markSourceVertex_eq] at h
  have h3 : 3 ≤ nonDanglingValency φ.data (TripodFrame.markSource (Frame.of φ) k) :=
    Dichotomy.three_le_markSource (Frame.of φ) k
  have h3' := φ.fullDim.trivalent (TripodFrame.markSource (Frame.of φ) k)
  have h' : nonDanglingValency φ.data (TripodFrame.markSource (Frame.of φ) k) =
      nonDanglingValency (glueDatum D π) (oldVertex₃ D π (markR₃ D π k)) := h
  omega

/-- The surviving arms of the glued datum are the two arms of each hairpin: the arm in the sheet
of the mark lies on a leg (`ShapeLabels.leg`), so the hairpin tip, of surviving valency other than
one, keeps the arm in the new sheet too. -/
theorem hairpinShaped_glue : HairpinShaped D π (fun y ↦ ¬ IsDangling (glueDatum D π) y) := by
  classical
  have hN := glue_connected Ξ
  have hσ : ∀ k, ¬ IsDangling (glueDatum D π) (armSheetEdge D π k (π.sheet k).castSucc) := by
    intro k hd
    obtain ⟨e', he', -⟩ := hS.leg k
    have h := (Ξ.isDangling_map_iff hN _).mpr hd
    have he'' : e'.1 = Ξ.sourceEdgeEquiv (armSheetEdge D π k (π.sheet k).castSucc) := he'
    rw [← he''] at h
    exact e'.2 h
  intro k j
  constructor
  · intro h
    by_contra hj
    push Not at hj
    exact h (isDangling_armSheetEdge D π hN k j hj.1 hj.2)
  · rintro (rfl | rfl)
    · exact hσ k
    · intro hd
      apply DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hN
        ((glueDatum D π).sourceEndpoint (π.tipTarget k) (π.sheet k).castSucc)
      unfold nonDanglingValency
      rw [Finset.card_eq_one]
      refine ⟨armSheetEdge D π k (π.sheet k).castSucc, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hnd, hinc⟩
        obtain ⟨hx1, -⟩ := (incident_tip_iff D π k _ x).mp hinc
        rw [eq_armSheetEdge D π x hx1] at hnd ⊢
        by_cases h1 : x.1.2 = (π.sheet k).castSucc
        · rw [h1]
        by_cases h2 : x.1.2 = Fin.last (2 + 2)
        · rw [h2] at hnd
          exact absurd hd hnd
        exact absurd (isDangling_armSheetEdge D π hN k _ h1 h2) hnd
      · rintro rfl
        exact ⟨hσ k, (incident_tip_iff D π k _ _).mpr ⟨rfl, by
          rw [armSheetEdge_sheet]; exact (SheetPartition.rel_iff _ _ _).mpr rfl⟩⟩

/-- **A surviving old edge of the glued datum survives in `refine₃ D π`** (the witness lemma: at
a mark the glued valency three is two old edges and the hairpin). -/
theorem not_isDangling_refine₃_of_glue {x : (refine₃ D π).SourceEdge}
    (hx : ¬ IsDangling (glueDatum D π) (liftSE D π x)) : ¬ IsDangling (refine₃ D π) x := by
  classical
  have hN := glue_connected Ξ
  have hND := hairpinShaped_glue Ξ hS
  refine not_isDangling_of_witness _ (fun x' ↦ ¬ IsDangling (glueDatum D π) (liftSE D π x'))
    (fun x₀ ↦ ?_) hx
  have hc := wCount_glue_oldVertex₃ D π hND x₀
  rw [← nonDanglingValency_eq_wCount] at hc
  by_cases hm : ∃ k, x₀ = markR₃ D π k
  · obtain ⟨k, rfl⟩ := hm
    rw [sum_mark_eq_one, nonDanglingValency_mark_glue Ξ hS k] at hc
    omega
  · push Not at hm
    rw [sum_mark_eq_zero D π hm, add_zero] at hc
    rw [← hc]
    exact DraismaVargas.LocalCases.NonDanglingValency.nonDanglingValency_ne_one _ hN _

omit hS in
/-- A mark over a dangling edge of `D` has surviving valency zero in `refine₃ D π`. -/
theorem nonDanglingValency_markR₃_eq_zero (hD : D.Connected) (k : Fin 3)
    (h : IsDangling D (D.sourceEdge (π.parentEdge k) (π.sheet k))) :
    nonDanglingValency (refine₃ D π) (markR₃ D π k) = 0 := by
  have h₁ := π.refine₁_connected D hD
  have h₂ := π.refine₂_connected D hD
  match k, h with
  | 0, h =>
    show nonDanglingValency (refine₃ D π) ((refine₃ D π).sourceEndpoint
      (subdivOld _ _ (subdivOld _ _ (subdivFresh T π.edge₀))) (π.sheet 0)) = 0
    rw [Refine.nonDanglingValency_sourceEndpoint_old _ _ h₂,
      Refine.nonDanglingValency_sourceEndpoint_old _ _ h₁,
      Refine.nonDanglingValency_sourceEndpoint_fresh _ _ hD,
      if_pos (show IsDangling D (D.sourceEdge π.edge₀ (π.sheet 0)) from h)]
  | 1, h =>
    show nonDanglingValency (refine₃ D π) ((refine₃ D π).sourceEndpoint
      (subdivOld _ _ (subdivFresh π.T₁ π.edge₁)) (π.sheet 1)) = 0
    rw [Refine.nonDanglingValency_sourceEndpoint_old _ _ h₂,
      Refine.nonDanglingValency_sourceEndpoint_fresh _ _ h₁, if_pos]
    rw [Refine.isDangling_sourceEdge _ _ hD]
    exact h
  | 2, h =>
    show nonDanglingValency (refine₃ D π) ((refine₃ D π).sourceEndpoint
      (subdivFresh π.T₂ π.edge₂) (π.sheet 2)) = 0
    rw [Refine.nonDanglingValency_sourceEndpoint_fresh _ _ h₂, if_pos]
    rw [Refine.isDangling_sourceEdge _ _ h₁, Refine.isDangling_sourceEdge _ _ hD]
    exact h

/-- **The marks lie on the core of `D`**: over a dangling edge, mark `k` would have no surviving
old edge in `refine₃ D π` (`nonDanglingValency_markR₃_eq_zero`), hence none in the glued datum
(`not_isDangling_refine₃_of_glue`), and glued valency one, not three. -/
theorem nonDangling_of_shape (hD : D.Connected) : π.NonDangling D := by
  classical
  intro k hk
  have hND := hairpinShaped_glue Ξ hS
  have h0 := nonDanglingValency_markR₃_eq_zero hD k hk
  have hc := wCount_glue_oldVertex₃ D π hND (markR₃ D π k)
  rw [← nonDanglingValency_eq_wCount, sum_mark_eq_one, nonDanglingValency_mark_glue Ξ hS k] at hc
  have hle : wCount (refine₃ D π) (fun x' ↦ ¬ IsDangling (glueDatum D π) (liftSE D π x'))
      (markR₃ D π k) ≤ nonDanglingValency (refine₃ D π) (markR₃ D π k) := by
    rw [nonDanglingValency_eq_wCount]
    exact wCount_le_of_imp _ _ fun x' _ h ↦ not_isDangling_refine₃_of_glue Ξ hS h
  omega

end ShapeConn₂

end ConnProof

/-! ### The statement -/

section Placement

variable {n p : ℕ} {core : Core n p} {s : MarkSlots p} {y : Fin (p + 1 + 1 + 1 + 3) → ℚ}

/-- **A shape is connected and non-dangling** (§5.5: the source of the deleted datum is a
modification of the connected `G̃`): if `Ξ : glueDatum D π ≅ φ.data` carries the marks, the centre
and the legs, then `D` is connected and the marks lie on its core. -/
theorem connected_nonDangling_of_shape (hconn : core.Connected) {T : CFGraph.{0}}
    {D : GluingDatum T (2 + 2)} {π : Placement T (2 + 2)}
    (φ : FibreMember (tripodCore core s) y (3 + 2))
    (Ξ : GeometricDatumIso (glueDatum D π) φ.data) (hS : ShapeLabels s D π φ.ident Ξ) :
    D.Connected ∧ π.NonDangling D := by
  have hD := ConnProof.connected_of_shape Ξ hS hconn
  exact ⟨hD, ConnProof.nonDangling_of_shape Ξ hS hD⟩

end Placement

end Onto

end GenusSixExistence.Tripod.Gluing

end
