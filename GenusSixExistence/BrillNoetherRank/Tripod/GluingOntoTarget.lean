module

public import GenusSixExistence.BrillNoetherRank.Tripod.Gluing
public import DraismaVargas.Infrastructure.GraphContraction
public import DraismaVargas.Infrastructure.IteratedContraction
public import DraismaVargas.LocalCases.IncomingTargetExpansion

@[expose] public section

/-!
# The target of a glued member is a glued target

The target half of `GluingOnto.exists_glueShape`. Prose proof:
`Research/genus-six-brill-noether-rank.md`, §5.5 (The bijection, the onto step: delete the new
sheet and the arms, and erase the three vertices `t_j`, which are then divalent); section numbers in
this file refer to that note. A target tree `X` with three leaves `v k`, joined to three distinct
trivalent vertices `w k`, is isomorphic, as a `CFGraph`, to the glued target `π.T₆` of a tree `T`
at a placement `π`, with `w k` the image of mark `k` and `v k` the tip of its arm
(`exists_targetShape`).

The tree `T` is made by six contractions (`GraphContraction.contract`): delete the leaves `v 2`,
`v 1`, `v 0` (each a contraction of its leaf edge), then erase `w 2`, `w 1`, `w 0`, which are then
divalent (each a contraction of one of its two edges). Each contraction is undone by a
`leafTarget` or a `subdivTarget` (`unleafIso`, `unsubdivIso`), and these are functorial in graph
isomorphisms (`leafMap`, `subdivMap`); both are read on the edge multiplicities
(`leaf_num_edges_*`, `subdiv_num_edges_*`). An isomorphism of `CFGraph`s is a vertex bijection
preserving `num_edges`, and its edge bijection is `GluingTransport.edgeEquiv`.
-/

open DraismaVargas.Infrastructure

noncomputable section

namespace GenusSixExistence.Tripod.Gluing

namespace OntoTarget

open TargetExpansion GraphContraction
open Utilities (CFGraphIso)


/-! ## 1. Multiplicities in an expanded target -/

theorem num_edges_eq_card_univ (A : CFGraph) (x y : A.V) :
    num_edges A x y = Multiset.card ((Finset.univ : Finset A.edges).val.filter
      fun e : A.edges ↦ (e : A.V × A.V) = (x, y) ∨ (e : A.V × A.V) = (y, x)) := by
  unfold num_edges
  conv_lhs => rw [← Multiset.map_univ_coe A.edges]
  rw [Multiset.filter_map, Multiset.card_map]
  rfl

theorem num_edges_graph (A : CFGraph) (w : A.V) (r : A.edges → Bool) (X Y : Vertex A) :
    num_edges (TargetExpansion.graph A w r) X Y =
      (if newEnds A w = (X, Y) ∨ newEnds A w = (Y, X) then 1 else 0) +
        Multiset.card ((enumeratedEdges A).filter fun e ↦
          oldEnds A w r e = (X, Y) ∨ oldEnds A w r e = (Y, X)) :=
  card_filter_expandedEdges A w r (fun e ↦ e = (X, Y) ∨ e = (Y, X))

theorem leaf_num_edges_old (A : CFGraph) (u x y : A.V) :
    num_edges (leafTarget A u) (Sum.inl x) (Sum.inl y) = num_edges A x y := by
  unfold leafTarget
  rw [num_edges_graph, ite_eq_right (by simp [newEnds, oldVertex, freshVertex]), zero_add,
    num_edges_eq_card_univ]
  congr 1
  apply Multiset.filter_congr
  intro e _
  simp [oldEnds, expandedEndpoint, oldVertex, Prod.ext_iff]

theorem leaf_num_edges_tip (A : CFGraph) (u x : A.V) :
    num_edges (leafTarget A u) (Sum.inl x) (Sum.inr ()) = if x = u then 1 else 0 := by
  unfold leafTarget
  rw [num_edges_graph]
  have h0 : (enumeratedEdges A).filter (fun e ↦
      oldEnds A u (fun _ ↦ false) e = ((Sum.inl x : Vertex A), (Sum.inr () : Vertex A)) ∨
        oldEnds A u (fun _ ↦ false) e = ((Sum.inr () : Vertex A), (Sum.inl x : Vertex A))) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro e _
    simp [oldEnds, expandedEndpoint, oldVertex, Prod.ext_iff]
  rw [h0, Multiset.card_zero, add_zero]
  by_cases h : x = u
  · subst h; simp [newEnds, oldVertex, freshVertex]
  · simp [newEnds, oldVertex, freshVertex, h, Ne.symm h]

theorem num_edges_self (G : CFGraph) (x : G.V) : num_edges G x x = 0 :=
  num_edges_self_zero G x

theorem leaf_num_edges_tip' (A : CFGraph) (u x : A.V) :
    num_edges (leafTarget A u) (Sum.inr ()) (Sum.inl x) = if x = u then 1 else 0 :=
  (num_edges_symmetric _ _ _).trans (leaf_num_edges_tip A u x)

theorem leaf_num_edges_tip_tip (A : CFGraph) (u : A.V) :
    num_edges (leafTarget A u) (Sum.inr ()) (Sum.inr ()) = 0 :=
  num_edges_self _ _

/-- The fresh vertex of `subdivTarget A t` sits between the two ends of `t`. -/
theorem subdiv_oldEnds_self (A : CFGraph) (t : A.edges) :
    oldEnds A (t : A.V × A.V).2 (subdivRight A t) t =
      (Sum.inl (t : A.V × A.V).1, Sum.inr ()) := by
  have hne := fst_ne_snd t
  simp only [oldEnds, expandedEndpoint, subdivRight, decide_true, ite_true, ite_eq_right hne]
  rfl

theorem subdiv_oldEnds_ne (A : CFGraph) {t e : A.edges} (h : e ≠ t) :
    oldEnds A (t : A.V × A.V).2 (subdivRight A t) e =
      (Sum.inl (e : A.V × A.V).1, Sum.inl (e : A.V × A.V).2) := by
  simp only [oldEnds, expandedEndpoint, subdivRight, h, decide_false, Bool.false_eq_true, ite_false]
  rfl

theorem subdiv_num_edges_old (A : CFGraph) (t : A.edges) (x y : A.V) :
    num_edges (subdivTarget A t) (Sum.inl x) (Sum.inl y) +
        (if (t : A.V × A.V) = (x, y) ∨ (t : A.V × A.V) = (y, x) then 1 else 0) =
      num_edges A x y := by
  classical
  unfold subdivTarget
  rw [num_edges_graph, ite_eq_right (by simp [newEnds, oldVertex, freshVertex]), zero_add,
    num_edges_eq_card_univ]
  set P : A.edges → Prop := fun e ↦ (e : A.V × A.V) = (x, y) ∨ (e : A.V × A.V) = (y, x) with hP
  have hfil : (enumeratedEdges A).filter (fun e ↦
      oldEnds A (t : A.V × A.V).2 (subdivRight A t) e =
          ((Sum.inl x : Vertex A), (Sum.inl y : Vertex A)) ∨
        oldEnds A (t : A.V × A.V).2 (subdivRight A t) e =
          ((Sum.inl y : Vertex A), (Sum.inl x : Vertex A))) =
      (Finset.univ.filter fun e ↦ P e ∧ e ≠ t).val := by
    rw [Finset.filter_val]
    apply Multiset.filter_congr
    intro e _
    by_cases he : e = t
    · subst he
      rw [subdiv_oldEnds_self]
      simp
    · rw [subdiv_oldEnds_ne A he]
      simp [hP, he, Prod.ext_iff]
  rw [hfil]
  change (Finset.univ.filter fun e ↦ P e ∧ e ≠ t).card + _ = (Finset.univ.filter P).card
  have hsplit : (Finset.univ.filter fun e ↦ P e ∧ e ≠ t) = (Finset.univ.filter P).erase t := by
    ext e
    simp [and_comm]
  rw [hsplit]
  by_cases ht : P t
  · rw [ite_eq_left ht, Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩)]
  · rw [ite_eq_right ht, add_zero, Finset.erase_eq_of_notMem (by simp [ht])]

theorem subdiv_num_edges_fresh (A : CFGraph) (t : A.edges) (x : A.V) :
    num_edges (subdivTarget A t) (Sum.inl x) (Sum.inr ()) =
      (if x = (t : A.V × A.V).2 then 1 else 0) + (if x = (t : A.V × A.V).1 then 1 else 0) := by
  classical
  unfold subdivTarget
  rw [num_edges_graph]
  congr 1
  · by_cases h : x = (t : A.V × A.V).2
    · subst h; simp [newEnds, oldVertex, freshVertex]
    · simp [newEnds, oldVertex, freshVertex, h, Ne.symm h]
  · have hfil : (enumeratedEdges A).filter (fun e ↦
        oldEnds A (t : A.V × A.V).2 (subdivRight A t) e =
            ((Sum.inl x : Vertex A), (Sum.inr () : Vertex A)) ∨
          oldEnds A (t : A.V × A.V).2 (subdivRight A t) e =
            ((Sum.inr () : Vertex A), (Sum.inl x : Vertex A))) =
        (Finset.univ.filter fun e ↦ e = t ∧ x = (t : A.V × A.V).1).val := by
      rw [Finset.filter_val]
      apply Multiset.filter_congr
      intro e _
      by_cases he : e = t
      · subst he
        rw [subdiv_oldEnds_self]
        simp [eq_comm]
      · rw [subdiv_oldEnds_ne A he]
        simp [he]
    rw [hfil]
    change (Finset.univ.filter fun e ↦ e = t ∧ x = (t : A.V × A.V).1).card = _
    by_cases h : x = (t : A.V × A.V).1
    · rw [ite_eq_left h]
      simp only [h, and_true]
      exact Finset.card_eq_one.mpr ⟨t, by ext e; simp⟩
    · rw [ite_eq_right h]
      simp [h]

theorem subdiv_num_edges_fresh' (A : CFGraph) (t : A.edges) (x : A.V) :
    num_edges (subdivTarget A t) (Sum.inr ()) (Sum.inl x) =
      (if x = (t : A.V × A.V).2 then 1 else 0) + (if x = (t : A.V × A.V).1 then 1 else 0) :=
  (num_edges_symmetric _ _ _).trans (subdiv_num_edges_fresh A t x)

/-! ## 2. Functoriality -/

/-- Symmetric form of a multiplicity. -/
theorem num_edges_comm (G : CFGraph) (x y : G.V) : num_edges G x y = num_edges G y x :=
  num_edges_symmetric G x y

/-- **Attaching a leaf is functorial** in graph isomorphisms. -/
def leafMap {A B : CFGraph} (ι : CFGraphIso A B) (u : A.V) (u' : B.V)
    (h : ι.vertexEquiv u = u') : CFGraphIso (leafTarget A u) (leafTarget B u') where
  vertexEquiv := (Equiv.sumCongr ι.vertexEquiv (Equiv.refl Unit) : A.V ⊕ Unit ≃ B.V ⊕ Unit)
  map_num_edges := by
    rintro (x | ⟨⟩) (y | ⟨⟩)
    · change num_edges (leafTarget B u') (Sum.inl (ι.vertexEquiv x)) (Sum.inl (ι.vertexEquiv y)) =
        num_edges (leafTarget A u) (Sum.inl x) (Sum.inl y)
      rw [leaf_num_edges_old, leaf_num_edges_old, ι.map_num_edges]
    · change num_edges (leafTarget B u') (Sum.inl (ι.vertexEquiv x)) (Sum.inr ()) =
        num_edges (leafTarget A u) (Sum.inl x) (Sum.inr ())
      rw [leaf_num_edges_tip, leaf_num_edges_tip, ← h]
      simp only [Equiv.apply_eq_iff_eq]
    · change num_edges (leafTarget B u') (Sum.inr ()) (Sum.inl (ι.vertexEquiv y)) =
        num_edges (leafTarget A u) (Sum.inr ()) (Sum.inl y)
      rw [leaf_num_edges_tip', leaf_num_edges_tip', ← h]
      simp only [Equiv.apply_eq_iff_eq]
    · exact (leaf_num_edges_tip_tip _ _).trans (leaf_num_edges_tip_tip _ _).symm

theorem leafMap_inl {A B : CFGraph} (ι : CFGraphIso A B) (u : A.V) (u' : B.V)
    (h : ι.vertexEquiv u = u') (x : A.V) :
    (leafMap ι u u' h).vertexEquiv (Sum.inl x) = Sum.inl (ι.vertexEquiv x) := rfl

theorem leafMap_inr {A B : CFGraph} (ι : CFGraphIso A B) (u : A.V) (u' : B.V)
    (h : ι.vertexEquiv u = u') :
    (leafMap ι u u' h).vertexEquiv (Sum.inr ()) = Sum.inr () := rfl

/-- **Subdividing an edge is functorial** in graph isomorphisms, for corresponding edges. -/
def subdivMap {A B : CFGraph} (ι : CFGraphIso A B) (t : A.edges) (t' : B.edges)
    (h : (t' : B.V × B.V) = (ι.vertexEquiv (t : A.V × A.V).1, ι.vertexEquiv (t : A.V × A.V).2) ∨
      (t' : B.V × B.V) = (ι.vertexEquiv (t : A.V × A.V).2, ι.vertexEquiv (t : A.V × A.V).1)) :
    CFGraphIso (subdivTarget A t) (subdivTarget B t') where
  vertexEquiv := (Equiv.sumCongr ι.vertexEquiv (Equiv.refl Unit) : A.V ⊕ Unit ≃ B.V ⊕ Unit)
  map_num_edges := by
    have hkey : ∀ x y : A.V, ((t' : B.V × B.V) = (ι.vertexEquiv x, ι.vertexEquiv y) ∨
        (t' : B.V × B.V) = (ι.vertexEquiv y, ι.vertexEquiv x)) ↔
        ((t : A.V × A.V) = (x, y) ∨ (t : A.V × A.V) = (y, x)) := by
      intro x y
      rcases h with h | h
      · rw [h]; simp only [Equiv.apply_eq_iff_eq, Prod.ext_iff]
      · rw [h]; simp only [Equiv.apply_eq_iff_eq, Prod.ext_iff]; tauto
    have hfresh : ∀ x : A.V,
        ((if ι.vertexEquiv x = (t' : B.V × B.V).2 then 1 else 0) +
          (if ι.vertexEquiv x = (t' : B.V × B.V).1 then 1 else 0) : ℕ) =
        (if x = (t : A.V × A.V).2 then 1 else 0) + (if x = (t : A.V × A.V).1 then 1 else 0) := by
      intro x
      rcases h with h | h <;> rw [h] <;> simp only [Equiv.apply_eq_iff_eq]
      exact add_comm _ _
    rintro (x | ⟨⟩) (y | ⟨⟩)
    · change num_edges (subdivTarget B t') (Sum.inl (ι.vertexEquiv x)) (Sum.inl (ι.vertexEquiv y)) =
        num_edges (subdivTarget A t) (Sum.inl x) (Sum.inl y)
      have h1 := subdiv_num_edges_old B t' (ι.vertexEquiv x) (ι.vertexEquiv y)
      have h2 := subdiv_num_edges_old A t x y
      rw [ι.map_num_edges] at h1
      have h3 : (if (t' : B.V × B.V) = (ι.vertexEquiv x, ι.vertexEquiv y) ∨
          (t' : B.V × B.V) = (ι.vertexEquiv y, ι.vertexEquiv x) then 1 else 0 : ℕ) =
          if (t : A.V × A.V) = (x, y) ∨ (t : A.V × A.V) = (y, x) then 1 else 0 := by
        simp only [hkey]
      omega
    · change num_edges (subdivTarget B t') (Sum.inl (ι.vertexEquiv x)) (Sum.inr ()) =
        num_edges (subdivTarget A t) (Sum.inl x) (Sum.inr ())
      rw [subdiv_num_edges_fresh, subdiv_num_edges_fresh, hfresh]
    · change num_edges (subdivTarget B t') (Sum.inr ()) (Sum.inl (ι.vertexEquiv y)) =
        num_edges (subdivTarget A t) (Sum.inr ()) (Sum.inl y)
      rw [subdiv_num_edges_fresh', subdiv_num_edges_fresh', hfresh]
    · exact (num_edges_self _ _).trans (num_edges_self _ _).symm

theorem subdivMap_inl {A B : CFGraph} (ι : CFGraphIso A B) (t : A.edges) (t' : B.edges) (h)
    (x : A.V) : (subdivMap ι t t' h).vertexEquiv (Sum.inl x) = Sum.inl (ι.vertexEquiv x) := rfl

theorem subdivMap_inr {A B : CFGraph} (ι : CFGraphIso A B) (t : A.edges) (t' : B.edges) (h) :
    (subdivMap ι t t' h).vertexEquiv (Sum.inr ()) = Sum.inr () := rfl


/-! ## 3. Undoing a contraction -/

/-- A vertex function supported on `S` sums, over `S`, to the valency: it vanishes off `S`. -/
theorem num_edges_eq_zero_of_sum {A : CFGraph} {v : A.V} (S : Finset A.V)
    (hS : ∑ x ∈ S, (num_edges A v x : ℤ) = vertex_degree A v) {z : A.V} (hz : z ∉ S) :
    num_edges A v z = 0 := by
  classical
  have hsplit := Finset.sum_sdiff (Finset.subset_univ S) (f := fun x ↦ (num_edges A v x : ℤ))
  have h0 : ∑ x ∈ Finset.univ \ S, (num_edges A v x : ℤ) = 0 := by
    unfold vertex_degree at hS
    linarith
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ by positivity)).mp h0 z (by simp [hz])
  exact_mod_cast this

/-! The vertices of a contraction, named through two functions whose declared types are the
vertex types themselves (`(contract A hab h1).V` is not reducibly a subtype, and terms such as
`⟨p, hp⟩` or `z.1` at that type defeat `rw`). -/

section ContractVertex

variable (A : CFGraph) {a b : A.V} (hab : a ≠ b) (h1 : num_edges A a b = 1)

/-- A vertex other than `b`, in the contraction. -/
def cv (p : A.V) (hp : p ≠ b) : (contract A hab h1).V := ⟨p, hp⟩

/-- A vertex of the contraction, in `A`. -/
def cval (z : (contract A hab h1).V) : A.V := z.1

@[simp] theorem cval_cv (p : A.V) (hp : p ≠ b) : cval A hab h1 (cv A hab h1 p hp) = p := rfl

theorem cval_ne (z : (contract A hab h1).V) : cval A hab h1 z ≠ b := z.2

theorem cval_injective : Function.Injective (cval A hab h1) := fun _ _ h ↦ Subtype.ext h

theorem cv_eq_iff (p : A.V) (hp : p ≠ b) (z : (contract A hab h1).V) :
    cv A hab h1 p hp = z ↔ p = cval A hab h1 z :=
  ⟨fun h ↦ h ▸ rfl, fun h ↦ cval_injective A hab h1 (by rw [cval_cv, h])⟩

theorem eq_cv_of_cval (z : (contract A hab h1).V) {p : A.V} (h : cval A hab h1 z = p) :
    z = cv A hab h1 p (h ▸ cval_ne A hab h1 z) :=
  cval_injective A hab h1 (by rw [cval_cv, h])

end ContractVertex

/-- **Contracting a pendant edge** keeps every multiplicity of the remaining vertices. -/
theorem num_edges_contract_pendant (A : CFGraph) {a b : A.V} (hab : a ≠ b)
    (h1 : num_edges A a b = 1) (hpend : ∀ z, z ≠ a → num_edges A b z = 0)
    (z w : (contract A hab h1).V) :
    num_edges (contract A hab h1) z w = num_edges A (cval A hab h1 z) (cval A hab h1 w) := by
  by_cases hza : cval A hab h1 z = a <;> by_cases hwa : cval A hab h1 w = a
  · have e : z = w := cval_injective A hab h1 (hza.trans hwa.symm)
    rw [e, num_edges_self_zero, num_edges_self_zero]
  · have e : z = cv A hab h1 a hab := eq_cv_of_cval A hab h1 z hza
    have hm : num_edges (contract A hab h1) (cv A hab h1 a hab) w =
        num_edges A a (cval A hab h1 w) + num_edges A b (cval A hab h1 w) :=
      num_edges_contract_merge A hab h1 (cval_ne A hab h1 w) hwa
    rw [e, hm, hpend _ hwa, add_zero, cval_cv]
  · have e : w = cv A hab h1 a hab := eq_cv_of_cval A hab h1 w hwa
    have hm : num_edges (contract A hab h1) (cv A hab h1 a hab) z =
        num_edges A a (cval A hab h1 z) + num_edges A b (cval A hab h1 z) :=
      num_edges_contract_merge A hab h1 (cval_ne A hab h1 z) hza
    rw [e, num_edges_symmetric, hm, hpend _ hza, add_zero, cval_cv, num_edges_symmetric]
  · exact num_edges_contract_of_ne A hab h1 (cval_ne A hab h1 z) (cval_ne A hab h1 w) hza hwa

/-- **Contracting one edge at a divalent vertex** `b` (neighbours `a` and `x`): the edge `bx`
becomes an edge `ax`. -/
theorem num_edges_contract_bivalent (A : CFGraph) {a b x : A.V} (hab : a ≠ b)
    (h1 : num_edges A a b = 1) (hxa : x ≠ a)
    (hbx : ∀ z, z ≠ a → num_edges A b z = if z = x then 1 else 0)
    (z w : (contract A hab h1).V) :
    num_edges (contract A hab h1) z w =
      num_edges A (cval A hab h1 z) (cval A hab h1 w) +
        if s(cval A hab h1 z, cval A hab h1 w) = s(a, x) then 1 else 0 := by
  by_cases hza : cval A hab h1 z = a <;> by_cases hwa : cval A hab h1 w = a
  · have e : z = w := cval_injective A hab h1 (hza.trans hwa.symm)
    rw [e, num_edges_self_zero, num_edges_self_zero, ite_eq_right]
    rw [Sym2.eq_iff]
    rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact hxa (h.symm.trans (e ▸ hza))
    · exact hxa (h.symm.trans (e ▸ hza))
  · have e : z = cv A hab h1 a hab := eq_cv_of_cval A hab h1 z hza
    have hm : num_edges (contract A hab h1) (cv A hab h1 a hab) w =
        num_edges A a (cval A hab h1 w) + num_edges A b (cval A hab h1 w) :=
      num_edges_contract_merge A hab h1 (cval_ne A hab h1 w) hwa
    rw [e, hm, hbx _ hwa, cval_cv]
    congr 1
    by_cases hwx : cval A hab h1 w = x
    · simp [hwx]
    · rw [ite_eq_right hwx, ite_eq_right]
      rw [Sym2.eq_iff]
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact hwx h
      · exact hwa h
  · have e : w = cv A hab h1 a hab := eq_cv_of_cval A hab h1 w hwa
    have hm : num_edges (contract A hab h1) (cv A hab h1 a hab) z =
        num_edges A a (cval A hab h1 z) + num_edges A b (cval A hab h1 z) :=
      num_edges_contract_merge A hab h1 (cval_ne A hab h1 z) hza
    rw [e, num_edges_symmetric, hm, hbx _ hza, cval_cv, num_edges_symmetric A a]
    congr 1
    by_cases hzx : cval A hab h1 z = x
    · simp [hzx, Sym2.eq_swap]
    · rw [ite_eq_right hzx, ite_eq_right]
      rw [Sym2.eq_iff]
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hza h
      · exact hzx h
  · have hne : num_edges (contract A hab h1) z w =
        num_edges A (cval A hab h1 z) (cval A hab h1 w) :=
      num_edges_contract_of_ne A hab h1 (cval_ne A hab h1 z) (cval_ne A hab h1 w) hza hwa
    rw [hne, ite_eq_right, add_zero]
    rw [Sym2.eq_iff]
    rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact hza h
    · exact hwa h

/-- **A pendant edge contracted and re-attached as a leaf** is the graph it came from. -/
def unleafIso (A : CFGraph) {u v : A.V} (huv : u ≠ v) (h1 : num_edges A u v = 1)
    (hpend : ∀ z, z ≠ u → num_edges A v z = 0) :
    CFGraphIso (leafTarget (contract A huv h1) (cv A huv h1 u huv)) A where
  vertexEquiv := DraismaVargas.LocalCases.IncomingTargetExpansion.vertexEquiv huv h1
  map_num_edges := by
    have hv : ∀ z : (contract A huv h1).V, num_edges A (cval A huv h1 z) v =
        num_edges (leafTarget (contract A huv h1) (cv A huv h1 u huv)) (Sum.inl z)
          (Sum.inr ()) := by
      intro z
      have hT := leaf_num_edges_tip (contract A huv h1) (cv A huv h1 u huv) z
      by_cases hzu : cval A huv h1 z = u
      · rw [ite_eq_left (eq_cv_of_cval A huv h1 z hzu)] at hT
        rw [hT, hzu, h1]
      · rw [ite_eq_right (fun h ↦ hzu (by rw [h, cval_cv]))] at hT
        rw [hT, num_edges_symmetric, hpend _ hzu]
    rintro (z | ⟨⟩) (w | ⟨⟩)
    · exact ((leaf_num_edges_old _ _ z w).trans
        (num_edges_contract_pendant A huv h1 hpend z w)).symm
    · exact hv z
    · exact (num_edges_symmetric A v (cval A huv h1 w)).trans
        ((hv w).trans (num_edges_symmetric _ _ _))
    · exact (num_edges_self_zero A v).trans (leaf_num_edges_tip_tip _ _).symm

theorem unleafIso_inl (A : CFGraph) {u v : A.V} (huv : u ≠ v) (h1 : num_edges A u v = 1)
    (hpend : ∀ z, z ≠ u → num_edges A v z = 0) (z : (contract A huv h1).V) :
    (unleafIso A huv h1 hpend).vertexEquiv (Sum.inl z) = cval A huv h1 z := rfl

theorem unleafIso_inr (A : CFGraph) {u v : A.V} (huv : u ≠ v) (h1 : num_edges A u v = 1)
    (hpend : ∀ z, z ≠ u → num_edges A v z = 0) :
    (unleafIso A huv h1 hpend).vertexEquiv (Sum.inr ()) = v := rfl

theorem exists_bivalentEdge (A : CFGraph) {a b x : A.V} (hab : a ≠ b)
    (h1 : num_edges A a b = 1) (hxa : x ≠ a) (hxb : x ≠ b)
    (hbx : ∀ z, z ≠ a → num_edges A b z = if z = x then 1 else 0) :
    ∃ t : (contract A hab h1).edges,
      GluingTransport.edgeKey _ t = s(cv A hab h1 x hxb, cv A hab h1 a hab) := by
  have hnum : 0 < num_edges (contract A hab h1) (cv A hab h1 x hxb) (cv A hab h1 a hab) := by
    rw [num_edges_contract_bivalent A hab h1 hxa hbx, cval_cv, cval_cv, ite_eq_left Sym2.eq_swap]
    omega
  have hcard := GluingTransport.card_edgeKey_fiber (contract A hab h1) (cv A hab h1 x hxb)
    (cv A hab h1 a hab)
  obtain ⟨⟨t, ht⟩⟩ := Fintype.card_pos_iff.mp (lt_of_lt_of_eq hnum hcard.symm)
  exact ⟨t, ht⟩

/-- The edge of the contracted graph that the erased divalent vertex subdivides. -/
def bivalentEdge (A : CFGraph) {a b x : A.V} (hab : a ≠ b)
    (h1 : num_edges A a b = 1) (hxa : x ≠ a) (hxb : x ≠ b)
    (hbx : ∀ z, z ≠ a → num_edges A b z = if z = x then 1 else 0) :
    (contract A hab h1).edges :=
  Classical.choose (exists_bivalentEdge A hab h1 hxa hxb hbx)

theorem bivalentEdge_ends (A : CFGraph) {a b x : A.V} (hab : a ≠ b)
    (h1 : num_edges A a b = 1) (hxa : x ≠ a) (hxb : x ≠ b)
    (hbx : ∀ z, z ≠ a → num_edges A b z = if z = x then 1 else 0) :
    ((bivalentEdge A hab h1 hxa hxb hbx : (contract A hab h1).edges) :
        (contract A hab h1).V × (contract A hab h1).V) = (cv A hab h1 x hxb, cv A hab h1 a hab) ∨
      ((bivalentEdge A hab h1 hxa hxb hbx : (contract A hab h1).edges) :
        (contract A hab h1).V × (contract A hab h1).V) =
          (cv A hab h1 a hab, cv A hab h1 x hxb) := by
  have ht := Classical.choose_spec (exists_bivalentEdge A hab h1 hxa hxb hbx)
  unfold GluingTransport.edgeKey at ht
  rcases Sym2.eq_iff.mp ht with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact Or.inl (Prod.ext h₁ h₂)
  · exact Or.inr (Prod.ext h₁ h₂)

/-- **An edge at a divalent vertex contracted and the merged edge re-subdivided** is the graph it
came from. -/
def unsubdivIso (A : CFGraph) {a b x : A.V} (hab : a ≠ b)
    (h1 : num_edges A a b = 1) (hxa : x ≠ a) (hxb : x ≠ b)
    (hbx : ∀ z, z ≠ a → num_edges A b z = if z = x then 1 else 0) :
    CFGraphIso (subdivTarget (contract A hab h1) (bivalentEdge A hab h1 hxa hxb hbx)) A where
  vertexEquiv := DraismaVargas.LocalCases.IncomingTargetExpansion.vertexEquiv hab h1
  map_num_edges := by
    set t := bivalentEdge A hab h1 hxa hxb hbx with htdef
    have hends := bivalentEdge_ends A hab h1 hxa hxb hbx
    rw [← htdef] at hends
    have hhit : ∀ z w : (contract A hab h1).V,
        ((t : (contract A hab h1).V × (contract A hab h1).V) = (z, w) ∨
          (t : (contract A hab h1).V × (contract A hab h1).V) = (w, z)) ↔
        s(cval A hab h1 z, cval A hab h1 w) = s(a, x) := by
      intro z w
      rw [Sym2.eq_iff]
      rcases hends with h | h <;> rw [h] <;> simp only [Prod.mk.injEq, cv_eq_iff] <;>
        constructor <;> intro h' <;> rcases h' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
        first
        | exact Or.inl ⟨h₁.symm, h₂.symm⟩ | exact Or.inr ⟨h₁.symm, h₂.symm⟩
        | exact Or.inl ⟨h₂.symm, h₁.symm⟩ | exact Or.inr ⟨h₂.symm, h₁.symm⟩
    have hb : ∀ z : (contract A hab h1).V, num_edges A (cval A hab h1 z) b =
        (if z = (t : (contract A hab h1).V × (contract A hab h1).V).2 then 1 else 0) +
        (if z = (t : (contract A hab h1).V × (contract A hab h1).V).1 then 1 else 0) := by
      intro z
      rw [num_edges_symmetric]
      have hval : num_edges A b (cval A hab h1 z) =
          (if z = cv A hab h1 a hab then 1 else 0) + if z = cv A hab h1 x hxb then 1 else 0 := by
        by_cases hza : cval A hab h1 z = a
        · rw [ite_eq_left (eq_cv_of_cval A hab h1 z hza), ite_eq_right (fun h ↦ hxa (by
            rw [h, cval_cv] at hza; exact hza)), hza, num_edges_symmetric, h1]
        · rw [ite_eq_right (fun h ↦ hza (by rw [h, cval_cv])), hbx _ hza, zero_add]
          by_cases hzx : cval A hab h1 z = x
          · rw [ite_eq_left hzx, ite_eq_left (eq_cv_of_cval A hab h1 z hzx)]
          · rw [ite_eq_right hzx, ite_eq_right (fun h ↦ hzx (by rw [h, cval_cv]))]
      rw [hval]
      rcases hends with h | h <;> rw [h]
      exact add_comm _ _
    rintro (z | ⟨⟩) (w | ⟨⟩)
    · have hL := subdiv_num_edges_old (contract A hab h1) t z w
      have hB := num_edges_contract_bivalent A hab h1 hxa hbx z w
      have hI := if_congr (hhit z w) (rfl : (1 : ℕ) = 1) (rfl : (0 : ℕ) = 0)
      exact (Nat.add_right_cancel (hL.trans (hB.trans (by rw [hI]; rfl)))).symm
    · exact (hb z).trans (subdiv_num_edges_fresh _ _ _).symm
    · exact ((num_edges_symmetric A b (cval A hab h1 w)).trans (hb w)).trans
        (subdiv_num_edges_fresh' _ _ _).symm
    · exact (num_edges_self_zero A b).trans (num_edges_self _ _).symm

theorem unsubdivIso_inl (A : CFGraph) {a b x : A.V} (hab : a ≠ b)
    (h1 : num_edges A a b = 1) (hxa : x ≠ a) (hxb : x ≠ b)
    (hbx : ∀ z, z ≠ a → num_edges A b z = if z = x then 1 else 0) (z : (contract A hab h1).V) :
    (unsubdivIso A hab h1 hxa hxb hbx).vertexEquiv (Sum.inl z) = cval A hab h1 z := rfl

theorem unsubdivIso_inr (A : CFGraph) {a b x : A.V} (hab : a ≠ b)
    (h1 : num_edges A a b = 1) (hxa : x ≠ a) (hxb : x ≠ b)
    (hbx : ∀ z, z ≠ a → num_edges A b z = if z = x then 1 else 0) :
    (unsubdivIso A hab h1 hxa hxb hbx).vertexEquiv (Sum.inr ()) = b := rfl

/-! ## 4. The six contractions -/

/-- In a tree, a divalent vertex has two distinct neighbours, joined to it by one edge each. -/
theorem exists_degree_two_nbrs {A : CFGraph} (hA : graph_connected A) (hA0 : genus A = 0)
    {w : A.V} (hw : vertex_degree A w = 2) :
    ∃ x y : A.V, x ≠ y ∧ x ≠ w ∧ y ≠ w ∧ num_edges A y w = 1 ∧
      ∀ z, z ≠ y → num_edges A w z = if z = x then 1 else 0 := by
  classical
  have hle := IteratedContraction.num_edges_le_one_of_genus_zero_of_connected A hA hA0
  set N := Finset.univ.filter fun z ↦ num_edges A w z = 1 with hN
  have hcard : (N.card : ℤ) = 2 := by
    rw [← hw, hN, Finset.card_filter]
    unfold vertex_degree
    push_cast
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    have := hle w z
    split_ifs with h
    · rw [h]; norm_num
    · omega
  obtain ⟨x, y, hxy, hNxy⟩ := Finset.card_eq_two.mp (by exact_mod_cast hcard)
  have hmem : ∀ z, num_edges A w z = 1 ↔ z = x ∨ z = y := by
    intro z
    have := congrArg (z ∈ ·) hNxy
    simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, eq_iff_iff] at this
    exact this
  have hx := (hmem x).mpr (Or.inl rfl)
  have hy := (hmem y).mpr (Or.inr rfl)
  refine ⟨x, y, hxy, fun h ↦ ?_, fun h ↦ ?_, ?_, fun z hz ↦ ?_⟩
  · rw [h, num_edges_self_zero] at hx; exact zero_ne_one hx
  · rw [h, num_edges_self_zero] at hy; exact zero_ne_one hy
  · rw [num_edges_symmetric]; exact hy
  · by_cases hzx : z = x
    · rw [ite_eq_left hzx, hzx, hx]
    · rw [ite_eq_right hzx]
      have := hle w z
      have hne : num_edges A w z ≠ 1 := fun h ↦ by
        rcases (hmem z).mp h with h' | h'
        · exact hzx h'
        · exact hz h'
      omega

/-- **One leaf deletion**, with its inverse. -/
theorem leaf_step {A : CFGraph.{0}} (hA : graph_connected A) (hA0 : genus A = 0) {u v : A.V}
    (huv : u ≠ v) (hv : vertex_degree A v = 1) (hpos : 0 < num_edges A u v) :
    ∃ (A' : CFGraph.{0}) (back : ∀ z : A.V, z ≠ v → A'.V)
      (ι : CFGraphIso (leafTarget A' (back u huv)) A),
      graph_connected A' ∧ genus A' = 0 ∧ ι.vertexEquiv (Sum.inr ()) = v ∧
      (∀ z hz, ι.vertexEquiv (Sum.inl (back z hz)) = z) ∧
      (∀ z hz, vertex_degree A' (back z hz) = vertex_degree A z - if z = u then 1 else 0) ∧
      (∀ z hz z' hz', num_edges A' (back z hz) (back z' hz') = num_edges A z z') := by
  classical
  have h1 : num_edges A u v = 1 :=
    le_antisymm (IteratedContraction.num_edges_le_one_of_genus_zero_of_connected A hA hA0 u v)
      hpos
  have hpend : ∀ z, z ≠ u → num_edges A v z = 0 := by
    intro z hz
    refine num_edges_eq_zero_of_sum {u} ?_ (by simpa using hz)
    rw [Finset.sum_singleton, num_edges_symmetric, h1, hv]
    norm_num
  refine ⟨contract A huv h1, cv A huv h1, unleafIso A huv h1 hpend,
    graph_connected_contract A huv h1 hA, (genus_contract A huv h1).trans hA0, rfl,
    fun _ _ ↦ rfl, fun z hz ↦ ?_, fun z hz z' hz' ↦ num_edges_contract_pendant A huv h1 hpend _ _⟩
  by_cases hzu : z = u
  · subst hzu
    rw [ite_eq_left rfl]
    have := vertex_degree_contract_merge A huv h1
    rw [hv] at this
    exact this.trans (by ring)
  · rw [ite_eq_right hzu, sub_zero]
    exact vertex_degree_contract_of_ne A huv h1 hz hzu

/-- **One erasure of a divalent vertex**, with its inverse. -/
theorem smooth_step {A : CFGraph.{0}} (hA : graph_connected A) (hA0 : genus A = 0) {b : A.V}
    (hb : vertex_degree A b = 2) :
    ∃ (A' : CFGraph.{0}) (t : A'.edges) (back : ∀ z : A.V, z ≠ b → A'.V)
      (ι : CFGraphIso (subdivTarget A' t) A),
      graph_connected A' ∧ genus A' = 0 ∧ ι.vertexEquiv (Sum.inr ()) = b ∧
      (∀ z hz, ι.vertexEquiv (Sum.inl (back z hz)) = z) ∧
      (∀ z hz, vertex_degree A' (back z hz) = vertex_degree A z) := by
  classical
  obtain ⟨x, y, hxy, hxb, hyb, hy1, hbx⟩ := exists_degree_two_nbrs hA hA0 hb
  refine ⟨contract A hyb hy1, bivalentEdge A hyb hy1 hxy hxb hbx, cv A hyb hy1,
    unsubdivIso A hyb hy1 hxy hxb hbx, graph_connected_contract A hyb hy1 hA,
    (genus_contract A hyb hy1).trans hA0, rfl, fun _ _ ↦ rfl, fun z hz ↦ ?_⟩
  by_cases hzy : z = y
  · subst hzy
    have := vertex_degree_contract_merge A hyb hy1
    rw [hb] at this
    exact this.trans (by ring)
  · exact vertex_degree_contract_of_ne A hyb hy1 hz hzy

/-- **The target of a glued member is a glued target.** A tree `X` with three leaves `v k` at three
distinct trivalent vertices `w k` is `π.T₆` for a tree `T` and a placement `π` (with any sheets),
by an isomorphism carrying `w k` to the image of mark `k` and `v k` to the tip of its arm. -/
theorem exists_targetShape {X : CFGraph.{0}} (hX : graph_connected X) (hX0 : genus X = 0)
    (v w : Fin 3 → X.V) (hv : ∀ k, vertex_degree X (v k) = 1)
    (hw : ∀ k, vertex_degree X (w k) = 3) (hvw : ∀ k, 0 < num_edges X (w k) (v k))
    (hwinj : Function.Injective w) {d : ℕ} (σ : Fin 3 → Fin d) :
    ∃ (T : CFGraph.{0}) (π : Placement T d) (τ : CFGraphIso X π.T₆), π.sheet = σ ∧
      (∀ k, τ.vertexEquiv (w k) = π.markTarget k) ∧
      (∀ k, τ.vertexEquiv (v k) = π.tipTarget k) := by
  classical
  have hwv : ∀ j k, w j ≠ v k := by
    intro j k h
    have := hw j
    rw [h, hv k] at this
    norm_num at this
  have h1 : ∀ k, num_edges X (w k) (v k) = 1 := fun k ↦
    le_antisymm (IteratedContraction.num_edges_le_one_of_genus_zero_of_connected X hX hX0 _ _)
      (hvw k)
  have hpend : ∀ k z, z ≠ w k → num_edges X (v k) z = 0 := by
    intro k z hz
    refine num_edges_eq_zero_of_sum {w k} ?_ (by simpa using hz)
    rw [Finset.sum_singleton, num_edges_symmetric, h1, hv]
    norm_num
  have hvinj : Function.Injective v := by
    intro i j hij
    by_contra hne
    have h0 := hpend i (w j) (fun h ↦ hne (hwinj h).symm)
    rw [hij, num_edges_symmetric, h1] at h0
    exact one_ne_zero h0
  have hww : ∀ j k, j ≠ k → w j ≠ w k := fun j k h e ↦ h (hwinj e)
  have hvv : ∀ j k, j ≠ k → v j ≠ v k := fun j k h e ↦ h (hvinj e)
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  -- delete the leaf `v 2`
  obtain ⟨X₅, b₅, ι₆, hc₅, hg₅, ι₆r, ι₆l, hd₅, hn₅⟩ :=
    leaf_step hX hX0 (hwv 2 2) (hv 2) (hvw 2)
  have inj₅ : ∀ z hz z' hz', b₅ z hz = b₅ z' hz' → z = z' := fun z hz z' hz' h ↦ by
    rw [← ι₆l z hz, ← ι₆l z' hz', h]
  -- delete the leaf `v 1`
  have hw1 : b₅ (w 1) (hwv 1 2) ≠ b₅ (v 1) (hvv 1 2 h12) := fun h ↦ hwv 1 1 (inj₅ _ _ _ _ h)
  obtain ⟨X₄, b₄, ι₅, hc₄, hg₄, ι₅r, ι₅l, hd₄, hn₄⟩ :=
    leaf_step hc₅ hg₅ hw1 (by rw [hd₅, hv, ite_eq_right (hwv 2 1).symm]; norm_num)
      (by rw [hn₅]; exact hvw 1)
  have inj₄ : ∀ z hz z' hz', b₄ z hz = b₄ z' hz' → z = z' := fun z hz z' hz' h ↦ by
    rw [← ι₅l z hz, ← ι₅l z' hz', h]
  -- delete the leaf `v 0`
  have hv₅ : ∀ k, w k ≠ v 1 → b₅ (w k) (hwv k 2) ≠ b₅ (v 1) (hvv 1 2 h12) :=
    fun k hk h ↦ hk (inj₅ _ _ _ _ h)
  have hv0₅ : b₅ (v 0) (hvv 0 2 h02) ≠ b₅ (v 1) (hvv 1 2 h12) :=
    fun h ↦ hvv 0 1 h01 (inj₅ _ _ _ _ h)
  have hw0 : b₄ (b₅ (w 0) (hwv 0 2)) (hv₅ 0 (hwv 0 1)) ≠ b₄ (b₅ (v 0) (hvv 0 2 h02)) hv0₅ :=
    fun h ↦ hwv 0 0 (inj₅ _ _ _ _ (inj₄ _ _ _ _ h))
  obtain ⟨X₃, b₃, ι₄, hc₃, hg₃, ι₄r, ι₄l, hd₃, -⟩ :=
    leaf_step hc₄ hg₄ hw0
      (by
        rw [hd₄, hd₅, hv, ite_eq_right (hwv 2 0).symm, ite_eq_right (fun h ↦ hwv 1 0 (inj₅ _ _ _ _ h).symm)]
        norm_num)
      (by rw [hn₄, hn₅]; exact hvw 0)
  have inj₃ : ∀ z hz z' hz', b₃ z hz = b₃ z' hz' → z = z' := fun z hz z' hz' h ↦ by
    rw [← ι₄l z hz, ← ι₄l z' hz', h]
  -- the three inner ends, in `X₃`
  have hv₄ : ∀ k, w k ≠ v 0 → ∀ h₁ h₂, b₄ (b₅ (w k) h₁) h₂ ≠ b₄ (b₅ (v 0) (hvv 0 2 h02)) hv0₅ :=
    fun k hk h₁ h₂ h ↦ hk (inj₅ _ _ _ _ (inj₄ _ _ _ _ h))
  let W : Fin 3 → X₃.V := fun k ↦
    b₃ (b₄ (b₅ (w k) (hwv k 2)) (hv₅ k (hwv k 1))) (hv₄ k (hwv k 0) _ _)
  have hWl : ∀ k, ι₆.vertexEquiv (Sum.inl (ι₅.vertexEquiv (Sum.inl
      (ι₄.vertexEquiv (Sum.inl (W k)))))) = w k := fun k ↦ by
    simp only [W]; rw [ι₄l, ι₅l, ι₆l]
  have hWinj : Function.Injective W := fun j k h ↦ hwinj (by rw [← hWl j, ← hWl k, h])
  have hW0 : W 0 = b₃ (b₄ (b₅ (w 0) (hwv 0 2)) (hv₅ 0 (hwv 0 1))) hw0 := rfl
  have hdW : ∀ k, vertex_degree X₃ (W k) = 2 := by
    have e₅ : ∀ j k, b₅ (w j) (hwv j 2) = b₅ (w k) (hwv k 2) ↔ j = k := fun j k ↦
      ⟨fun h ↦ hwinj (inj₅ _ _ _ _ h), fun h ↦ by subst h; rfl⟩
    have e₄ : ∀ j k h h', b₄ (b₅ (w j) (hwv j 2)) h = b₄ (b₅ (w k) (hwv k 2)) h' ↔ j = k :=
      fun j k h h' ↦ ⟨fun e ↦ hwinj (inj₅ _ _ _ _ (inj₄ _ _ _ _ e)), fun e ↦ by subst e; rfl⟩
    intro k
    simp only [W]
    rw [hd₃, hd₄, hd₅, hw k]
    simp only [e₄, e₅, hwinj.eq_iff]
    fin_cases k <;> simp
  -- erase `w 2`, `w 1`, `w 0`
  obtain ⟨X₂, t₂, b₂, ι₃, hc₂, hg₂, ι₃r, ι₃l, hd₂⟩ := smooth_step hc₃ hg₃ (hdW 2)
  have hW12 : W 1 ≠ W 2 := fun h ↦ h12 (hWinj h)
  have hW02 : W 0 ≠ W 2 := fun h ↦ h02 (hWinj h)
  obtain ⟨X₁, t₁, b₁, ι₂, hc₁, hg₁, ι₂r, ι₂l, hd₁⟩ :=
    smooth_step hc₂ hg₂ (b := b₂ (W 1) hW12) (by rw [hd₂]; exact hdW 1)
  have hW01 : b₂ (W 0) hW02 ≠ b₂ (W 1) hW12 := fun h ↦ h01 (hWinj (by
    rw [← ι₃l (W 0) hW02, ← ι₃l (W 1) hW12, h]))
  obtain ⟨T, t₀, b₀, ι₁, -, -, ι₁r, -, -⟩ :=
    smooth_step hc₁ hg₁ (b := b₁ (b₂ (W 0) hW02) hW01) (by rw [hd₁, hd₂]; exact hdW 0)
  -- re-assemble: the three subdivisions
  let e₁ := (GluingTransport.edgeEquiv ι₁).symm t₁
  let κ₂ := (subdivMap ι₁ e₁ t₁ (GluingTransport.edgeEquiv_symm_ends ι₁ t₁)).trans ι₂
  let e₂ := (GluingTransport.edgeEquiv κ₂).symm t₂
  let κ₃ := (subdivMap κ₂ e₂ t₂ (GluingTransport.edgeEquiv_symm_ends κ₂ t₂)).trans ι₃
  let π : Placement T d := ⟨t₀, e₁, e₂, σ⟩
  have hm₀ : κ₃.vertexEquiv (π.markVertex₃ 0) = W 0 := by
    show ι₃.vertexEquiv (Sum.inl (ι₂.vertexEquiv (Sum.inl (ι₁.vertexEquiv (Sum.inr ()))))) = W 0
    rw [ι₁r, ι₂l, ι₃l]
  have hm₁ : κ₃.vertexEquiv (π.markVertex₃ 1) = W 1 := by
    show ι₃.vertexEquiv (Sum.inl (ι₂.vertexEquiv (Sum.inr ()))) = W 1
    rw [ι₂r, ι₃l]
  have hm₂ : κ₃.vertexEquiv (π.markVertex₃ 2) = W 2 := ι₃r
  -- and the three arms
  let κ₄ := (leafMap κ₃ (π.markVertex₃ 0) _ (hm₀.trans hW0)).trans ι₄
  have hm₁' : κ₄.vertexEquiv (leafOld π.T₃ _ (π.markVertex₃ 1)) =
      b₄ (b₅ (w 1) (hwv 1 2)) hw1 := by
    show ι₄.vertexEquiv (Sum.inl (κ₃.vertexEquiv (π.markVertex₃ 1))) = _
    rw [hm₁]
    exact ι₄l _ _
  let κ₅ := (leafMap κ₄ _ _ hm₁').trans ι₅
  have hm₂' : κ₅.vertexEquiv (leafOld π.T₄ _ (leafOld π.T₃ _ (π.markVertex₃ 2))) =
      b₅ (w 2) (hwv 2 2) := by
    show ι₅.vertexEquiv (Sum.inl (ι₄.vertexEquiv (Sum.inl (κ₃.vertexEquiv (π.markVertex₃ 2))))) = _
    rw [hm₂]
    simp only [W]
    rw [ι₄l, ι₅l]
  let κ₆ : CFGraphIso π.T₆ X := (leafMap κ₅ _ _ hm₂').trans ι₆
  refine ⟨T, π, κ₆.symm, rfl, fun k ↦ ?_, fun k ↦ ?_⟩
  · show κ₆.vertexEquiv.symm (w k) = _
    rw [Equiv.symm_apply_eq]
    show w k = ι₆.vertexEquiv (Sum.inl (ι₅.vertexEquiv (Sum.inl (ι₄.vertexEquiv
      (Sum.inl (κ₃.vertexEquiv (π.markVertex₃ k)))))))
    fin_cases k
    · show w 0 = ι₆.vertexEquiv (Sum.inl (ι₅.vertexEquiv (Sum.inl (ι₄.vertexEquiv
        (Sum.inl (κ₃.vertexEquiv (π.markVertex₃ 0)))))))
      rw [hm₀, hWl]
    · show w 1 = ι₆.vertexEquiv (Sum.inl (ι₅.vertexEquiv (Sum.inl (ι₄.vertexEquiv
        (Sum.inl (κ₃.vertexEquiv (π.markVertex₃ 1)))))))
      rw [hm₁, hWl]
    · show w 2 = ι₆.vertexEquiv (Sum.inl (ι₅.vertexEquiv (Sum.inl (ι₄.vertexEquiv
        (Sum.inl (κ₃.vertexEquiv (π.markVertex₃ 2)))))))
      rw [hm₂, hWl]
  · show κ₆.vertexEquiv.symm (v k) = _
    rw [Equiv.symm_apply_eq]
    fin_cases k
    · show v 0 = ι₆.vertexEquiv (Sum.inl (ι₅.vertexEquiv (Sum.inl (ι₄.vertexEquiv (Sum.inr ())))))
      rw [ι₄r, ι₅l, ι₆l]
    · show v 1 = ι₆.vertexEquiv (Sum.inl (ι₅.vertexEquiv (Sum.inr ())))
      rw [ι₅r, ι₆l]
    · show v 2 = ι₆.vertexEquiv (Sum.inr ())
      rw [ι₆r]

end OntoTarget

end GenusSixExistence.Tripod.Gluing

end
