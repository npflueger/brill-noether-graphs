import Utilities.CubicGraphs.CubicDarts

/-!
# Peeling an actual lollipop from a cubic dart graph

The genus-induction step removes a loop vertex and its bridge's far endpoint,
then joins the two remaining external darts. All reconstruction maps use the
actual six removed darts. The exceptional case where the far endpoint also
carries a loop is derived to have genus two, using connectedness.

This is the inverse of the `plant` construction of
`Utilities.CubicGraphs.CubicDarts`. It complements the
attachment-slide/lift mechanism in Caporaso's Proposition 3.3.2; it does not
assert that every graph can already be moved to one carrying a loop.
-/

namespace DraismaVargas.Infrastructure.CubicDarts

open Finset CubicDartGraph

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- The actual loop, bridge, and two other darts at its far endpoint. -/
structure LollipopData (G : CubicDartGraph D V) where
  ell : D
  q : D
  s : D
  t : D
  loop : G.vert (G.op ell) = G.vert ell
  q_vert : G.vert q = G.vert ell
  q_ne : q ≠ ell
  q_ne_op : q ≠ G.op ell
  allA : ∀ z, G.vert z = G.vert ell → z = ell ∨ z = G.op ell ∨ z = q
  s_vert : G.vert s = G.vert (G.op q)
  t_vert : G.vert t = G.vert (G.op q)
  s_ne : s ≠ G.op q
  t_ne : t ≠ G.op q
  st : s ≠ t
  allB : ∀ z, G.vert z = G.vert (G.op q) → z = G.op q ∨ z = s ∨ z = t
  ops : G.op s ≠ t

namespace LollipopData

variable {G : CubicDartGraph D V} (L : LollipopData G)

def A : V := G.vert L.ell
def B : V := G.vert (G.op L.q)

theorem A_ne_B : L.A ≠ L.B := by
  intro h
  rcases L.allA (G.op L.q) h.symm with h' | h' | h'
  · exact L.q_ne_op ((G.op_eq_iff).mp h')
  · exact L.q_ne (G.op_injective h')
  · exact G.op_ne L.q h'

end LollipopData

/-- A vertex of a cubic dart graph is represented by an actual dart. -/
theorem vert_surjective (G : CubicDartGraph D V) : Function.Surjective G.vert := by
  intro v
  have h := G.card_fibre v
  have hNonempty : (univ.filter (fun d ↦ G.vert d = v)).Nonempty := by
    rw [← card_pos, h]
    omega
  obtain ⟨d, hd⟩ := hNonempty
  exact ⟨d, (mem_filter.mp hd).2⟩

/-- A second loop at the bridge's far endpoint exhausts a connected graph:
this is the genus-two dumbbell exception, not a new peeling hypothesis. -/
theorem genus_le_two_of_double_lollipop (G : CubicDartGraph D V)
    (ell q s t : D)
    (hLoop : G.vert (G.op ell) = G.vert ell)
    (hq : G.vert q = G.vert ell)
    (hAllA : ∀ z, G.vert z = G.vert ell → z = ell ∨ z = G.op ell ∨ z = q)
    (hs : G.vert s = G.vert (G.op q))
    (ht : G.vert t = G.vert (G.op q))
    (hAllB : ∀ z, G.vert z = G.vert (G.op q) → z = G.op q ∨ z = s ∨ z = t)
    (hOp : G.op s = t) : G.genus ≤ 2 := by
  let P : D → Prop := fun z ↦ G.vert z = G.vert ell ∨ G.vert z = G.vert (G.op q)
  have hClosed : ∀ z, P z → P (G.op z) := by
    intro z hz
    rcases hz with hz | hz
    · rcases hAllA z hz with rfl | rfl | rfl
      · exact Or.inl hLoop
      · exact Or.inl (by rw [G.op_invol])
      · exact Or.inr rfl
    · rcases hAllB z hz with rfl | rfl | rfl
      · exact Or.inl (by rw [G.op_invol]; exact hq)
      · exact Or.inr (by rw [hOp]; exact ht)
      · exact Or.inr (by rw [← hOp, G.op_invol]; exact hs)
  have hAll : ∀ z, P z := by
    have key : ∀ x y, Relation.EqvGen (DartRel G.op G.vert) x y → (P x ↔ P y) := by
      intro x y h
      induction h with
      | rel x y hxy =>
        rcases hxy with hxy | hxy
        · subst y
          exact ⟨hClosed x, fun hp ↦ by simpa only [G.op_invol] using hClosed (G.op x) hp⟩
        · change (_ = _ ∨ _ = _) ↔ (_ = _ ∨ _ = _)
          rw [hxy]
      | refl x => rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    exact fun z ↦ (key ell z (G.conn ell z)).mp (Or.inl rfl)
  have hSub : (univ : Finset V) ⊆ {G.vert ell, G.vert (G.op q)} := by
    intro v _
    obtain ⟨d, rfl⟩ := vert_surjective G v
    simpa only [mem_insert, mem_singleton] using hAll d
  have hCard : Fintype.card V ≤ 2 :=
    le_trans (by simpa only [card_univ] using card_le_card hSub)
      (le_trans (card_insert_le _ _) (by simp))
  unfold genus
  omega

/-- Every actual loop in genus at least three supplies valid peel data. -/
theorem exists_lollipopData (G : CubicDartGraph D V) (ell : D)
    (hLoop : G.IsLoopDart ell) (hg : 3 ≤ G.genus) :
    ∃ L : LollipopData G, L.ell = ell := by
  obtain ⟨q, hq, hq₁, hq₂, hAllA⟩ :=
    G.exists_third rfl hLoop (Ne.symm (G.op_ne ell))
  obtain ⟨s, hs, hsNe⟩ : ∃ s, G.vert s = G.vert (G.op q) ∧ s ≠ G.op q := by
    have hCard := G.card_fibre (G.vert (G.op q))
    have hNot : ¬ (univ.filter (fun z ↦ G.vert z = G.vert (G.op q))) ⊆ {G.op q} := by
      intro h
      have := card_le_card h
      rw [hCard, card_singleton] at this
      omega
    obtain ⟨s, hs, hsNe⟩ := not_subset.mp hNot
    exact ⟨s, (mem_filter.mp hs).2, by simpa only [mem_singleton] using hsNe⟩
  obtain ⟨t, ht, htNe, hts, hAllB⟩ := G.exists_third rfl hs hsNe.symm
  refine ⟨⟨ell, q, s, t, hLoop, hq, hq₁, hq₂, hAllA, hs, ht, hsNe, htNe,
    hts.symm, hAllB, ?_⟩, rfl⟩
  intro hOp
  have := genus_le_two_of_double_lollipop G ell q s t hLoop hq hAllA hs ht hAllB hOp
  omega

namespace LollipopData

variable {G : CubicDartGraph D V} (L : LollipopData G)

abbrev PeelV := {v : V // v ≠ L.A ∧ v ≠ L.B}
abbrev PeelD := {d : D // G.vert d ≠ L.A ∧ G.vert d ≠ L.B}

theorem q_ne_s : L.q ≠ L.s := by
  intro h
  exact L.A_ne_B (L.q_vert.symm.trans ((congrArg G.vert h).trans L.s_vert))

theorem q_ne_t : L.q ≠ L.t := by
  intro h
  exact L.A_ne_B (L.q_vert.symm.trans ((congrArg G.vert h).trans L.t_vert))

theorem op_s_ne_A : G.vert (G.op L.s) ≠ L.A := by
  intro h
  rcases L.allA _ h with h | h | h
  · have hs := (G.op_eq_iff).mp h
    exact L.A_ne_B (L.loop.symm.trans ((congrArg G.vert hs).symm.trans L.s_vert))
  · have hs := G.op_injective h
    exact L.A_ne_B ((congrArg G.vert hs).symm.trans L.s_vert)
  · exact L.s_ne ((G.op_eq_iff).mp h)

theorem op_t_ne_A : G.vert (G.op L.t) ≠ L.A := by
  intro h
  rcases L.allA _ h with h | h | h
  · have ht := (G.op_eq_iff).mp h
    exact L.A_ne_B (L.loop.symm.trans ((congrArg G.vert ht).symm.trans L.t_vert))
  · have ht := G.op_injective h
    exact L.A_ne_B ((congrArg G.vert ht).symm.trans L.t_vert)
  · exact L.t_ne ((G.op_eq_iff).mp h)

theorem op_s_ne_B : G.vert (G.op L.s) ≠ L.B := by
  intro h
  rcases L.allB _ h with h | h | h
  · exact L.q_ne_s (G.op_injective h).symm
  · exact G.op_ne L.s h
  · exact L.ops h

theorem op_t_ne_B : G.vert (G.op L.t) ≠ L.B := by
  intro h
  rcases L.allB _ h with h | h | h
  · exact L.q_ne_t (G.op_injective h).symm
  · exact L.ops ((G.op_eq_iff).mpr h.symm)
  · exact G.op_ne L.t h

/-- The two actual outside darts become the suppressed edge. -/
def root : L.PeelD := ⟨G.op L.s, L.op_s_ne_A, L.op_s_ne_B⟩
def mate : L.PeelD := ⟨G.op L.t, L.op_t_ne_A, L.op_t_ne_B⟩

theorem root_ne_mate : L.root ≠ L.mate := by
  intro h
  exact L.st (G.op_injective (congrArg Subtype.val h))

theorem op_remaining (d : L.PeelD) (hs : d ≠ L.root) (ht : d ≠ L.mate) :
    G.vert (G.op d.1) ≠ L.A ∧ G.vert (G.op d.1) ≠ L.B := by
  constructor
  · intro h
    rcases L.allA _ h with h | h | h
    · have hd := (G.op_eq_iff).mp h
      exact d.2.1 ((congrArg G.vert hd).trans L.loop)
    · exact d.2.1 (congrArg G.vert (G.op_injective h))
    · exact d.2.2 (congrArg G.vert ((G.op_eq_iff).mp h))
  · intro h
    rcases L.allB _ h with h | h | h
    · exact d.2.1 ((congrArg G.vert (G.op_injective h)).trans L.q_vert)
    · exact hs (Subtype.ext ((G.op_eq_iff).mp h))
    · exact ht (Subtype.ext ((G.op_eq_iff).mp h))

/-- Reconnect the two external darts and preserve every other edge. -/
def peelOp (d : L.PeelD) : L.PeelD :=
  if hs : d = L.root then L.mate else if ht : d = L.mate then L.root
  else ⟨G.op d.1, L.op_remaining d hs ht⟩

@[simp] theorem peelOp_root : L.peelOp L.root = L.mate := by
  simp only [peelOp, dif_pos]

@[simp] theorem peelOp_mate : L.peelOp L.mate = L.root := by
  simp only [peelOp, dif_neg L.root_ne_mate.symm, dif_pos]

theorem peelOp_other (d : L.PeelD) (hs : d ≠ L.root) (ht : d ≠ L.mate) :
    (L.peelOp d).1 = G.op d.1 := by
  simp only [peelOp, dif_neg hs, dif_neg ht]

theorem peelOp_invol (d : L.PeelD) : L.peelOp (L.peelOp d) = d := by
  by_cases hs : d = L.root
  · subst d; simp
  by_cases ht : d = L.mate
  · subst d; simp
  have hs' : L.peelOp d ≠ L.root := by
    intro h
    have hv := congrArg Subtype.val h
    rw [L.peelOp_other d hs ht] at hv
    exact d.2.2 ((congrArg G.vert (G.op_injective hv)).trans L.s_vert)
  have ht' : L.peelOp d ≠ L.mate := by
    intro h
    have hv := congrArg Subtype.val h
    rw [L.peelOp_other d hs ht] at hv
    exact d.2.2 ((congrArg G.vert (G.op_injective hv)).trans L.t_vert)
  apply Subtype.ext
  rw [L.peelOp_other _ hs' ht', L.peelOp_other d hs ht, G.op_invol]

theorem peelOp_ne (d : L.PeelD) : L.peelOp d ≠ d := by
  by_cases hs : d = L.root
  · subst d; simpa using L.root_ne_mate.symm
  by_cases ht : d = L.mate
  · subst d; simpa using L.root_ne_mate
  intro h
  have hv := congrArg Subtype.val h
  rw [L.peelOp_other d hs ht] at hv
  exact G.op_ne d.1 hv

def peelVert (d : L.PeelD) : L.PeelV := ⟨G.vert d.1, d.2⟩

theorem peel_card_fibre (v : L.PeelV) :
    (univ.filter (fun d ↦ L.peelVert d = v)).card = 3 := by
  rw [← G.card_fibre v.1]
  refine card_bij (fun d _ ↦ d.1) ?_ ?_ ?_
  · intro d hd
    exact mem_filter.mpr ⟨mem_univ _, congrArg Subtype.val (mem_filter.mp hd).2⟩
  · intro d _ e _ h
    exact Subtype.ext h
  · intro d hd
    have hv := (mem_filter.mp hd).2
    refine ⟨⟨d, by rw [hv]; exact v.2⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    exact Subtype.ext hv

/-- Collapse the removed local configuration onto one end of the new edge. -/
def retract (d : D) : L.PeelD :=
  if h : G.vert d ≠ L.A ∧ G.vert d ≠ L.B then ⟨d, h⟩ else L.root

@[simp] theorem retract_remaining (d : L.PeelD) : L.retract d.1 = d := by
  simp only [retract, dif_pos d.2]

theorem retract_removed (d : D) (h : ¬ (G.vert d ≠ L.A ∧ G.vert d ≠ L.B)) :
    L.retract d = L.root := by
  simp only [retract, dif_neg h]

theorem eq_root_or_mate_of_op_removed (d : L.PeelD)
    (h : ¬ (G.vert (G.op d.1) ≠ L.A ∧ G.vert (G.op d.1) ≠ L.B)) :
    d = L.root ∨ d = L.mate := by
  by_cases hs : d = L.root
  · exact Or.inl hs
  by_cases ht : d = L.mate
  · exact Or.inr ht
  exact (h (L.op_remaining d hs ht)).elim

theorem retract_vert (d e : D) (h : G.vert d = G.vert e) :
    Relation.EqvGen (DartRel L.peelOp L.peelVert) (L.retract d) (L.retract e) := by
  by_cases hd : G.vert d ≠ L.A ∧ G.vert d ≠ L.B
  · have he : G.vert e ≠ L.A ∧ G.vert e ≠ L.B := by rw [← h]; exact hd
    apply DartRel.of_vert
    simp only [retract, dif_pos hd, dif_pos he]
    exact Subtype.ext h
  · have he : ¬ (G.vert e ≠ L.A ∧ G.vert e ≠ L.B) := by rw [← h]; exact hd
    rw [L.retract_removed d hd, L.retract_removed e he]
    exact Relation.EqvGen.refl _

theorem retract_op_of_remaining (d : L.PeelD) :
    Relation.EqvGen (DartRel L.peelOp L.peelVert) d (L.retract (G.op d.1)) := by
  by_cases he : G.vert (G.op d.1) ≠ L.A ∧ G.vert (G.op d.1) ≠ L.B
  · have hs : d ≠ L.root := by
      intro h
      have hv := congrArg Subtype.val h
      exact he.2 (by rw [hv]; change G.vert (G.op (G.op L.s)) = L.B
                     rw [G.op_invol]; exact L.s_vert)
    have ht : d ≠ L.mate := by
      intro h
      have hv := congrArg Subtype.val h
      exact he.2 (by rw [hv]; change G.vert (G.op (G.op L.t)) = L.B
                     rw [G.op_invol]; exact L.t_vert)
    apply DartRel.of_op
    apply Subtype.ext
    rw [L.peelOp_other d hs ht]
    simp only [retract, dif_pos he]
  · rw [L.retract_removed _ he]
    rcases L.eq_root_or_mate_of_op_removed d he with rfl | rfl
    · exact Relation.EqvGen.refl _
    · exact DartRel.of_op L.peelOp_mate

theorem retract_op (d : D) :
    Relation.EqvGen (DartRel L.peelOp L.peelVert) (L.retract d) (L.retract (G.op d)) := by
  by_cases hd : G.vert d ≠ L.A ∧ G.vert d ≠ L.B
  · simpa only [L.retract_remaining ⟨d, hd⟩] using L.retract_op_of_remaining ⟨d, hd⟩
  by_cases he : G.vert (G.op d) ≠ L.A ∧ G.vert (G.op d) ≠ L.B
  · have h := (L.retract_op_of_remaining ⟨G.op d, he⟩).symm
    simpa only [G.op_invol, L.retract_remaining ⟨G.op d, he⟩] using h
  · rw [L.retract_removed d hd, L.retract_removed _ he]
    exact Relation.EqvGen.refl _

theorem peel_conn (p q : L.PeelD) :
    Relation.EqvGen (DartRel L.peelOp L.peelVert) p q := by
  have key : ∀ x y, Relation.EqvGen (DartRel G.op G.vert) x y →
      Relation.EqvGen (DartRel L.peelOp L.peelVert) (L.retract x) (L.retract y) := by
    intro x y h
    induction h with
    | rel x y hxy =>
      rcases hxy with hxy | hxy
      · subst y; exact L.retract_op x
      · exact L.retract_vert x y hxy
    | refl x => exact Relation.EqvGen.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact DartRel.trans ih₁ ih₂
  simpa only [retract_remaining] using key p.1 q.1 (G.conn p.1 q.1)

/-- The smaller cubic connected graph, with the actual surviving dart set. -/
def peel : CubicDartGraph L.PeelD L.PeelV where
  op := L.peelOp
  vert := L.peelVert
  op_invol := L.peelOp_invol
  op_ne := L.peelOp_ne
  card_fibre := L.peel_card_fibre
  conn := L.peel_conn

/-- The subdivision point is the old bridge foot; the new loop vertex is
the old loop vertex. -/
def localV : Fin 2 → V := ![L.B, L.A]

theorem localV_injective : Function.Injective L.localV := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [localV, L.A_ne_B, L.A_ne_B.symm]

/-- The six removed darts, in the literal ordering used by `plant`. -/
def localD : Fin 6 → D := ![L.s, L.t, G.op L.q, L.q, L.ell, G.op L.ell]

theorem localD_vert (k : Fin 6) : G.vert (L.localD k) = L.localV (plantVertInr k) := by
  fin_cases k <;> simp [localD, localV, L.s_vert, L.t_vert, L.q_vert, L.loop, A, B]

theorem localD_injective : Function.Injective L.localD := by
  intro i j h
  have hv := L.localV_injective
    ((L.localD_vert i).symm.trans ((congrArg G.vert h).trans (L.localD_vert j)))
  have hOp := G.op_ne L.ell
  fin_cases i <;> fin_cases j <;>
    simp [localD, plantVertInr] at h hv ⊢ <;>
    first
    | exact (L.st h).elim
    | exact (L.st h.symm).elim
    | exact (L.s_ne h).elim
    | exact (L.s_ne h.symm).elim
    | exact (L.t_ne h).elim
    | exact (L.t_ne h.symm).elim
    | exact (L.q_ne h).elim
    | exact (L.q_ne h.symm).elim
    | exact (L.q_ne_op h).elim
    | exact (L.q_ne_op h.symm).elim
    | exact (hOp h).elim
    | exact (hOp h.symm).elim

def emitV : L.PeelV ⊕ Fin 2 → V := Sum.elim Subtype.val L.localV

theorem localV_removed (k : Fin 2) : L.localV k = L.A ∨ L.localV k = L.B := by
  fin_cases k <;> simp [localV]

theorem emitV_bijective : Function.Bijective L.emitV := by
  constructor
  · rintro (v | i) (w | j) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact ((L.localV_removed j).elim
        (fun hi ↦ v.2.1 (h.trans hi)) (fun hi ↦ v.2.2 (h.trans hi))).elim
    · exact ((L.localV_removed i).elim
        (fun hi ↦ w.2.1 (h.symm.trans hi)) (fun hi ↦ w.2.2 (h.symm.trans hi))).elim
    · exact congrArg Sum.inr (L.localV_injective h)
  · intro v
    by_cases ha : v = L.A
    · exact ⟨Sum.inr 1, ha.symm⟩
    by_cases hb : v = L.B
    · exact ⟨Sum.inr 0, hb.symm⟩
    exact ⟨Sum.inl ⟨v, ha, hb⟩, rfl⟩

def emitD : L.PeelD ⊕ Fin 6 → D := Sum.elim Subtype.val L.localD

theorem localD_removed (k : Fin 6) : G.vert (L.localD k) = L.A ∨ G.vert (L.localD k) = L.B := by
  rw [L.localD_vert]
  exact L.localV_removed _

theorem emitD_bijective : Function.Bijective L.emitD := by
  constructor
  · rintro (d | i) (e | j) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact ((L.localD_removed j).elim
        (fun hj ↦ d.2.1 ((congrArg G.vert h).trans hj))
        (fun hj ↦ d.2.2 ((congrArg G.vert h).trans hj))).elim
    · exact ((L.localD_removed i).elim
        (fun hi ↦ e.2.1 ((congrArg G.vert h).symm.trans hi))
        (fun hi ↦ e.2.2 ((congrArg G.vert h).symm.trans hi))).elim
    · exact congrArg Sum.inr (L.localD_injective h)
  · intro d
    by_cases ha : G.vert d = L.A
    · rcases L.allA d ha with h | h | h
      · exact ⟨Sum.inr 4, h.symm⟩
      · exact ⟨Sum.inr 5, h.symm⟩
      · exact ⟨Sum.inr 3, h.symm⟩
    by_cases hb : G.vert d = L.B
    · rcases L.allB d hb with h | h | h
      · exact ⟨Sum.inr 2, h.symm⟩
      · exact ⟨Sum.inr 0, h.symm⟩
      · exact ⟨Sum.inr 1, h.symm⟩
    exact ⟨Sum.inl ⟨d, ha, hb⟩, rfl⟩

noncomputable def vertexEquiv : (L.PeelV ⊕ Fin 2) ≃ V :=
  Equiv.ofBijective L.emitV L.emitV_bijective

noncomputable def dartEquiv : (L.PeelD ⊕ Fin 6) ≃ D :=
  Equiv.ofBijective L.emitD L.emitD_bijective

theorem genus_peel : L.peel.genus + 1 = G.genus := by
  have hCard := Fintype.card_congr L.vertexEquiv
  rw [Fintype.card_sum, Fintype.card_fin] at hCard
  change Fintype.card L.PeelV / 2 + 1 + 1 = Fintype.card V / 2 + 1
  omega

@[simp] theorem peel_op_root : L.peel.op L.root = L.mate := L.peelOp_root

theorem emitD_op (d : L.PeelD ⊕ Fin 6) :
    G.op (L.emitD d) = L.emitD ((plant L.peel L.root).op d) := by
  rcases d with d | k
  · by_cases hs : d = L.root
    · subst d
      simp only [plant_op, plantOp_inl_self]
      change G.op (G.op L.s) = L.s
      exact G.op_invol L.s
    by_cases ht : d = L.mate
    · subst d
      rw [← L.peel_op_root, plant_op, plantOp_inl_op]
      change G.op (L.peel.op L.root).1 = L.t
      rw [L.peel_op_root]
      exact G.op_invol L.t
    · have ht' : d ≠ L.peel.op L.root := by rwa [L.peel_op_root]
      rw [plant_op, plantOp_inl_of_ne L.peel L.root hs ht']
      exact (L.peelOp_other d hs ht).symm
  · fin_cases k
    · change G.op L.s = L.root.1
      rfl
    · change G.op L.t = (L.peel.op L.root).1
      rw [L.peel_op_root]
      rfl
    · change G.op (G.op L.q) = L.q
      exact G.op_invol L.q
    · change G.op L.q = G.op L.q
      rfl
    · change G.op L.ell = G.op L.ell
      rfl
    · change G.op (G.op L.ell) = L.ell
      exact G.op_invol L.ell

theorem emitD_vert (d : L.PeelD ⊕ Fin 6) :
    G.vert (L.emitD d) = L.emitV ((plant L.peel L.root).vert d) := by
  rcases d with d | k
  · rfl
  · exact L.localD_vert k

/-- Replanting the suppressed edge recovers the original graph with an
explicit bijection on every dart and vertex, not merely matching counts. -/
noncomputable def reconstructionIso : Iso (plant L.peel L.root) G where
  dart := L.dartEquiv
  vtx := L.vertexEquiv
  op_map := L.emitD_op
  vert_map := L.emitD_vert

@[simp] theorem reconstructionIso_dart_inl (d : L.PeelD) :
    L.reconstructionIso.dart (Sum.inl d) = d.1 := rfl

@[simp] theorem reconstructionIso_dart_inr (k : Fin 6) :
    L.reconstructionIso.dart (Sum.inr k) = L.localD k := rfl

@[simp] theorem reconstructionIso_vertex_inl (v : L.PeelV) :
    L.reconstructionIso.vtx (Sum.inl v) = v.1 := rfl

@[simp] theorem reconstructionIso_vertex_inr (k : Fin 2) :
    L.reconstructionIso.vtx (Sum.inr k) = L.localV k := rfl

theorem card_peel_vertices : Fintype.card L.PeelV + 2 = Fintype.card V := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr L.vertexEquiv

theorem card_peel_darts : Fintype.card L.PeelD + 6 = Fintype.card D := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using Fintype.card_congr L.dartEquiv

theorem reachesIso_plant_peel : ReachesIso G (plant L.peel L.root) :=
  ReachesIso.of_iso L.reconstructionIso.symm

end LollipopData

/-- An actual loop in genus at least three can be peeled. The returned
smaller graph is cubic and connected by construction, has genus one less,
and replanting its named edge recovers the original literal dart graph. -/
theorem exists_peel_of_loop (G : CubicDartGraph D V) (ell : D)
    (hLoop : G.IsLoopDart ell) (hg : 3 ≤ G.genus) :
    ∃ L : LollipopData G, L.ell = ell ∧
      L.peel.genus + 1 = G.genus ∧ 2 ≤ L.peel.genus ∧
      Nonempty (Iso (plant L.peel L.root) G) := by
  obtain ⟨L, hL⟩ := exists_lollipopData G ell hLoop hg
  refine ⟨L, hL, L.genus_peel, ?_, ⟨L.reconstructionIso⟩⟩
  have h := L.genus_peel
  omega

/-- Non-vacuity: the loop introduced in the genus-three caterpillar peels
to a genus-two graph and its actual plant reconstructs the caterpillar. -/
theorem caterpillar_three_peel :
    ∃ L : LollipopData (caterpillarDarts 3), L.peel.genus = 2 ∧
      Nonempty (Iso (plant L.peel L.root) (caterpillarDarts 3)) := by
  obtain ⟨L, _, hGenus, _, hIso⟩ := exists_peel_of_loop (caterpillarDarts 3)
    (Sum.inr 4) (by rfl) (by rw [genus_caterpillarDarts (by omega)])
  refine ⟨L, ?_, hIso⟩
  rw [genus_caterpillarDarts (by omega)] at hGenus
  omega

end DraismaVargas.Infrastructure.CubicDarts
