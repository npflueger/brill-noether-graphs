import Utilities.CubicGraphs.CubicDarts

/-!
# The actual genus-two cubic dart classification

Every connected cubic dart graph of genus two is isomorphic to the theta
graph or the dumbbell. We derive the two vertices and six darts, and then
construct the isomorphism from literal paired dart lists. No nonemptiness
assumption or precomputed classification is imposed on the incoming graph.

This is the genus-two base case for the lollipop induction toward the ordinary
cubic linkage theorem of Caporaso, Theorem 2.4.3 (arXiv:1001.2815v5). Loops
are allowed; the two alternatives are derived here rather than postulated.
-/

namespace DraismaVargas.Infrastructure.CubicDarts

open Finset CubicDartGraph

namespace GenusTwo

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  (G : CubicDartGraph D V) (hg : G.genus = 2)

include hg

theorem card_vertices : Fintype.card V = 2 := by
  have h := G.card_verts_add_two
  rw [hg] at h
  omega

theorem card_darts : Fintype.card D = 6 := by
  rw [G.card_darts, card_vertices G hg]

theorem vertex_cases (a b : V) (hab : a ≠ b) (v : V) : v = a ∨ v = b := by
  have hEq : ({a, b} : Finset V) = univ := by
    apply eq_of_subset_of_card_le (subset_univ _)
    rw [card_univ, card_vertices G hg, card_pair hab]
  have hMem : v ∈ ({a, b} : Finset V) := by rw [hEq]; exact mem_univ _
  simpa only [mem_insert, mem_singleton] using hMem

omit hg in
theorem exists_other_dart (d : D) : ∃ s : D, G.vert s = G.vert d ∧ s ≠ d := by
  have hCard := G.card_fibre (G.vert d)
  have hNot : ¬ (univ.filter (fun z ↦ G.vert z = G.vert d)) ⊆ {d} := by
    intro h
    have := card_le_card h
    rw [hCard, card_singleton] at this
    omega
  obtain ⟨s, hs, hsNe⟩ := not_subset.mp hNot
  exact ⟨s, (mem_filter.mp hs).2, by simpa only [mem_singleton] using hsNe⟩

/-- Without loops, all three darts at the first vertex pair to the second
vertex. Their literal paired enumeration gives the theta isomorphism. -/
theorem iso_theta_of_no_loop (hNoLoop : ¬ G.HasLoop) : Nonempty (Iso theta G) := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card
    (show 1 < Fintype.card V by rw [card_vertices G hg]; omega)
  obtain ⟨p, q, r, hpq, hpr, hqr, hAll⟩ := card_eq_three.mp (G.card_fibre a)
  have hAt : ∀ d, G.vert d = a ↔ d = p ∨ d = q ∨ d = r := by
    intro d
    have := congrArg (fun s : Finset D ↦ d ∈ s) hAll
    simpa only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton] using iff_of_eq this
  have hp : G.vert p = a := (hAt p).mpr (Or.inl rfl)
  have hq : G.vert q = a := (hAt q).mpr (Or.inr (Or.inl rfl))
  have hr : G.vert r = a := (hAt r).mpr (Or.inr (Or.inr rfl))
  have hOther : ∀ d, G.vert d = a → G.vert (G.op d) = b := by
    intro d hd
    rcases vertex_cases G hg a b hab (G.vert (G.op d)) with h | h
    · exact (hNoLoop ⟨d, h.trans hd.symm⟩).elim
    · exact h
  have hReverse : ∀ d, G.vert d = b → G.vert (G.op d) = a := by
    intro d hd
    rcases vertex_cases G hg a b hab (G.vert (G.op d)) with h | h
    · exact h
    · exact (hNoLoop ⟨d, h.trans hd.symm⟩).elim
  let dart : Fin 6 → D := ![p, G.op p, q, G.op q, r, G.op r]
  let vertex : Fin 2 → V := ![a, b]
  have hD : Function.Surjective dart := by
    intro d
    rcases vertex_cases G hg a b hab (G.vert d) with h | h
    · rcases (hAt d).mp h with h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨2, h.symm⟩
      · exact ⟨4, h.symm⟩
    · rcases (hAt (G.op d)).mp (hReverse d h) with h | h | h
      · exact ⟨1, ((G.op_eq_iff).mp h).symm⟩
      · exact ⟨3, ((G.op_eq_iff).mp h).symm⟩
      · exact ⟨5, ((G.op_eq_iff).mp h).symm⟩
  have hV : Function.Surjective vertex := by
    intro v
    rcases vertex_cases G hg a b hab v with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
  refine ⟨{
    dart := Equiv.ofBijective dart ((Fintype.bijective_iff_surjective_and_card dart).mpr
      ⟨hD, by rw [Fintype.card_fin, card_darts G hg]⟩)
    vtx := Equiv.ofBijective vertex ((Fintype.bijective_iff_surjective_and_card vertex).mpr
      ⟨hV, by rw [Fintype.card_fin, card_vertices G hg]⟩)
    op_map := ?_
    vert_map := ?_ }⟩
  · intro k
    change G.op (dart k) = dart (smallOp k)
    fin_cases k <;> simp [dart, smallOp, G.op_invol]
  · intro k
    change G.vert (dart k) = vertex (thetaVert k)
    fin_cases k <;> simp [dart, vertex, thetaVert, hp, hq, hr,
      hOther p hp, hOther q hq, hOther r hr]

/-- A loop supplies two darts at one vertex and a bridge to the other.
The remaining two darts are forced to pair, giving the literal dumbbell. -/
theorem iso_dumbbell_of_loop (ell : D) (hLoop : G.IsLoopDart ell) :
    Nonempty (Iso dumbbell G) := by
  obtain ⟨q, hq, hq₁, hq₂, hAllA⟩ :=
    G.exists_third rfl hLoop (Ne.symm (G.op_ne ell))
  have hAB : G.vert ell ≠ G.vert (G.op q) := by
    intro h
    rcases hAllA (G.op q) h.symm with h | h | h
    · exact hq₂ ((G.op_eq_iff).mp h)
    · exact hq₁ (G.op_injective h)
    · exact G.op_ne q h
  obtain ⟨s, hs, hsNe⟩ := exists_other_dart G (G.op q)
  obtain ⟨t, ht, htNe, hts, hAllB⟩ := G.exists_third rfl hs hsNe.symm
  have hsA : G.vert s ≠ G.vert ell := fun h ↦ hAB (h.symm.trans hs)
  have hsOpA : G.vert (G.op s) ≠ G.vert ell := by
    intro h
    rcases hAllA (G.op s) h with h | h | h
    · exact hsA ((congrArg G.vert ((G.op_eq_iff).mp h)).trans hLoop)
    · exact hsA (congrArg G.vert (G.op_injective h))
    · exact hsNe ((G.op_eq_iff).mp h)
  have hsOpB : G.vert (G.op s) = G.vert (G.op q) :=
    (vertex_cases G hg _ _ hAB _).resolve_left hsOpA
  have hOp : G.op s = t := by
    rcases hAllB (G.op s) hsOpB with h | h | h
    · exact (hsA ((congrArg G.vert (G.op_injective h)).trans hq)).elim
    · exact (G.op_ne s h).elim
    · exact h
  have hOp' : G.op t = s := (G.op_eq_iff).mpr hOp.symm
  let dart : Fin 6 → D := ![ell, G.op ell, q, G.op q, s, t]
  let vertex : Fin 2 → V := ![G.vert ell, G.vert (G.op q)]
  have hD : Function.Surjective dart := by
    intro d
    rcases vertex_cases G hg _ _ hAB (G.vert d) with h | h
    · rcases hAllA d h with h | h | h
      · exact ⟨0, h.symm⟩
      · exact ⟨1, h.symm⟩
      · exact ⟨2, h.symm⟩
    · rcases hAllB d h with h | h | h
      · exact ⟨3, h.symm⟩
      · exact ⟨4, h.symm⟩
      · exact ⟨5, h.symm⟩
  have hV : Function.Surjective vertex := by
    intro v
    rcases vertex_cases G hg _ _ hAB v with h | h
    · exact ⟨0, h.symm⟩
    · exact ⟨1, h.symm⟩
  refine ⟨{
    dart := Equiv.ofBijective dart ((Fintype.bijective_iff_surjective_and_card dart).mpr
      ⟨hD, by rw [Fintype.card_fin, card_darts G hg]⟩)
    vtx := Equiv.ofBijective vertex ((Fintype.bijective_iff_surjective_and_card vertex).mpr
      ⟨hV, by rw [Fintype.card_fin, card_vertices G hg]⟩)
    op_map := ?_
    vert_map := ?_ }⟩
  · intro k
    change G.op (dart k) = dart (smallOp k)
    fin_cases k <;> simp [dart, smallOp, G.op_invol, hOp, hOp']
  · intro k
    change G.vert (dart k) = vertex (dumbbellVert k)
    have hLoop' : G.vert (G.op ell) = G.vert ell := hLoop
    fin_cases k <;> simp [dart, vertex, dumbbellVert, hLoop', hq, hs, ht]

/-- Exhaustive classification from the actual graph: the alternatives
contain isomorphisms, not only cardinalities or matching invariants. -/
theorem classification : Nonempty (Iso dumbbell G) ∨ Nonempty (Iso theta G) := by
  by_cases hLoop : G.HasLoop
  · obtain ⟨ell, hEll⟩ := hLoop
    exact Or.inl (iso_dumbbell_of_loop G hg ell hEll)
  · exact Or.inr (iso_theta_of_no_loop G hg hLoop)

/-- Every actual connected cubic genus-two graph reaches the dumbbell. -/
theorem reachesIso_dumbbell : ReachesIso G dumbbell := by
  rcases classification G hg with h | h
  · obtain ⟨i⟩ := h
    exact ReachesIso.of_iso i.symm
  · obtain ⟨i⟩ := h
    exact (ReachesIso.of_iso i.symm).trans theta_reachesIso_dumbbell

/-- The base case in the same canonical family as the peel/plant induction. -/
theorem reachesIso_caterpillar : ReachesIso G (caterpillarDarts 2) :=
  reachesIso_dumbbell G hg

end GenusTwo

example : Nonempty (Iso dumbbell dumbbell) :=
  GenusTwo.iso_dumbbell_of_loop dumbbell dumbbell_genus 0 (by decide)

example : Nonempty (Iso theta theta) :=
  GenusTwo.iso_theta_of_no_loop theta theta_genus (by unfold HasLoop; decide)

example : ReachesIso theta (caterpillarDarts 2) :=
  GenusTwo.reachesIso_caterpillar theta theta_genus

end DraismaVargas.Infrastructure.CubicDarts

