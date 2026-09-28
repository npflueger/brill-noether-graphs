import Utilities.CubicGraphs.CubicDarts
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Creating a loop by genuine Whitehead moves

This proves the loop-creation step of the cubic genus induction toward
Caporaso's ordinary linkage theorem (Theorem 2.4.3, arXiv:1001.2815v5).
It uses a direct cycle-shrinking construction, rather than formalizing
Caporaso's more general Hamiltonian argument.

The incoming graph supplies only its actual cubic dart structure and genus
at least two. Loops and parallel pairs are handled first. In the remaining
case its underlying simple graph is connected and cannot be a tree: a leaf
would force distinct darts in its cubic fibre to be parallel. A simple
cycle then lifts to actual dart occurrences; its trail property excludes
using both orientations of one occurrence.

One explicit non-loop Whitehead move shortens any nontrivial dart cycle by
one. In particular a genuine parallel pair becomes a loop. Iterating gives
`reaches_loop` on the original dart and vertex types, with no assumed cycle,
loop, graph isomorphism, or family membership.
-/

namespace DraismaVargas.Infrastructure.CubicDarts.WhiteheadLoop

open Finset CubicDartGraph

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- An actual cycle with `n+1` oriented edge occurrences. Indices outside
`0,...,n` are irrelevant. Distinctness is on vertices and on unoriented edges,
so the length-two case is a genuine parallel pair, not backtracking. -/
structure CycleData (G : CubicDartGraph D V) (n : ℕ) where
  dart : ℕ → D
  vertex_inj : ∀ i ≤ n, ∀ j ≤ n, G.vert (dart i) = G.vert (dart j) → i = j
  next : ∀ i < n, G.vert (G.op (dart i)) = G.vert (dart (i + 1))
  close : G.vert (G.op (dart n)) = G.vert (dart 0)
  edge_ne_op : ∀ i ≤ n, ∀ j ≤ n, dart i ≠ G.op (dart j)

namespace CycleData

variable {G : CubicDartGraph D V}

/-- Shrink one cycle edge by an actual non-loop Whitehead move. The same
formula takes a parallel pair to a loop when `n=0`. -/
theorem exists_shrink {n : ℕ} (C : CycleData G (n + 1)) :
    ∃ m : G.MoveData, Nonempty (CycleData (G.move m) n) := by
  have hNext := C.next 0 (by omega)
  have hNe : G.op (C.dart 0) ≠ C.dart 1 := (C.edge_ne_op 1 (by omega) 0 (by omega)).symm
  obtain ⟨r, hr, hr₀, hr₁, _⟩ := G.exists_third hNext rfl hNe
  let m : G.MoveData := {
    base := C.dart 0
    left := G.op (C.dart (n + 1))
    right := r
    nonloop := by
      intro h
      have := C.vertex_inj 1 (by omega) 0 (by omega) (hNext.symm.trans h)
      omega
    left_vert := C.close
    left_ne := (C.edge_ne_op 0 (by omega) (n + 1) le_rfl).symm
    right_vert := hr.trans hNext.symm
    right_ne := hr₀ }
  have hVert : ∀ i ≤ n, (G.move m).vert (C.dart (i + 1)) = G.vert (C.dart (i + 1)) := by
    intro i hi
    rw [move_vert, m.perm_of_ne (C.edge_ne_op (i + 1) (by omega) (n + 1) le_rfl) ?_]
    intro h
    have hIndex := C.vertex_inj (i + 1) (by omega) 1 (by omega)
      ((congrArg G.vert h).trans hr)
    rw [hIndex] at h
    exact hr₁ h.symm
  refine ⟨m, ⟨{
    dart := fun i ↦ C.dart (i + 1)
    vertex_inj := ?_
    next := ?_
    close := ?_
    edge_ne_op := ?_ }⟩⟩
  · intro i hi j hj h
    rw [hVert i hi, hVert j hj] at h
    have := C.vertex_inj (i + 1) (by omega) (j + 1) (by omega) h
    omega
  · intro i hi
    rw [hVert (i + 1) (by omega), move_op, move_vert]
    have hLeft : G.op (C.dart (i + 1)) ≠ m.left := by
      intro h
      have hd := G.op_injective h
      have := C.vertex_inj (i + 1) (by omega) (n + 1) le_rfl (congrArg G.vert hd)
      omega
    have hRight : G.op (C.dart (i + 1)) ≠ m.right := by
      intro h
      have hSame : G.vert (C.dart (i + 1 + 1)) = G.vert (C.dart 1) :=
        (C.next (i + 1) (by omega)).symm.trans ((congrArg G.vert h).trans hr)
      have := C.vertex_inj (i + 1 + 1) (by omega) 1 (by omega) hSame
      omega
    rw [m.perm_of_ne hLeft hRight]
    exact C.next (i + 1) (by omega)
  · rw [hVert 0 (by omega), move_op, move_vert]
    change G.vert (m.perm m.left) = G.vert (C.dart 1)
    rw [m.perm_left]
    exact hr
  · intro i hi j hj
    exact C.edge_ne_op (i + 1) (by omega) (j + 1) (by omega)

/-- Every actual finite cycle can be shortened to a loop. -/
theorem reaches_loop {n : ℕ} (C : CycleData G n) :
    ∃ H : CubicDartGraph D V, Reaches G H ∧ H.HasLoop := by
  induction n generalizing G with
  | zero => exact ⟨G, Reaches.refl G, C.dart 0, C.close⟩
  | succ n ih =>
    obtain ⟨m, ⟨C'⟩⟩ := C.exists_shrink
    obtain ⟨H, hReach, hLoop⟩ := ih C'
    exact ⟨H, (Reaches.move G m).trans hReach, hLoop⟩

end CycleData

/-- Parallel occurrences, with the same orientation at their endpoints. -/
def HasParallel (G : CubicDartGraph D V) : Prop :=
  ∃ p q : D, p ≠ q ∧ G.vert p = G.vert q ∧ G.vert (G.op p) = G.vert (G.op q)

theorem cycle_of_parallel (G : CubicDartGraph D V) (hNoLoop : ¬ G.HasLoop)
    (hParallel : HasParallel G) : Nonempty (CycleData G 1) := by
  obtain ⟨p, q, hpq, hpv, hopv⟩ := hParallel
  have hv : G.vert p ≠ G.vert (G.op q) := by
    intro h
    exact hNoLoop ⟨q, h.symm.trans hpv⟩
  refine ⟨{
    dart := fun i ↦ if i = 0 then p else G.op q
    vertex_inj := ?_
    next := ?_
    close := ?_
    edge_ne_op := ?_ }⟩
  · intro i hi j hj h
    interval_cases i <;> interval_cases j <;> norm_num at h ⊢
    · exact (hv h).elim
    · exact (hv h.symm).elim
  · intro i hi
    have : i = 0 := by omega
    subst i
    simpa using hopv
  · simpa using hpv.symm
  · intro i hi j hj
    interval_cases i <;> interval_cases j <;>
      simp only [ite_true, ite_false, one_ne_zero, G.op_invol]
    · exact (G.op_ne p).symm
    · exact hpq
    · exact fun h ↦ hpq (G.op_injective h).symm
    · exact G.op_ne q

/-- The underlying simple graph is used only to find an initial cycle
after loops and parallel occurrences have been handled separately. -/
def underlying (G : CubicDartGraph D V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ d : D, G.vert d = u ∧ G.vert (G.op d) = v
  symm := ⟨by
    intro u v h
    obtain ⟨hne, d, hd, hop⟩ := h
    exact ⟨hne.symm, G.op d, hop, by rw [G.op_invol]; exact hd⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

theorem vert_surjective (G : CubicDartGraph D V) : Function.Surjective G.vert := by
  intro v
  have h := G.card_fibre v
  have hNonempty : (univ.filter (fun d ↦ G.vert d = v)).Nonempty := by
    rw [← card_pos, h]; omega
  obtain ⟨d, hd⟩ := hNonempty
  exact ⟨d, (mem_filter.mp hd).2⟩

theorem underlying_connected (G : CubicDartGraph D V) (hNoLoop : ¬ G.HasLoop)
    [Nonempty V] : (underlying G).Connected := by
  refine ⟨?_⟩
  intro v w
  obtain ⟨p, rfl⟩ := vert_surjective G v
  obtain ⟨q, rfl⟩ := vert_surjective G w
  have key : ∀ x y, Relation.EqvGen (DartRel G.op G.vert) x y →
      (underlying G).Reachable (G.vert x) (G.vert y) := by
    intro x y h
    induction h with
    | rel x y hxy =>
      rcases hxy with hxy | hxy
      · subst y
        apply SimpleGraph.Adj.reachable
        exact ⟨fun h ↦ hNoLoop ⟨x, h.symm⟩, x, rfl, rfl⟩
      · exact hxy ▸ SimpleGraph.Reachable.refl _
    | refl x => exact SimpleGraph.Reachable.refl _
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact key p q (G.conn p q)

theorem underlying_has_cycle (G : CubicDartGraph D V) (hg : 2 ≤ G.genus)
    (hNoLoop : ¬ G.HasLoop) (hNoParallel : ¬ HasParallel G) :
    ∃ v : V, ∃ c : (underlying G).Walk v v, c.IsCycle := by
  classical
  have hCard := G.card_verts_add_two
  have hTwo : 1 < Fintype.card V := by omega
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp hTwo
  by_contra hNone
  have hAcyclic : (underlying G).IsAcyclic := by
    intro v c hc
    exact hNone ⟨v, c, hc⟩
  have hTree : (underlying G).IsTree := ⟨underlying_connected G hNoLoop, hAcyclic⟩
  obtain ⟨v, hv⟩ := hTree.exists_vert_degree_one_of_nontrivial
  obtain ⟨w, _, hUnique⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
  obtain ⟨p, q, r, hpq, _, _, hAll⟩ := card_eq_three.mp (G.card_fibre v)
  have hp : G.vert p = v := by
    have h : p ∈ univ.filter (fun d ↦ G.vert d = v) := by rw [hAll]; simp
    exact (mem_filter.mp h).2
  have hq : G.vert q = v := by
    have h : q ∈ univ.filter (fun d ↦ G.vert d = v) := by rw [hAll]; simp
    exact (mem_filter.mp h).2
  have hNeighbor : ∀ d, G.vert d = v → G.vert (G.op d) = w := by
    intro d hd
    apply hUnique
    exact ⟨fun h ↦ hNoLoop ⟨d, h.symm.trans hd.symm⟩, d, hd, rfl⟩
  exact hNoParallel ⟨p, q, hpq, hp.trans hq.symm, (hNeighbor p hp).trans (hNeighbor q hq).symm⟩

/-- Lift a simple cycle by choosing the actual dart occurrence witnessing
each adjacency. Its trail condition prevents opposite choices of one edge. -/
theorem cycle_of_simple_cycle (G : CubicDartGraph D V) {v : V}
    (c : (underlying G).Walk v v) (hc : c.IsCycle) :
    ∃ n : ℕ, Nonempty (CycleData G n) := by
  classical
  have hLength := hc.three_le_length
  have hAdj : ∀ i < c.length, ∃ d : D,
      G.vert d = c.getVert i ∧ G.vert (G.op d) = c.getVert (i + 1) := by
    intro i hi
    exact (c.adj_getVert_succ hi).2
  choose edge hSource hTarget using hAdj
  let dart : ℕ → D := fun i ↦ if h : i < c.length then edge i h else edge 0 (by omega)
  have hd : ∀ i, ∀ hi : i < c.length,
      G.vert (dart i) = c.getVert i ∧ G.vert (G.op (dart i)) = c.getVert (i + 1) := by
    intro i hi
    simp only [dart, dif_pos hi]
    exact ⟨hSource i hi, hTarget i hi⟩
  refine ⟨c.length - 1, ⟨{
    dart := dart
    vertex_inj := ?_
    next := ?_
    close := ?_
    edge_ne_op := ?_ }⟩⟩
  · intro i hi j hj h
    rw [(hd i (by omega)).1, (hd j (by omega)).1] at h
    exact hc.getVert_injOn' hi hj h
  · intro i hi
    rw [(hd i (by omega)).2, (hd (i + 1) (by omega)).1]
  · rw [(hd (c.length - 1) (by omega)).2, (hd 0 (by omega)).1,
      Nat.sub_add_cancel (by omega), c.getVert_length, c.getVert_zero]
  · intro i hi j hj h
    have hSourceEq : c.getVert i = c.getVert (j + 1) :=
      (hd i (by omega)).1.symm.trans ((congrArg G.vert h).trans (hd j (by omega)).2)
    have hTargetEq : c.getVert (i + 1) = c.getVert j := by
      have hop := congrArg G.op h
      rw [G.op_invol] at hop
      exact (hd i (by omega)).2.symm.trans ((congrArg G.vert hop).trans (hd j (by omega)).1)
    have hi' : i < c.edges.length := by rw [c.length_edges]; omega
    have hj' : j < c.edges.length := by rw [c.length_edges]; omega
    have hEdge : c.edges[i] = c.edges[j] := by
      rw [SimpleGraph.Walk.getElem_edges, SimpleGraph.Walk.getElem_edges,
        hSourceEq, hTargetEq]
      exact Sym2.eq_swap
    have hIndex := hc.isTrail.edges_nodup.getElem_inj_iff.mp hEdge
    subst j
    exact G.op_ne (dart i) h.symm

/-- Every actual cubic graph of genus at least two has an actual dart
cycle: a loop, a parallel pair, or a lifted simple cycle. -/
theorem exists_cycle (G : CubicDartGraph D V) (hg : 2 ≤ G.genus) :
    ∃ n : ℕ, Nonempty (CycleData G n) := by
  classical
  by_cases hLoop : G.HasLoop
  · obtain ⟨d, hd⟩ := hLoop
    refine ⟨0, ⟨{
      dart := fun _ ↦ d
      vertex_inj := by intros; omega
      next := by intros; omega
      close := hd
      edge_ne_op := by intros; exact (G.op_ne d).symm }⟩⟩
  by_cases hParallel : HasParallel G
  · exact ⟨1, cycle_of_parallel G hLoop hParallel⟩
  · obtain ⟨v, c, hc⟩ := underlying_has_cycle G hg hLoop hParallel
    exact cycle_of_simple_cycle G c hc

/-- Produce a loop by finitely many genuine non-loop Whitehead moves.
No cycle or loop witness is required from the incoming graph. -/
theorem reaches_loop (G : CubicDartGraph D V) (hg : 2 ≤ G.genus) :
    ∃ H : CubicDartGraph D V, Reaches G H ∧ H.HasLoop := by
  obtain ⟨n, ⟨C⟩⟩ := exists_cycle G hg
  exact C.reaches_loop

/-- The parallel-pair branch is inhabited by actual theta occurrences. -/
theorem theta_parallel_cycle : Nonempty (CycleData theta 1) :=
  cycle_of_parallel theta (by unfold HasLoop; decide)
    ⟨0, 2, by decide, by decide, by decide⟩

example : ∃ H : CubicDartGraph (Fin 6) (Fin 2), Reaches theta H ∧ H.HasLoop :=
  (Classical.choice theta_parallel_cycle).reaches_loop

end DraismaVargas.Infrastructure.CubicDarts.WhiteheadLoop

