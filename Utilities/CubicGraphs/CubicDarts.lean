import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# Trivalent genus-`g` types as dart graphs, and the Whitehead move

This is the model layer for the connectivity input of Vargas, Part II
(arXiv:2609.09109): the lemma that the tropical moduli space `M_g^trop` is
connected through codimension one (`lemma-tropM-connected-co1` there, citing
Caporaso).  Combinatorially, it says that any two trivalent genus-`g` types
are joined by a finite sequence of Whitehead moves.

A *cubic dart graph* of genus `g` is a set of `6g − 6` darts with a
fixed-point-free involution `σ` (edges = orbits) and a partition into `2g − 2`
triples (vertices); loops, parallel edges and bridges are allowed, and
connectedness is assumed.  Here the partition into triples is presented,
equivalently, by a vertex map `vert : D → V` all of whose fibres have exactly
three elements; this is the presentation that makes the Whitehead move a
one-line formula.

## The Whitehead move

The move at a non-loop edge `e = {d, op d}` joining `x ≠ y` deletes `e`, merges
`x ∪ y ∖ {d, op d}` into a four-dart vertex `{a, b, c, d'}`, and re-expands it
along one of the two other pairings.  On darts this is exactly an **exchange
of one dart of `x` with one dart of `y`**: if `a` is a dart at `x` other than `d` and
`c` is a dart at `y` other than `op d`, the re-expansion `{b, c} | {a, d'}` is
`vert ↦ vert ∘ (a c)`.  This is `CubicDartGraph.move`, and it makes three facts free:

* the darts and the edge involution are untouched, so `|E|`, `|V|` and hence the genus
  are preserved (`genus_move`);
* the fibres of the new vertex map are the images of the old fibres under a bijection,
  so trivalence is preserved;
* the move is undone by the move that exchanges the two darts back
  (`MoveData.reverse`, `move_reverse`), so `Reaches` is an equivalence relation
  (`Reaches.symm`).

Connectedness is the only property that takes an argument (`move`'s `conn` field): every
generating adjacency of `G` is recovered in `G.move m` by a detour across the contracted
edge.

## Contents

* `CubicDartGraph` — the model, with `genus`, `edgeCard` and Euler's relation `euler`;
* `MoveData`, `move`, `move_reverse`, `Move`, `Reaches`, `Iso`, `ReachesIso` — the move,
  its reversibility, and reachability (up to isomorphism, i.e. between *types*);
* `MoveData.swap`, `move_swap` — the same move read from the other end of the contracted
  edge (`base ↔ op base`, `left ↔ right`), which yields the very same graph;
* `plant` — hang a lollipop on an edge: subdivide `{d, op d}`, attach a bridge and a
  loop.  Six darts, two vertices and three edges are added, so `genus_plant`;
* `dumbbell`, `theta`, `thetaMove`, `thetaMoveIso` — the two genus-two types and the
  single Whitehead move joining them;
* `caterpillar`, `caterpillarDarts` — the caterpillar of loops `HCL_g` of
  Vargas, Part II (`def-caterpillar-loops`), built by planting `g - 2` lollipops
  one at a time on the last spine edge, starting from the dumbbell `HCL₂`;
* `exists_third`, `lollipop_of_loop` — the three darts at a vertex, and the fact that in
  a cubic graph every loop already sits on a lollipop.

The module imports only Mathlib: it is self-contained combinatorics.
-/

namespace DraismaVargas.Infrastructure
namespace CubicDarts

open Finset

/-! ## The dart model -/

/-- The generating adjacency relation on darts: two darts are directly related when
one is the edge-partner of the other, or when they sit at the same vertex. -/
def DartRel {D V : Type*} (op : D → D) (vert : D → V) : D → D → Prop :=
  fun p q => op p = q ∨ vert p = vert q

namespace DartRel

variable {D V : Type*} {op : D → D} {vert : D → V}

lemma of_op {p q : D} (h : op p = q) : Relation.EqvGen (DartRel op vert) p q :=
  Relation.EqvGen.rel _ _ (Or.inl h)

lemma of_vert {p q : D} (h : vert p = vert q) : Relation.EqvGen (DartRel op vert) p q :=
  Relation.EqvGen.rel _ _ (Or.inr h)

lemma symm {p q : D} (h : Relation.EqvGen (DartRel op vert) p q) :
    Relation.EqvGen (DartRel op vert) q p := Relation.EqvGen.symm _ _ h

lemma trans {p q r : D} (h : Relation.EqvGen (DartRel op vert) p q)
    (h' : Relation.EqvGen (DartRel op vert) q r) : Relation.EqvGen (DartRel op vert) p r :=
  Relation.EqvGen.trans _ _ _ h h'

/-- To see that a dart graph is connected it suffices to link every dart to one base dart. -/
lemma conn_of_forall_base (r : D) (h : ∀ p, Relation.EqvGen (DartRel op vert) p r) :
    ∀ p q : D, Relation.EqvGen (DartRel op vert) p q :=
  fun p q => trans (h p) (symm (h q))

/-- Transfer of connectivity to a second dart structure on the same darts: it suffices
that each generating relation of the first is witnessed in the second. -/
lemma conn_transfer {op' : D → D} {vert' : D → V}
    (hc : ∀ p q : D, Relation.EqvGen (DartRel op vert) p q)
    (hop : ∀ p : D, Relation.EqvGen (DartRel op' vert') p (op p))
    (hv : ∀ p q : D, vert p = vert q → Relation.EqvGen (DartRel op' vert') p q) :
    ∀ p q : D, Relation.EqvGen (DartRel op' vert') p q := by
  intro p q
  have h := hc p q
  induction h with
  | rel x y hxy =>
      rcases hxy with hxy | hxy
      · exact hxy ▸ hop x
      · exact hv x y hxy
  | refl x => exact Relation.EqvGen.refl x
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

end DartRel

/-- A **cubic dart graph**: a finite connected trivalent multigraph, presented by its
darts.  `op` is the edge involution (its orbits are the edges) and `vert` sends a dart
to the vertex it sits at; every vertex carries exactly three darts.  Loops (both darts
of an edge at the same vertex), parallel edges and bridges are all allowed. -/
structure CubicDartGraph (D V : Type*) [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] where
  /-- the edge involution on darts -/
  op : D → D
  /-- the vertex a dart sits at -/
  vert : D → V
  op_invol : ∀ d, op (op d) = d
  op_ne : ∀ d, op d ≠ d
  card_fibre : ∀ x : V, (univ.filter (fun d => vert d = x)).card = 3
  conn : ∀ p q : D, Relation.EqvGen (DartRel op vert) p q

namespace CubicDartGraph

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

lemma op_injective (G : CubicDartGraph D V) : Function.Injective G.op :=
  Function.Involutive.injective G.op_invol

@[simp] lemma op_op (G : CubicDartGraph D V) (d : D) : G.op (G.op d) = d := G.op_invol d

lemma op_eq_iff (G : CubicDartGraph D V) {p q : D} : G.op p = q ↔ p = G.op q := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/-- Two cubic dart graphs on the same darts and vertices with the same structure maps
are equal. -/
lemma ext' {G H : CubicDartGraph D V} (ho : G.op = H.op) (hv : G.vert = H.vert) : G = H := by
  cases G; cases H; cases ho; cases hv; rfl

/-! ### Counting: vertices, edges and the genus -/

/-- The number of edges: darts come in pairs. -/
def edgeCard (_G : CubicDartGraph D V) : ℕ := Fintype.card D / 2

/-- The genus `|E| - |V| + 1`; since the graph is trivalent this is `|V|/2 + 1`. -/
def genus (_G : CubicDartGraph D V) : ℕ := Fintype.card V / 2 + 1

lemma card_darts (G : CubicDartGraph D V) : Fintype.card D = 3 * Fintype.card V := by
  classical
  have h : (univ : Finset D).card = ∑ x : V, (univ.filter (fun d => G.vert d = x)).card :=
    Finset.card_eq_sum_card_fiberwise (fun d _ => mem_univ (G.vert d))
  have h2 : ∑ x : V, (univ.filter (fun d => G.vert d = x)).card = ∑ _x : V, 3 :=
    Finset.sum_congr rfl (fun x _ => G.card_fibre x)
  rw [h2, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm] at h
  rw [← Finset.card_univ]
  exact h

lemma even_card_darts (G : CubicDartGraph D V) : 2 ∣ Fintype.card D := by
  have h : ((Fintype.card D : ℕ) : ZMod 2) = 0 := by
    have : ∑ _d : D, (1 : ZMod 2) = 0 := by
      refine Finset.sum_involution (fun a _ => G.op a) (fun a _ => by decide)
        (fun a _ _ => G.op_ne a) (fun a _ => mem_univ _) (fun a _ => G.op_invol a)
    simpa using this
  exact (ZMod.natCast_eq_zero_iff _ 2).mp h

lemma even_card_verts (G : CubicDartGraph D V) : 2 ∣ Fintype.card V := by
  have h := G.even_card_darts
  rw [G.card_darts] at h
  omega

lemma card_verts_add_two (G : CubicDartGraph D V) :
    Fintype.card V + 2 = 2 * G.genus := by
  have h := G.even_card_verts
  unfold genus
  omega

lemma card_darts_add_six (G : CubicDartGraph D V) :
    Fintype.card D + 6 = 6 * G.genus := by
  have h := G.card_darts
  have h2 := G.card_verts_add_two
  omega

/-- Euler's relation `|E| + 1 = g + |V|`. -/
lemma euler (G : CubicDartGraph D V) :
    G.edgeCard + 1 = G.genus + Fintype.card V := by
  have h := G.card_darts
  have h2 := G.even_card_verts
  unfold edgeCard genus
  omega

/-! ### The Whitehead move -/

omit [DecidableEq D] in
lemma card_filter_comp_perm (e : Equiv.Perm D) (p : D → Prop) [DecidablePred p] :
    (univ.filter (fun d => p (e d))).card = (univ.filter p).card := by
  refine Finset.card_nbij' (fun d => e d) (fun d => e.symm d) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    exact hd
  · intro d hd
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    simpa using hd
  · intro d _; simp
  · intro d _; simp

/-- The data of a **Whitehead move** on `G`.  Contract the non-loop edge
`{base, op base}` to a four-valent vertex and re-expand it along one of the two other
pairings: equivalently, exchange a dart `left` at `vert base` (other than `base`) with
a dart `right` at `vert (op base)` (other than `op base`). -/
structure MoveData (G : CubicDartGraph D V) where
  /-- one dart of the contracted edge -/
  base : D
  /-- the dart at `vert base` that travels to the other end -/
  left : D
  /-- the dart at `vert (op base)` that travels to `vert base` -/
  right : D
  nonloop : G.vert (G.op base) ≠ G.vert base
  left_vert : G.vert left = G.vert base
  left_ne : left ≠ base
  right_vert : G.vert right = G.vert (G.op base)
  right_ne : right ≠ G.op base

namespace MoveData

variable {G : CubicDartGraph D V} (m : G.MoveData)

lemma base_ne_left : m.base ≠ m.left := fun h => m.left_ne h.symm

lemma base_ne_right : m.base ≠ m.right := by
  intro h
  exact m.nonloop (by rw [← m.right_vert, ← h])

lemma opBase_ne_left : G.op m.base ≠ m.left := by
  intro h
  exact m.nonloop (by rw [h, m.left_vert])

lemma opBase_ne_right : G.op m.base ≠ m.right := fun h => m.right_ne h.symm

lemma left_ne_right : m.left ≠ m.right := by
  intro h
  exact m.nonloop (by rw [← m.right_vert, ← h, m.left_vert])

/-- The transposition of darts realising the move. -/
def perm : Equiv.Perm D := Equiv.swap m.left m.right

@[simp] lemma perm_left : m.perm m.left = m.right := Equiv.swap_apply_left _ _

@[simp] lemma perm_right : m.perm m.right = m.left := Equiv.swap_apply_right _ _

@[simp] lemma perm_base : m.perm m.base = m.base :=
  Equiv.swap_apply_of_ne_of_ne m.base_ne_left m.base_ne_right

@[simp] lemma perm_opBase : m.perm (G.op m.base) = G.op m.base :=
  Equiv.swap_apply_of_ne_of_ne m.opBase_ne_left m.opBase_ne_right

lemma perm_of_ne {p : D} (h1 : p ≠ m.left) (h2 : p ≠ m.right) : m.perm p = p :=
  Equiv.swap_apply_of_ne_of_ne h1 h2

end MoveData

/-- The graph obtained from `G` by the Whitehead move `m`. -/
def move (G : CubicDartGraph D V) (m : G.MoveData) : CubicDartGraph D V where
  op := G.op
  vert := fun d => G.vert (m.perm d)
  op_invol := G.op_invol
  op_ne := G.op_ne
  card_fibre := fun x => by
    rw [card_filter_comp_perm m.perm (fun d => G.vert d = x)]
    exact G.card_fibre x
  conn := by
    refine DartRel.conn_transfer G.conn (fun p => DartRel.of_op rfl) ?_
    intro p q hpq
    have key : ∀ r : D, G.vert r = G.vert m.base →
        Relation.EqvGen (DartRel G.op (fun d => G.vert (m.perm d))) r m.base := by
      intro r hr
      by_cases hrl : r = m.left
      · subst hrl
        refine DartRel.trans (DartRel.of_vert ?_) (DartRel.of_op (G.op_invol m.base))
        show G.vert (m.perm m.left) = G.vert (m.perm (G.op m.base))
        rw [m.perm_left, m.perm_opBase, m.right_vert]
      · have hrr : r ≠ m.right := by
          intro h; subst h; exact m.nonloop (by rw [← m.right_vert, hr])
        refine DartRel.of_vert ?_
        show G.vert (m.perm r) = G.vert (m.perm m.base)
        rw [m.perm_of_ne hrl hrr, m.perm_base]; exact hr
    have key2 : ∀ r : D, G.vert r = G.vert (G.op m.base) →
        Relation.EqvGen (DartRel G.op (fun d => G.vert (m.perm d))) r (G.op m.base) := by
      intro r hr
      by_cases hrr : r = m.right
      · subst hrr
        refine DartRel.trans (DartRel.of_vert ?_) (DartRel.of_op rfl)
        show G.vert (m.perm m.right) = G.vert (m.perm m.base)
        rw [m.perm_right, m.perm_base, m.left_vert]
      · have hrl : r ≠ m.left := by
          intro h; subst h; exact m.nonloop (by rw [← hr, m.left_vert])
        refine DartRel.of_vert ?_
        show G.vert (m.perm r) = G.vert (m.perm (G.op m.base))
        rw [m.perm_of_ne hrl hrr, m.perm_opBase]; exact hr
    by_cases hX : G.vert p = G.vert m.base
    · exact DartRel.trans (key p hX) (DartRel.symm (key q (hpq ▸ hX)))
    by_cases hY : G.vert p = G.vert (G.op m.base)
    · exact DartRel.trans (key2 p hY) (DartRel.symm (key2 q (hpq ▸ hY)))
    · have hpl : p ≠ m.left := fun h => hX (h ▸ m.left_vert)
      have hpr : p ≠ m.right := fun h => hY (h ▸ m.right_vert)
      have hql : q ≠ m.left := fun h => hX (hpq.trans (h ▸ m.left_vert))
      have hqr : q ≠ m.right := fun h => hY (hpq.trans (h ▸ m.right_vert))
      refine DartRel.of_vert ?_
      show G.vert (m.perm p) = G.vert (m.perm q)
      rw [m.perm_of_ne hpl hpr, m.perm_of_ne hql hqr]; exact hpq

@[simp] lemma move_op (G : CubicDartGraph D V) (m : G.MoveData) : (G.move m).op = G.op := rfl

@[simp] lemma move_vert (G : CubicDartGraph D V) (m : G.MoveData) (d : D) :
    (G.move m).vert d = G.vert (m.perm d) := rfl

/-! ### Reversibility -/

/-- The Whitehead move that undoes `m`: exchange the two darts back. -/
def MoveData.reverse {G : CubicDartGraph D V} (m : G.MoveData) : (G.move m).MoveData where
  base := m.base
  left := m.right
  right := m.left
  nonloop := by
    show G.vert (m.perm (G.op m.base)) ≠ G.vert (m.perm m.base)
    rw [m.perm_opBase, m.perm_base]; exact m.nonloop
  left_vert := by
    show G.vert (m.perm m.right) = G.vert (m.perm m.base)
    rw [m.perm_right, m.perm_base]; exact m.left_vert
  left_ne := m.base_ne_right.symm
  right_vert := by
    show G.vert (m.perm m.left) = G.vert (m.perm (G.op m.base))
    rw [m.perm_left, m.perm_opBase]; exact m.right_vert
  right_ne := m.opBase_ne_left.symm

/-- A Whitehead move is undone by a Whitehead move. -/
lemma move_reverse (G : CubicDartGraph D V) (m : G.MoveData) :
    (G.move m).move m.reverse = G := by
  refine ext' rfl (funext fun d => ?_)
  show G.vert (m.perm (m.reverse.perm d)) = G.vert d
  have : m.reverse.perm = m.perm := by
    show Equiv.swap m.right m.left = Equiv.swap m.left m.right
    exact Equiv.swap_comm _ _
  rw [this]
  show G.vert (Equiv.swap m.left m.right (Equiv.swap m.left m.right d)) = G.vert d
  rw [Equiv.swap_apply_self]

/-! ### The move seen from the other end of the contracted edge -/

/-- The same Whitehead move described from the other end of the contracted edge:
exchange `base` with `op base` and, with them, `left` with `right`.  The two
descriptions carry the same dart transposition, so they produce the same graph
(`move_swap`). -/
def MoveData.swap {G : CubicDartGraph D V} (m : G.MoveData) : G.MoveData where
  base := G.op m.base
  left := m.right
  right := m.left
  nonloop := by rw [G.op_op]; exact m.nonloop.symm
  left_vert := m.right_vert
  left_ne := m.right_ne
  right_vert := by rw [G.op_op]; exact m.left_vert
  right_ne := by rw [G.op_op]; exact m.left_ne

@[simp] lemma MoveData.swap_base {G : CubicDartGraph D V} (m : G.MoveData) :
    m.swap.base = G.op m.base := rfl

@[simp] lemma MoveData.swap_left {G : CubicDartGraph D V} (m : G.MoveData) :
    m.swap.left = m.right := rfl

@[simp] lemma MoveData.swap_right {G : CubicDartGraph D V} (m : G.MoveData) :
    m.swap.right = m.left := rfl

/-- The transposition is symmetric, so both descriptions permute the darts alike. -/
@[simp] lemma MoveData.swap_perm {G : CubicDartGraph D V} (m : G.MoveData) :
    m.swap.perm = m.perm :=
  Equiv.swap_comm _ _

/-- **Both ends of the contracted edge prescribe the same Whitehead move.** -/
@[simp] lemma move_swap (G : CubicDartGraph D V) (m : G.MoveData) :
    G.move m.swap = G.move m := by
  refine ext' rfl (funext fun d => ?_)
  show G.vert (m.swap.perm d) = G.vert (m.perm d)
  rw [MoveData.swap_perm]

/-- Swapping twice returns the original move data. -/
@[simp] lemma MoveData.swap_swap {G : CubicDartGraph D V} (m : G.MoveData) :
    m.swap.swap = m := by
  cases m with
  | mk base left right _ _ _ _ _ =>
    simp only [MoveData.swap, G.op_op]

/-- `Move G H`: `H` arises from `G` by a single Whitehead move. -/
def Move (G H : CubicDartGraph D V) : Prop := ∃ m : G.MoveData, H = G.move m

lemma Move.symm {G H : CubicDartGraph D V} (h : Move G H) : Move H G := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m.reverse, (move_reverse G m).symm⟩

/-- Whitehead moves preserve the genus: they change neither the darts nor the vertices. -/
@[simp] lemma genus_move (G : CubicDartGraph D V) (m : G.MoveData) :
    (G.move m).genus = G.genus := rfl

lemma Move.genus_eq {G H : CubicDartGraph D V} (h : Move G H) : H.genus = G.genus := by
  obtain ⟨m, rfl⟩ := h; rfl

/-! ### Isomorphism -/

variable {D' V' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']
variable {D'' V'' : Type*} [Fintype D''] [DecidableEq D''] [Fintype V''] [DecidableEq V'']

/-- An isomorphism of cubic dart graphs: a bijection of darts and a bijection of
vertices intertwining the edge involution and the vertex map. -/
structure Iso (G : CubicDartGraph D V) (G' : CubicDartGraph D' V') where
  /-- the bijection on darts -/
  dart : D ≃ D'
  /-- the bijection on vertices -/
  vtx : V ≃ V'
  op_map : ∀ x, G'.op (dart x) = dart (G.op x)
  vert_map : ∀ x, G'.vert (dart x) = vtx (G.vert x)

namespace Iso

/-- The identity isomorphism. -/
def refl (G : CubicDartGraph D V) : Iso G G where
  dart := Equiv.refl D
  vtx := Equiv.refl V
  op_map := fun _ => rfl
  vert_map := fun _ => rfl

/-- The inverse isomorphism. -/
def symm {G : CubicDartGraph D V} {G' : CubicDartGraph D' V'} (i : Iso G G') : Iso G' G where
  dart := i.dart.symm
  vtx := i.vtx.symm
  op_map := fun x => by
    apply i.dart.injective
    rw [Equiv.apply_symm_apply, ← i.op_map, Equiv.apply_symm_apply]
  vert_map := fun x => by
    apply i.vtx.injective
    rw [Equiv.apply_symm_apply, ← i.vert_map, Equiv.apply_symm_apply]

/-- Composition of isomorphisms. -/
def trans {G : CubicDartGraph D V} {G' : CubicDartGraph D' V'} {G'' : CubicDartGraph D'' V''}
    (i : Iso G G') (j : Iso G' G'') : Iso G G'' where
  dart := i.dart.trans j.dart
  vtx := i.vtx.trans j.vtx
  op_map := fun x => by
    show G''.op (j.dart (i.dart x)) = j.dart (i.dart (G.op x))
    rw [j.op_map, i.op_map]
  vert_map := fun x => by
    show G''.vert (j.dart (i.dart x)) = j.vtx (i.vtx (G.vert x))
    rw [j.vert_map, i.vert_map]

lemma genus_eq {G : CubicDartGraph D V} {G' : CubicDartGraph D' V'} (i : Iso G G') :
    G'.genus = G.genus := by
  unfold genus
  rw [Fintype.card_congr i.vtx.symm]

end Iso

/-- A Whitehead move transports along an isomorphism. -/
def MoveData.transport {G : CubicDartGraph D V} {H : CubicDartGraph D' V'} (i : Iso G H)
    (m : G.MoveData) : H.MoveData where
  base := i.dart m.base
  left := i.dart m.left
  right := i.dart m.right
  nonloop := by
    rw [i.op_map, i.vert_map, i.vert_map]
    exact fun h => m.nonloop (i.vtx.injective h)
  left_vert := by rw [i.vert_map, i.vert_map, m.left_vert]
  left_ne := fun h => m.left_ne (i.dart.injective h)
  right_vert := by rw [i.vert_map, i.op_map, i.vert_map, m.right_vert]
  right_ne := by rw [i.op_map]; exact fun h => m.right_ne (i.dart.injective h)

/-- The transported move produces an isomorphic graph. -/
def Iso.move {G : CubicDartGraph D V} {H : CubicDartGraph D' V'} (i : Iso G H)
    (m : G.MoveData) : Iso (G.move m) (H.move (m.transport i)) where
  dart := i.dart
  vtx := i.vtx
  op_map := fun x => i.op_map x
  vert_map := fun x => by
    show H.vert ((m.transport i).perm (i.dart x)) = i.vtx (G.vert (m.perm x))
    have hp : (m.transport i).perm (i.dart x) = i.dart (m.perm x) := by
      show Equiv.swap (i.dart m.left) (i.dart m.right) (i.dart x)
        = i.dart (Equiv.swap m.left m.right x)
      by_cases h1 : x = m.left
      · subst h1; simp
      by_cases h2 : x = m.right
      · subst h2; simp
      · rw [Equiv.swap_apply_of_ne_of_ne (fun h => h1 (i.dart.injective h))
          (fun h => h2 (i.dart.injective h)), Equiv.swap_apply_of_ne_of_ne h1 h2]
    rw [hp, i.vert_map]

/-! ### Reachability -/

/-- `Reaches G H`: `H` is obtained from `G` by a finite sequence of Whitehead moves.
This is the reflexive-transitive closure of `Move`; because a Whitehead move is undone
by a Whitehead move it is in fact an equivalence relation. -/
def Reaches (G H : CubicDartGraph D V) : Prop := Relation.ReflTransGen Move G H

namespace Reaches

lemma refl (G : CubicDartGraph D V) : Reaches G G := Relation.ReflTransGen.refl

lemma single {G H : CubicDartGraph D V} (h : Move G H) : Reaches G H :=
  Relation.ReflTransGen.single h

lemma trans {G H K : CubicDartGraph D V} (h : Reaches G H) (h' : Reaches H K) :
    Reaches G K := Relation.ReflTransGen.trans h h'

lemma symm {G H : CubicDartGraph D V} (h : Reaches G H) : Reaches H G := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hbc.symm) ih

lemma move (G : CubicDartGraph D V) (m : G.MoveData) : Reaches G (G.move m) :=
  single ⟨m, rfl⟩

lemma genus_eq {G H : CubicDartGraph D V} (h : Reaches G H) : H.genus = G.genus := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => rw [hbc.genus_eq, ih]

/-- Reachability transports along an isomorphism. -/
lemma transport {G : CubicDartGraph D V} {H : CubicDartGraph D' V'} (i : Iso G H)
    {G' : CubicDartGraph D V} (h : Reaches G G') :
    ∃ H' : CubicDartGraph D' V', Reaches H H' ∧ Nonempty (Iso G' H') := by
  induction h with
  | refl => exact ⟨H, Relation.ReflTransGen.refl, ⟨i⟩⟩
  | tail _ hbc ih =>
      obtain ⟨H', hH', ⟨j⟩⟩ := ih
      obtain ⟨m, rfl⟩ := hbc
      exact ⟨H'.move (m.transport j), Relation.ReflTransGen.tail hH' ⟨_, rfl⟩, ⟨j.move m⟩⟩

end Reaches

/-- `ReachesIso G H`: a finite sequence of Whitehead moves takes `G` to a graph
isomorphic to `H`.  This is the relation "`G` and `H` are the same point of the
`M_g^trop` Whitehead graph", allowed to compare graphs on different dart sets. -/
def ReachesIso (G : CubicDartGraph D V) (H : CubicDartGraph D' V') : Prop :=
  ∃ K : CubicDartGraph D V, Reaches G K ∧ Nonempty (Iso K H)

namespace ReachesIso

lemma of_reaches {G H : CubicDartGraph D V} (h : Reaches G H) : ReachesIso G H :=
  ⟨H, h, ⟨Iso.refl H⟩⟩

lemma of_iso {G : CubicDartGraph D V} {H : CubicDartGraph D' V'} (i : Iso G H) :
    ReachesIso G H := ⟨G, Reaches.refl G, ⟨i⟩⟩

lemma refl (G : CubicDartGraph D V) : ReachesIso G G := of_reaches (Reaches.refl G)

lemma symm {G : CubicDartGraph D V} {H : CubicDartGraph D' V'} (h : ReachesIso G H) :
    ReachesIso H G := by
  obtain ⟨K, hGK, ⟨i⟩⟩ := h
  obtain ⟨H', hH', ⟨j⟩⟩ := Reaches.transport i hGK.symm
  exact ⟨H', hH', ⟨j.symm⟩⟩

lemma trans {G : CubicDartGraph D V} {H : CubicDartGraph D' V'} {J : CubicDartGraph D'' V''}
    (h : ReachesIso G H) (h' : ReachesIso H J) : ReachesIso G J := by
  obtain ⟨K, hGK, ⟨i⟩⟩ := h
  obtain ⟨L, hHL, ⟨j⟩⟩ := h'
  obtain ⟨K', hKK', ⟨k⟩⟩ := Reaches.transport i.symm hHL
  exact ⟨K', hGK.trans hKK', ⟨k.symm.trans j⟩⟩

lemma genus_eq {G : CubicDartGraph D V} {H : CubicDartGraph D' V'} (h : ReachesIso G H) :
    H.genus = G.genus := by
  obtain ⟨K, hGK, ⟨i⟩⟩ := h
  rw [i.genus_eq, hGK.genus_eq]

end ReachesIso

/-! ### Planting a lollipop on an edge

`plant G d` subdivides the edge `{d, op d}` of `G` by a new vertex `B`, and attaches to
`B` a bridge leading to a new vertex `A` carrying a loop.  Six darts and two vertices
are added, so three edges are added and the genus goes up by one.  The new darts are
indexed by `Fin 6`: `0` and `1` are the darts at `B` of the two halves of the
subdivided edge, `2` and `3` are the darts of the bridge (at `B` and at `A`), and
`4`, `5` are the two darts of the loop at `A`. -/

omit [DecidableEq V] in
lemma card_filter_sum {α β : Type*} [Fintype α] [Fintype β] (p : α ⊕ β → Prop)
    [DecidablePred p] :
    (univ.filter p).card = (univ.filter (fun a => p (Sum.inl a))).card
      + (univ.filter (fun b => p (Sum.inr b))).card := by
  simp only [Finset.card_filter]
  exact Fintype.sum_sum_type _

/-- The edge involution on the six new darts. -/
def plantOpInr (G : CubicDartGraph D V) (d : D) (k : Fin 6) : D ⊕ Fin 6 :=
  if k = 0 then Sum.inl d else if k = 1 then Sum.inl (G.op d)
  else if k = 2 then Sum.inr 3 else if k = 3 then Sum.inr 2
  else if k = 4 then Sum.inr 5 else Sum.inr 4

/-- The vertex of each of the six new darts: `0, 1, 2` at the subdivision point,
`3, 4, 5` at the lollipop vertex. -/
def plantVertInr (k : Fin 6) : Fin 2 := if (k : ℕ) < 3 then 0 else 1

/-- The edge involution of `plant G d`. -/
def plantOp (G : CubicDartGraph D V) (d : D) : D ⊕ Fin 6 → D ⊕ Fin 6 :=
  Sum.elim
    (fun x => if x = d then Sum.inr 0 else if x = G.op d then Sum.inr 1 else Sum.inl (G.op x))
    (plantOpInr G d)

/-- The vertex map of `plant G d`. -/
def plantVert (G : CubicDartGraph D V) : D ⊕ Fin 6 → V ⊕ Fin 2 :=
  Sum.elim (fun x => Sum.inl (G.vert x)) (fun k => Sum.inr (plantVertInr k))

lemma plantOp_inl (G : CubicDartGraph D V) (d x : D) :
    plantOp G d (Sum.inl x) =
      if x = d then Sum.inr 0 else if x = G.op d then Sum.inr 1 else Sum.inl (G.op x) := rfl

@[simp] lemma plantOp_inl_self (G : CubicDartGraph D V) (d : D) :
    plantOp G d (Sum.inl d) = Sum.inr 0 := by rw [plantOp_inl, if_pos rfl]

@[simp] lemma plantOp_inl_op (G : CubicDartGraph D V) (d : D) :
    plantOp G d (Sum.inl (G.op d)) = Sum.inr 1 := by
  rw [plantOp_inl, if_neg (G.op_ne d), if_pos rfl]

lemma plantOp_inl_of_ne (G : CubicDartGraph D V) (d : D) {x : D} (h1 : x ≠ d)
    (h2 : x ≠ G.op d) : plantOp G d (Sum.inl x) = Sum.inl (G.op x) := by
  rw [plantOp_inl, if_neg h1, if_neg h2]

@[simp] lemma plantOpInr_zero (G : CubicDartGraph D V) (d : D) :
    plantOpInr G d 0 = Sum.inl d := rfl

@[simp] lemma plantOpInr_one (G : CubicDartGraph D V) (d : D) :
    plantOpInr G d 1 = Sum.inl (G.op d) := rfl

@[simp] lemma plantOpInr_two (G : CubicDartGraph D V) (d : D) :
    plantOpInr G d 2 = Sum.inr 3 := rfl

@[simp] lemma plantOpInr_three (G : CubicDartGraph D V) (d : D) :
    plantOpInr G d 3 = Sum.inr 2 := rfl

@[simp] lemma plantOpInr_four (G : CubicDartGraph D V) (d : D) :
    plantOpInr G d 4 = Sum.inr 5 := rfl

@[simp] lemma plantOpInr_five (G : CubicDartGraph D V) (d : D) :
    plantOpInr G d 5 = Sum.inr 4 := rfl

@[simp] lemma plantVertInr_zero : plantVertInr 0 = 0 := rfl

@[simp] lemma plantVertInr_one : plantVertInr 1 = 0 := rfl

@[simp] lemma plantVertInr_two : plantVertInr 2 = 0 := rfl

@[simp] lemma plantVertInr_three : plantVertInr 3 = 1 := rfl

@[simp] lemma plantVertInr_four : plantVertInr 4 = 1 := rfl

@[simp] lemma plantVertInr_five : plantVertInr 5 = 1 := rfl

@[simp] lemma plantOp_inr (G : CubicDartGraph D V) (d : D) (k : Fin 6) :
    plantOp G d (Sum.inr k) = plantOpInr G d k := rfl

@[simp] lemma plantVert_inl (G : CubicDartGraph D V) (x : D) :
    plantVert G (Sum.inl x) = Sum.inl (G.vert x) := rfl

@[simp] lemma plantVert_inr (G : CubicDartGraph D V) (k : Fin 6) :
    plantVert G (Sum.inr k) = Sum.inr (plantVertInr k) := rfl

lemma plantOp_involutive (G : CubicDartGraph D V) (d : D) :
    ∀ z, plantOp G d (plantOp G d z) = z := by
  rintro (x | k)
  · by_cases h1 : x = d
    · subst h1; simp
    by_cases h2 : x = G.op d
    · subst h2; simp
    · have h3 : G.op x ≠ d := fun h => h2 (by rw [← h, G.op_invol])
      have h4 : G.op x ≠ G.op d := fun h => h1 (G.op_injective h)
      rw [plantOp_inl_of_ne G d h1 h2, plantOp_inl_of_ne G d h3 h4, G.op_invol]
  · fin_cases k <;> simp

lemma plantOp_ne (G : CubicDartGraph D V) (d : D) : ∀ z, plantOp G d z ≠ z := by
  rintro (x | k)
  · by_cases h1 : x = d
    · subst h1; simp
    by_cases h2 : x = G.op d
    · subst h2; simp
    · rw [plantOp_inl_of_ne G d h1 h2]; simpa using G.op_ne x
  · fin_cases k <;> simp

lemma plant_card_fibre (G : CubicDartGraph D V) (x : V ⊕ Fin 2) :
    (univ.filter (fun z : D ⊕ Fin 6 => plantVert G z = x)).card = 3 := by
  rw [card_filter_sum]
  match x with
  | Sum.inl w =>
      have h1 : (univ.filter (fun a : D => plantVert G (Sum.inl a) = Sum.inl w)).card = 3 := by
        simpa using G.card_fibre w
      have h2 : (univ.filter
          (fun k : Fin 6 => plantVert G (Sum.inr k) = (Sum.inl w : V ⊕ Fin 2))).card = 0 := by
        simp
      rw [h1, h2]
  | Sum.inr j =>
      have h1 : (univ.filter
          (fun a : D => plantVert G (Sum.inl a) = (Sum.inr j : V ⊕ Fin 2))).card = 0 := by
        simp
      have h2 : (univ.filter
          (fun k : Fin 6 => plantVert G (Sum.inr k) = (Sum.inr j : V ⊕ Fin 2))).card = 3 := by
        simp only [plantVert_inr, Sum.inr.injEq]
        fin_cases j <;> decide
      rw [h1, h2]

lemma plant_link_d (G : CubicDartGraph D V) (d : D) :
    Relation.EqvGen (DartRel (plantOp G d) (plantVert G)) (Sum.inl d) (Sum.inl (G.op d)) := by
  refine DartRel.trans (DartRel.of_op (show plantOp G d (Sum.inl d) = Sum.inr 0 by simp)) ?_
  refine DartRel.trans (DartRel.of_vert (show plantVert G (Sum.inr 0)
    = plantVert G (Sum.inr 1) by simp [plantVertInr])) ?_
  exact DartRel.of_op (show plantOp G d (Sum.inr 1) = Sum.inl (G.op d) by simp [plantOpInr])

lemma plant_link_inl_op (G : CubicDartGraph D V) (d x : D) :
    Relation.EqvGen (DartRel (plantOp G d) (plantVert G)) (Sum.inl x) (Sum.inl (G.op x)) := by
  by_cases h1 : x = d
  · subst h1; exact plant_link_d G x
  by_cases h2 : x = G.op d
  · subst h2
    rw [G.op_invol]
    exact DartRel.symm (plant_link_d G d)
  · exact DartRel.of_op (plantOp_inl_of_ne G d h1 h2)

lemma plant_conn_inl (G : CubicDartGraph D V) (d : D) : ∀ x y : D,
    Relation.EqvGen (DartRel (plantOp G d) (plantVert G)) (Sum.inl x) (Sum.inl y) := by
  intro x y
  have h := G.conn x y
  induction h with
  | rel a b hab =>
      rcases hab with hab | hab
      · exact hab ▸ plant_link_inl_op G d a
      · exact DartRel.of_vert (by simp [hab])
  | refl a => exact Relation.EqvGen.refl _
  | symm a b _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

lemma plant_conn (G : CubicDartGraph D V) (d : D) : ∀ p q : D ⊕ Fin 6,
    Relation.EqvGen (DartRel (plantOp G d) (plantVert G)) p q := by
  refine DartRel.conn_of_forall_base (Sum.inl d) ?_
  have h0 : Relation.EqvGen (DartRel (plantOp G d) (plantVert G)) (Sum.inr 0) (Sum.inl d) :=
    DartRel.of_op (by simp [plantOpInr])
  have h2 : Relation.EqvGen (DartRel (plantOp G d) (plantVert G)) (Sum.inr 2) (Sum.inl d) :=
    DartRel.trans (DartRel.of_vert (by simp [plantVertInr])) h0
  have h3 : Relation.EqvGen (DartRel (plantOp G d) (plantVert G)) (Sum.inr 3) (Sum.inl d) :=
    DartRel.trans (DartRel.of_op (show plantOp G d (Sum.inr 3) = Sum.inr 2 by
      simp [plantOpInr])) h2
  rintro (x | k)
  · exact plant_conn_inl G d x d
  · fin_cases k
    · exact h0
    · exact DartRel.trans (DartRel.of_vert (by simp [plantVertInr])) h0
    · exact h2
    · exact h3
    · exact DartRel.trans (DartRel.of_vert (by simp [plantVertInr])) h3
    · exact DartRel.trans (DartRel.of_op (show plantOp G d (Sum.inr 5) = Sum.inr 4 by
        simp [plantOpInr])) (DartRel.trans (DartRel.of_vert (by simp [plantVertInr])) h3)

/-- **Planting a lollipop.**  `plant G d` subdivides the edge `{d, op d}` and hangs a
loop-plus-bridge (a lollipop) at the subdivision point. -/
def plant (G : CubicDartGraph D V) (d : D) : CubicDartGraph (D ⊕ Fin 6) (V ⊕ Fin 2) where
  op := plantOp G d
  vert := plantVert G
  op_invol := plantOp_involutive G d
  op_ne := plantOp_ne G d
  card_fibre := plant_card_fibre G
  conn := plant_conn G d

@[simp] lemma plant_op (G : CubicDartGraph D V) (d : D) : (plant G d).op = plantOp G d := rfl

@[simp] lemma plant_vert (G : CubicDartGraph D V) (d : D) : (plant G d).vert = plantVert G := rfl

/-- Planting a lollipop raises the genus by one. -/
lemma genus_plant (G : CubicDartGraph D V) (d : D) : (plant G d).genus = G.genus + 1 := by
  show Fintype.card (V ⊕ Fin 2) / 2 + 1 = Fintype.card V / 2 + 1 + 1
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

/-! ### The three darts at a vertex -/

/-- Given two distinct darts at a vertex, there is a unique third one, and those are
all the darts at that vertex. -/
lemma exists_third (G : CubicDartGraph D V) {x : V} {p q : D} (hp : G.vert p = x)
    (hq : G.vert q = x) (hpq : p ≠ q) :
    ∃ r : D, G.vert r = x ∧ r ≠ p ∧ r ≠ q ∧ ∀ z : D, G.vert z = x → z = p ∨ z = q ∨ z = r := by
  classical
  have hsub : ({p, q} : Finset D) ⊆ univ.filter (fun d => G.vert d = x) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [hp, hq]
  have hpair : ({p, q} : Finset D).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using hpq), Finset.card_singleton]
  have hinter : (({p, q} : Finset D) ∩ (univ.filter (fun d => G.vert d = x)))
      = ({p, q} : Finset D) := Finset.inter_eq_left.mpr hsub
  have hcard : ((univ.filter (fun d => G.vert d = x)) \ ({p, q} : Finset D)).card = 1 := by
    rw [Finset.card_sdiff, hinter, G.card_fibre, hpair]
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
  have hrmem : r ∈ (univ.filter (fun d => G.vert d = x)) \ ({p, q} : Finset D) := by
    rw [hr]; exact Finset.mem_singleton_self r
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, not_or] at hrmem
  refine ⟨r, hrmem.1, hrmem.2.1, hrmem.2.2, fun z hz => ?_⟩
  by_cases h1 : z = p
  · exact Or.inl h1
  by_cases h2 : z = q
  · exact Or.inr (Or.inl h2)
  · refine Or.inr (Or.inr ?_)
    have : z ∈ (univ.filter (fun d => G.vert d = x)) \ ({p, q} : Finset D) := by
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hz, h1, h2⟩
    rw [hr] at this
    simpa using this

/-- A dart whose edge is a loop. -/
def IsLoopDart (G : CubicDartGraph D V) (d : D) : Prop := G.vert (G.op d) = G.vert d

instance (G : CubicDartGraph D V) (d : D) : Decidable (G.IsLoopDart d) :=
  inferInstanceAs (Decidable (_ = _))

/-- `G` carries a loop.  In a cubic graph a loop is automatically a lollipop: the third
dart at the vertex of the loop leads to a different vertex. -/
def HasLoop (G : CubicDartGraph D V) : Prop := ∃ d : D, G.IsLoopDart d

/-- The two darts of a loop, together with the third dart at that vertex, exhaust the
vertex; and the third dart leads elsewhere, so a loop always sits on a lollipop. -/
lemma lollipop_of_loop (G : CubicDartGraph D V) {d : D} (hd : G.IsLoopDart d) :
    ∃ q : D, G.vert q = G.vert d ∧ q ≠ d ∧ q ≠ G.op d ∧ G.vert (G.op q) ≠ G.vert q := by
  obtain ⟨q, hq, hq1, hq2, hall⟩ :=
    G.exists_third (x := G.vert d) rfl hd (Ne.symm (G.op_ne d))
  refine ⟨q, hq, hq1, hq2, ?_⟩
  intro hloop
  have := hall (G.op q) (by rw [hloop, hq])
  rcases this with h | h | h
  · exact hq2 (by have h2 := congrArg G.op h; rwa [G.op_invol] at h2)
  · exact hq1 (G.op_injective h)
  · exact G.op_ne q h

end CubicDartGraph
open CubicDartGraph

/-! ## Explicit small graphs

The two trivalent genus-two types: the theta graph and the dumbbell.  The dumbbell is
the caterpillar of loops `HCL₂`. -/

/-- The edge involution of the genus-two graphs on six darts: `0↔1`, `2↔3`, `4↔5`. -/
def smallOp : Fin 6 → Fin 6 := ![1, 0, 3, 2, 5, 4]

/-- Vertex map of the dumbbell: a loop `{0,1}` at vertex `0`, the bridge `{2,3}`, and a
loop `{4,5}` at vertex `1`. -/
def dumbbellVert : Fin 6 → Fin 2 := ![0, 0, 0, 1, 1, 1]

/-- Vertex map of the theta graph: all three edges join the two vertices. -/
def thetaVert : Fin 6 → Fin 2 := ![0, 1, 0, 1, 0, 1]

/-- The **dumbbell**: two loops joined by a bridge.  This is the caterpillar of loops
`HCL₂`, the genus-two base case of the connectivity induction. -/
def dumbbell : CubicDartGraph (Fin 6) (Fin 2) where
  op := smallOp
  vert := dumbbellVert
  op_invol := by decide
  op_ne := by decide
  card_fibre := by decide
  conn := by
    refine DartRel.conn_of_forall_base 0 ?_
    have h2 : Relation.EqvGen (DartRel smallOp dumbbellVert) 2 0 :=
      DartRel.of_vert (by decide)
    have h3 : Relation.EqvGen (DartRel smallOp dumbbellVert) 3 0 :=
      DartRel.trans (DartRel.of_op (by decide)) h2
    have h4 : Relation.EqvGen (DartRel smallOp dumbbellVert) 4 0 :=
      DartRel.trans (DartRel.of_vert (by decide)) h3
    intro p
    fin_cases p
    · exact Relation.EqvGen.refl _
    · exact DartRel.of_op (by decide)
    · exact h2
    · exact h3
    · exact h4
    · exact DartRel.trans (DartRel.of_op (by decide)) h4

/-- The **theta graph**: two vertices joined by three parallel edges. -/
def theta : CubicDartGraph (Fin 6) (Fin 2) where
  op := smallOp
  vert := thetaVert
  op_invol := by decide
  op_ne := by decide
  card_fibre := by decide
  conn := by
    refine DartRel.conn_of_forall_base 0 ?_
    have h1 : Relation.EqvGen (DartRel smallOp thetaVert) 1 0 :=
      DartRel.of_op (by decide)
    intro p
    fin_cases p
    · exact Relation.EqvGen.refl _
    · exact h1
    · exact DartRel.of_vert (by decide)
    · exact DartRel.trans (DartRel.of_vert (by decide)) h1
    · exact DartRel.of_vert (by decide)
    · exact DartRel.trans (DartRel.of_vert (by decide)) h1

@[simp] lemma dumbbell_genus : dumbbell.genus = 2 := by decide

@[simp] lemma theta_genus : theta.genus = 2 := by decide

/-- The Whitehead move that turns the theta graph into the dumbbell: contract the edge
`{0,1}` and re-pair `{2,5}` against `{3,4}`. -/
def thetaMove : theta.MoveData where
  base := 0
  left := 2
  right := 5
  nonloop := by decide
  left_vert := by decide
  left_ne := by decide
  right_vert := by decide
  right_ne := by decide

/-- One Whitehead move takes the theta graph to the dumbbell. -/
def thetaMoveIso : Iso (theta.move thetaMove) dumbbell where
  dart := Equiv.addRight (2 : Fin 6)
  vtx := Equiv.refl (Fin 2)
  op_map := by decide
  vert_map := by decide

/-- The theta graph reaches the caterpillar `HCL₂`. -/
lemma theta_reachesIso_dumbbell : ReachesIso theta dumbbell :=
  ⟨theta.move thetaMove, Reaches.move theta thetaMove, ⟨thetaMoveIso⟩⟩

/-! ## The caterpillar of loops

`HCL_g` (Vargas, Part II, `def-caterpillar-loops`) is the graph obtained from a
path `A₁ h₁ B₂ h₂ … B_{g-1} h_{g-1} A_g` by attaching a self-loop at each of `A₁` and
`A_g` and a lollipop (a bridge to a new vertex carrying a loop) at each interior vertex
`B_i`.  Writing `g = m + 2`, it is built here by planting `m` lollipops, one at a time,
on the last spine edge of the previous caterpillar, starting from the dumbbell
`HCL₂`. -/

/-- The darts of the caterpillar of loops of genus `m + 2`. -/
def CatD : ℕ → Type
  | 0 => Fin 6
  | (m + 1) => CatD m ⊕ Fin 6

/-- The vertices of the caterpillar of loops of genus `m + 2`. -/
def CatV : ℕ → Type
  | 0 => Fin 2
  | (m + 1) => CatV m ⊕ Fin 2

instance instFintypeCatD : (m : ℕ) → Fintype (CatD m)
  | 0 => inferInstanceAs (Fintype (Fin 6))
  | (m + 1) => letI := instFintypeCatD m; inferInstanceAs (Fintype (CatD m ⊕ Fin 6))

instance instDecidableEqCatD : (m : ℕ) → DecidableEq (CatD m)
  | 0 => inferInstanceAs (DecidableEq (Fin 6))
  | (m + 1) => letI := instDecidableEqCatD m; inferInstanceAs (DecidableEq (CatD m ⊕ Fin 6))

instance instFintypeCatV : (m : ℕ) → Fintype (CatV m)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | (m + 1) => letI := instFintypeCatV m; inferInstanceAs (Fintype (CatV m ⊕ Fin 2))

instance instDecidableEqCatV : (m : ℕ) → DecidableEq (CatV m)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | (m + 1) => letI := instDecidableEqCatV m; inferInstanceAs (DecidableEq (CatV m ⊕ Fin 2))

/-- The dart of the last spine edge sitting at the end vertex `A_g`. -/
def lastSpine : (m : ℕ) → CatD m
  | 0 => (3 : Fin 6)
  | (m + 1) => Sum.inl (lastSpine m)

/-- The **caterpillar of loops** `HCL_{m+2}`. -/
def caterpillar : (m : ℕ) → CubicDartGraph (CatD m) (CatV m)
  | 0 => dumbbell
  | (m + 1) => plant (caterpillar m) (lastSpine m)

@[simp] lemma caterpillar_zero : caterpillar 0 = dumbbell := rfl

lemma caterpillar_succ (m : ℕ) :
    caterpillar (m + 1) = plant (caterpillar m) (lastSpine m) := rfl

/-- The caterpillar of genus `m + 3` *is* a lollipop planted on the caterpillar of
genus `m + 2`, on its last spine edge. -/
def caterpillarSuccIso (m : ℕ) :
    Iso (plant (caterpillar m) (lastSpine m)) (caterpillar (m + 1)) :=
  Iso.refl _

lemma card_catD (m : ℕ) : Fintype.card (CatD m) = 6 * m + 6 := by
  induction m with
  | zero => rfl
  | succ n ih =>
      show Fintype.card (CatD n ⊕ Fin 6) = _
      rw [Fintype.card_sum, ih, Fintype.card_fin]; ring

lemma card_catV (m : ℕ) : Fintype.card (CatV m) = 2 * m + 2 := by
  induction m with
  | zero => rfl
  | succ n ih =>
      show Fintype.card (CatV n ⊕ Fin 2) = _
      rw [Fintype.card_sum, ih, Fintype.card_fin]; ring

/-- The caterpillar of loops `HCL_{m+2}` has genus `m + 2`. -/
@[simp] lemma genus_caterpillar (m : ℕ) : (caterpillar m).genus = m + 2 := by
  show Fintype.card (CatV m) / 2 + 1 = m + 2
  rw [card_catV]
  omega

/-- The **caterpillar of genus `g`**, for `g ≥ 2`. -/
def caterpillarDarts (g : ℕ) : CubicDartGraph (CatD (g - 2)) (CatV (g - 2)) :=
  caterpillar (g - 2)

@[simp] lemma genus_caterpillarDarts {g : ℕ} (hg : 2 ≤ g) :
    (caterpillarDarts g).genus = g := by
  unfold caterpillarDarts
  rw [genus_caterpillar]
  omega

/-! ## Non-vacuity -/

example : (caterpillarDarts 2).genus = 2 := genus_caterpillarDarts (by norm_num)

example : (caterpillarDarts 4).genus = 4 := genus_caterpillarDarts (by norm_num)

example : caterpillarDarts 2 = dumbbell := rfl

example : Fintype.card (CatD 2) = 18 := card_catD 2

example : Fintype.card (CatV 2) = 6 := card_catV 2

/-- A genus-four trivalent type that is **not** a caterpillar of loops: two lollipops
planted on the theta graph. -/
def thetaTwoLollipops : CubicDartGraph ((Fin 6 ⊕ Fin 6) ⊕ Fin 6) ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) :=
  plant (plant theta 0) (Sum.inl 0)

example : thetaTwoLollipops.genus = 4 := by
  show (plant (plant theta 0) (Sum.inl 0)).genus = 4
  rw [genus_plant, genus_plant, theta_genus]

/-- The genus-three caterpillar `HCL₃`: a chain of three loops. -/
example : (caterpillarDarts 3).genus = 3 := genus_caterpillarDarts (by norm_num)

end CubicDarts
end DraismaVargas.Infrastructure
