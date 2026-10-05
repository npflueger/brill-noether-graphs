module

public import Utilities.CubicGraphs.CubicDarts

@[expose] public section

/-!
# Sliding planted lollipops and lifting Whitehead paths

This is the slide/lift step of the genus induction for Whitehead
connectivity, not the connectivity theorem itself (that is
`Utilities.CubicGraphs.WhiteheadConnectivity`).
Caporaso, *Geometry of tropical moduli spaces and linkage of graphs*,
Theorem 2.4.3 (arXiv:1001.2815v5), proves linkage for ordinary connected
regular multigraphs, with loops allowed; her Definition 2.1.3 requires the
contracted edge to be a non-loop. Her Hamiltonian-cycle/chord-twist proof
gives an independent route to the general theorem; here we use a genus
induction in the dart model instead.

Attachment sliding and lifting are also the graph-level mechanism in the
proof of Caporaso's Proposition 3.3.2, for attached legs. We verify the
corresponding planted-lollipop maps directly, including loops. In particular,
sliding *off* a loop needs a different transposition from the non-loop slide:
exchange the old third dart with the second subdivided-loop dart, not with the
lollipop bridge dart. The latter only exchanges the names of the old vertex
and the subdivision vertex.

The final finite example uses both slide and lift, taking two lollipops
planted on theta to the genus-four caterpillar.
-/

namespace DraismaVargas.Infrastructure
namespace CubicDarts

open Finset CubicDartGraph

/-! ## A four-cycle of darts -/

/-- The four-cycle `w ↦ x ↦ y ↦ z ↦ w`. -/
def cycle4 {α : Type*} [DecidableEq α] (w x y z : α) : Equiv.Perm α :=
  ((Equiv.swap w x).trans (Equiv.swap w y)).trans (Equiv.swap w z)

variable {α : Type*} [DecidableEq α] {w x y z : α}

@[simp] lemma cycle4_fst (hwx : w ≠ x) (hxy : x ≠ y) (hxz : x ≠ z) :
    cycle4 w x y z w = x := by
  simp only [cycle4, Equiv.trans_apply, Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hwx) hxy,
    Equiv.swap_apply_of_ne_of_ne (Ne.symm hwx) hxz]

@[simp] lemma cycle4_snd (hyw : y ≠ w) (hyz : y ≠ z) : cycle4 w x y z x = y := by
  simp only [cycle4, Equiv.trans_apply, Equiv.swap_apply_right, Equiv.swap_apply_left]
  rw [Equiv.swap_apply_of_ne_of_ne hyw hyz]

@[simp] lemma cycle4_thd (hyw : y ≠ w) (hyx : y ≠ x) : cycle4 w x y z y = z := by
  simp only [cycle4, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hyw hyx, Equiv.swap_apply_right, Equiv.swap_apply_left]

@[simp] lemma cycle4_fth (hzw : z ≠ w) (hzx : z ≠ x) (hzy : z ≠ y) :
    cycle4 w x y z z = w := by
  simp only [cycle4, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hzw hzx, Equiv.swap_apply_of_ne_of_ne hzw hzy,
    Equiv.swap_apply_right]

lemma cycle4_other {u : α} (huw : u ≠ w) (hux : u ≠ x) (huy : u ≠ y) (huz : u ≠ z) :
    cycle4 w x y z u = u := by
  simp only [cycle4, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne huw hux, Equiv.swap_apply_of_ne_of_ne huw huy,
    Equiv.swap_apply_of_ne_of_ne huw huz]

/-! ## The slide

A lollipop planted on an edge `e` can be slid onto any other edge meeting `e`, by a
single Whitehead move.  There are two cases, according to whether `e` is a loop; both
are treated here, and they need different moves (see `SlideLoopData`).
-/

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]

/-- Re-rooting `plant` at the other dart of the same edge. -/
def plantOpIso (G : CubicDartGraph D V) (d : D) :
    Iso (plant G d) (plant G (G.op d)) where
  dart := Equiv.swap (Sum.inr 0) (Sum.inr 1)
  vtx := Equiv.refl _
  op_map := by
    have hsw : ∀ x : D, (Equiv.swap (Sum.inr 0 : D ⊕ Fin 6) (Sum.inr 1)) (Sum.inl x)
        = Sum.inl x := fun x => Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
    have hsw2 : ∀ k : Fin 6, k ≠ 0 → k ≠ 1 →
        (Equiv.swap (Sum.inr 0 : D ⊕ Fin 6) (Sum.inr 1)) (Sum.inr k) = Sum.inr k :=
      fun k h0 h1 => Equiv.swap_apply_of_ne_of_ne (by simpa using h0) (by simpa using h1)
    have hdd : plantOp G (G.op d) (Sum.inl d) = Sum.inr 1 := by
      have h := plantOp_inl_op G (G.op d); rwa [G.op_invol] at h
    rintro (w | k) <;> simp only [plant_op]
    · rw [hsw]
      by_cases h1 : w = d
      · subst h1; rw [hdd, plantOp_inl_self, Equiv.swap_apply_left]
      by_cases h2 : w = G.op d
      · subst h2; rw [plantOp_inl_self, plantOp_inl_op, Equiv.swap_apply_right]
      · rw [plantOp_inl_of_ne G (G.op d) h2 (by rwa [G.op_invol]),
          plantOp_inl_of_ne G d h1 h2, hsw]
    · fin_cases k <;> simp [hsw, hsw2, G.op_invol]
  vert_map := by
    have hsw : ∀ x : D, (Equiv.swap (Sum.inr 0 : D ⊕ Fin 6) (Sum.inr 1)) (Sum.inl x)
        = Sum.inl x := fun x => Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)
    have hsw2 : ∀ k : Fin 6, k ≠ 0 → k ≠ 1 →
        (Equiv.swap (Sum.inr 0 : D ⊕ Fin 6) (Sum.inr 1)) (Sum.inr k) = Sum.inr k :=
      fun k h0 h1 => Equiv.swap_apply_of_ne_of_ne (by simpa using h0) (by simpa using h1)
    rintro (w | k) <;> simp only [plant_vert]
    · rw [hsw]; rfl
    · fin_cases k <;> simp [hsw2]

/-- The data for a slide at a **non-loop** edge.  `d` is a dart of the edge carrying the
planted lollipop, and `a`, `b` are the other two darts at `vert d`.  The slide moves the
lollipop from the edge of `d` onto the edge of `a`. -/
structure SlideData (G : CubicDartGraph D V) where
  /-- the dart of the edge currently carrying the lollipop -/
  d : D
  /-- the dart at `vert d` whose edge will carry the lollipop afterwards -/
  a : D
  /-- the remaining dart at `vert d` -/
  b : D
  nonloop : G.vert (G.op d) ≠ G.vert d
  a_vert : G.vert a = G.vert d
  b_vert : G.vert b = G.vert d
  a_ne : a ≠ d
  b_ne : b ≠ d
  ab : a ≠ b
  all : ∀ z : D, G.vert z = G.vert d → z = d ∨ z = a ∨ z = b

namespace SlideData

variable {G : CubicDartGraph D V} (s : SlideData G)

lemma a_ne_opd : s.a ≠ G.op s.d := fun h => s.nonloop (by rw [← h, s.a_vert])

lemma b_ne_opd : s.b ≠ G.op s.d := fun h => s.nonloop (by rw [← h, s.b_vert])

lemma d_ne_opd : s.d ≠ G.op s.d := Ne.symm (G.op_ne s.d)

lemma opa_ne_d : G.op s.a ≠ s.d := by
  intro h
  exact s.a_ne_opd (by rw [← h, G.op_invol])

lemma opa_ne_a : G.op s.a ≠ s.a := G.op_ne s.a

lemma opa_ne_opd : G.op s.a ≠ G.op s.d := fun h => s.a_ne (G.op_injective h)

lemma d_ne_opa : s.d ≠ G.op s.a := Ne.symm s.opa_ne_d

lemma vert_ne_of_not_mem {w : D} (h1 : w ≠ s.d) (h2 : w ≠ s.a) (h3 : w ≠ s.b) :
    G.vert w ≠ G.vert s.d := by
  intro h
  rcases s.all w h with h' | h' | h'
  exacts [h1 h', h2 h', h3 h']

/-- The Whitehead move realising the slide: at the edge joining `vert d` to the
subdivision point, exchange the dart `b` with the bridge dart of the lollipop. -/
def move : (plant G s.d).MoveData where
  base := Sum.inl s.d
  left := Sum.inl s.b
  right := Sum.inr 2
  nonloop := by simp
  left_vert := by simpa using s.b_vert
  left_ne := by simpa using s.b_ne
  right_vert := by simp
  right_ne := by simp

end SlideData

lemma fin6_cases : ∀ k : Fin 6, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by decide

namespace SlideData

variable {G : CubicDartGraph D V} (s : SlideData G)

@[simp] lemma move_base : s.move.base = Sum.inl s.d := rfl

@[simp] lemma move_left : s.move.left = Sum.inl s.b := rfl

@[simp] lemma move_right : s.move.right = (Sum.inr 2 : D ⊕ Fin 6) := rfl

/-- The dart bijection of the slide: the four-cycle
`inl d ↦ inr 0 ↦ inl a ↦ inr 1 ↦ inl d`. -/
def dartMap : (D ⊕ Fin 6) ≃ (D ⊕ Fin 6) :=
  cycle4 (Sum.inl s.d) (Sum.inr 0) (Sum.inl s.a) (Sum.inr 1)

lemma dartMap_d : s.dartMap (Sum.inl s.d) = Sum.inr 0 :=
  cycle4_fst (by simp) (by simp) (by simp)

lemma dartMap_r0 : s.dartMap (Sum.inr 0) = Sum.inl s.a :=
  cycle4_snd (by simpa using s.a_ne) (by simp)

lemma dartMap_a : s.dartMap (Sum.inl s.a) = Sum.inr 1 :=
  cycle4_thd (by simpa using s.a_ne) (by simp)

lemma dartMap_r1 : s.dartMap (Sum.inr 1) = Sum.inl s.d :=
  cycle4_fth (by simp) (by simp) (by simp)

lemma dartMap_inl {u : D} (h1 : u ≠ s.d) (h2 : u ≠ s.a) :
    s.dartMap (Sum.inl u) = Sum.inl u :=
  cycle4_other (by simpa using h1) (by simp) (by simpa using h2) (by simp)

lemma dartMap_inr {k : Fin 6} (h1 : k ≠ 0) (h2 : k ≠ 1) :
    s.dartMap (Sum.inr k) = Sum.inr k :=
  cycle4_other (by simp) (by simpa using h1) (by simp) (by simpa using h2)

/-- The vertex bijection of the slide: exchange `vert d` with the subdivision point. -/
def vtxMap : (V ⊕ Fin 2) ≃ (V ⊕ Fin 2) :=
  Equiv.swap (Sum.inl (G.vert s.d)) (Sum.inr 0)

lemma vtxMap_d : s.vtxMap (Sum.inl (G.vert s.d)) = Sum.inr 0 := Equiv.swap_apply_left _ _

lemma vtxMap_r0 : s.vtxMap (Sum.inr 0) = Sum.inl (G.vert s.d) := Equiv.swap_apply_right _ _

lemma vtxMap_r1 : s.vtxMap (Sum.inr 1) = Sum.inr 1 :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)

lemma vtxMap_inl {w : V} (h : w ≠ G.vert s.d) : s.vtxMap (Sum.inl w) = Sum.inl w :=
  Equiv.swap_apply_of_ne_of_ne (by simpa using h) (by simp)

lemma perm_b : s.move.perm (Sum.inl s.b) = Sum.inr 2 := Equiv.swap_apply_left _ _

lemma perm_r2 : s.move.perm (Sum.inr 2) = Sum.inl s.b := Equiv.swap_apply_right _ _

lemma perm_inl {u : D} (h : u ≠ s.b) : s.move.perm (Sum.inl u) = Sum.inl u :=
  Equiv.swap_apply_of_ne_of_ne (by simpa using h) (by simp)

lemma perm_inr {k : Fin 6} (h : k ≠ 2) : s.move.perm (Sum.inr k) = Sum.inr k :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using h)

/-- **The slide.**  One Whitehead move takes the lollipop planted on the (non-loop) edge
of `d` to the lollipop planted on the edge of `a`. -/
def iso : Iso ((plant G s.d).move s.move) (plant G s.a) where
  dart := s.dartMap
  vtx := s.vtxMap
  op_map := by
    intro z
    simp only [move_op, plant_op]
    rcases z with w | k
    · by_cases h1 : w = s.d
      · subst h1
        rw [s.dartMap_d, plantOp_inl_self, s.dartMap_r0]
        simp
      by_cases h2 : w = s.a
      · subst h2
        rw [s.dartMap_a, plantOp_inl_of_ne G s.d s.a_ne s.a_ne_opd,
          s.dartMap_inl s.opa_ne_d s.opa_ne_a]
        simp
      by_cases h3 : w = G.op s.d
      · subst h3
        rw [s.dartMap_inl (Ne.symm s.d_ne_opd) (Ne.symm s.a_ne_opd), plantOp_inl_op,
          s.dartMap_r1, plantOp_inl_of_ne G s.a (Ne.symm s.a_ne_opd)
            (Ne.symm s.opa_ne_opd), G.op_invol]
      by_cases h4 : w = G.op s.a
      · subst h4
        rw [s.dartMap_inl s.opa_ne_d s.opa_ne_a, plantOp_inl_op,
          plantOp_inl_of_ne G s.d s.opa_ne_d s.opa_ne_opd, G.op_invol, s.dartMap_a]
      · have k1 : G.op w ≠ s.d := fun h => h3 (by rw [← h, G.op_invol])
        have k2 : G.op w ≠ s.a := fun h => h4 (by rw [← h, G.op_invol])
        rw [s.dartMap_inl h1 h2, plantOp_inl_of_ne G s.a h2 h4,
          plantOp_inl_of_ne G s.d h1 h3, s.dartMap_inl k1 k2]
    · rcases fin6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [s.dartMap_r0, plantOp_inl_self]
        simp only [plantOp_inr, plantOpInr_zero]
        rw [s.dartMap_d]
      · rw [s.dartMap_r1, plantOp_inl_of_ne G s.a (Ne.symm s.a_ne) s.d_ne_opa]
        simp only [plantOp_inr, plantOpInr_one]
        rw [s.dartMap_inl (G.op_ne s.d) (Ne.symm s.a_ne_opd)]
      · rw [s.dartMap_inr (by decide) (by decide)]
        simp only [plantOp_inr, plantOpInr_two]
        rw [s.dartMap_inr (k := 3) (by decide) (by decide)]
      · rw [s.dartMap_inr (by decide) (by decide)]
        simp only [plantOp_inr, plantOpInr_three]
        rw [s.dartMap_inr (k := 2) (by decide) (by decide)]
      · rw [s.dartMap_inr (by decide) (by decide)]
        simp only [plantOp_inr, plantOpInr_four]
        rw [s.dartMap_inr (k := 5) (by decide) (by decide)]
      · rw [s.dartMap_inr (by decide) (by decide)]
        simp only [plantOp_inr, plantOpInr_five]
        rw [s.dartMap_inr (k := 4) (by decide) (by decide)]
  vert_map := by
    intro z
    simp only [move_vert, plant_vert]
    rcases z with w | k
    · by_cases h1 : w = s.d
      · subst h1
        rw [s.dartMap_d, s.perm_inl (Ne.symm s.b_ne)]
        simp only [plantVert_inl, plantVert_inr, plantVertInr_zero, s.vtxMap_d]
      by_cases h2 : w = s.a
      · subst h2
        rw [s.dartMap_a, s.perm_inl s.ab]
        simp only [plantVert_inl, plantVert_inr, plantVertInr_one, s.a_vert, s.vtxMap_d]
      by_cases h3 : w = s.b
      · subst h3
        rw [s.dartMap_inl s.b_ne (Ne.symm s.ab), s.perm_b]
        simp only [plantVert_inl, plantVert_inr, plantVertInr_two, s.b_vert, s.vtxMap_r0]
      · rw [s.dartMap_inl h1 h2, s.perm_inl h3]
        simp only [plantVert_inl]
        rw [s.vtxMap_inl (s.vert_ne_of_not_mem h1 h2 h3)]
    · rcases fin6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [s.dartMap_r0, s.perm_inr (by decide)]
        simp only [plantVert_inl, plantVert_inr, plantVertInr_zero, s.a_vert, s.vtxMap_r0]
      · rw [s.dartMap_r1, s.perm_inr (by decide)]
        simp only [plantVert_inl, plantVert_inr, plantVertInr_one, s.vtxMap_r0]
      · rw [s.dartMap_inr (by decide) (by decide), s.perm_r2]
        simp only [plantVert_inl, plantVert_inr, plantVertInr_two, s.b_vert, s.vtxMap_d]
      · rw [s.dartMap_inr (by decide) (by decide), s.perm_inr (by decide)]
        simp only [plantVert_inr, plantVertInr_three, s.vtxMap_r1]
      · rw [s.dartMap_inr (by decide) (by decide), s.perm_inr (by decide)]
        simp only [plantVert_inr, plantVertInr_four, s.vtxMap_r1]
      · rw [s.dartMap_inr (by decide) (by decide), s.perm_inr (by decide)]
        simp only [plantVert_inr, plantVertInr_five, s.vtxMap_r1]

/-- The slide as a reachability statement. -/
lemma reachesIso : ReachesIso (plant G s.d) (plant G s.a) :=
  ⟨(plant G s.d).move s.move, Reaches.move _ _, ⟨s.iso⟩⟩

end SlideData

/-! ### The slide across a loop

The move of the non-loop case does not slide the lollipop off a loop: when the edge
carrying the lollipop is a loop at `x`, exchanging the third dart at `x` with the
**bridge** dart of the lollipop returns an isomorphic copy of the same graph (the
roles of `x` and of the subdivision point are simply swapped).  The
move that does slide the lollipop off the loop exchanges the third dart at `x` with the
**other dart of the subdivided loop** (`inr 1` instead of `inr 2`); that is
`SlideLoopData.move` below. -/

/-- The data for a slide at a **loop** edge: the edge `{d, op d}` is a loop at `vert d`
and `b` is the third dart there.  The slide moves the lollipop from the loop onto the
edge of `b`. -/
structure SlideLoopData (G : CubicDartGraph D V) where
  /-- a dart of the loop carrying the lollipop -/
  d : D
  /-- the third dart at the vertex of the loop -/
  b : D
  loop : G.vert (G.op d) = G.vert d
  b_vert : G.vert b = G.vert d
  b_ne : b ≠ d
  b_ne_op : b ≠ G.op d
  all : ∀ z : D, G.vert z = G.vert d → z = d ∨ z = G.op d ∨ z = b

namespace SlideLoopData

variable {G : CubicDartGraph D V} (s : SlideLoopData G)

lemma opb_ne_d : G.op s.b ≠ s.d := by
  intro h
  exact s.b_ne_op (by rw [← h, G.op_invol])

lemma opb_ne_b : G.op s.b ≠ s.b := G.op_ne s.b

lemma opb_ne_opd : G.op s.b ≠ G.op s.d := fun h => s.b_ne (G.op_injective h)

lemma d_ne_opb : s.d ≠ G.op s.b := Ne.symm s.opb_ne_d

lemma opd_ne_opb : G.op s.d ≠ G.op s.b := Ne.symm s.opb_ne_opd

lemma vert_ne_of_not_mem {w : D} (h1 : w ≠ s.d) (h2 : w ≠ G.op s.d) (h3 : w ≠ s.b) :
    G.vert w ≠ G.vert s.d := by
  intro h
  rcases s.all w h with h' | h' | h'
  exacts [h1 h', h2 h', h3 h']

/-- The Whitehead move realising the slide off a loop: exchange the third dart at the
loop's vertex with the second dart of the subdivided loop. -/
def move : (plant G s.d).MoveData where
  base := Sum.inl s.d
  left := Sum.inl s.b
  right := Sum.inr 1
  nonloop := by simp
  left_vert := by simpa using s.b_vert
  left_ne := by simpa using s.b_ne
  right_vert := by simp
  right_ne := by simp

@[simp] lemma move_left : s.move.left = Sum.inl s.b := rfl

@[simp] lemma move_right : s.move.right = (Sum.inr 1 : D ⊕ Fin 6) := rfl

/-- The dart bijection: the four-cycle `inl d ↦ inl b ↦ inr 1 ↦ inl (op d) ↦ inl d`. -/
def dartMap : (D ⊕ Fin 6) ≃ (D ⊕ Fin 6) :=
  cycle4 (Sum.inl s.d) (Sum.inl s.b) (Sum.inr 1) (Sum.inl (G.op s.d))

lemma dartMap_d : s.dartMap (Sum.inl s.d) = Sum.inl s.b :=
  cycle4_fst (by simpa using Ne.symm s.b_ne) (by simp) (by simpa using s.b_ne_op)

lemma dartMap_b : s.dartMap (Sum.inl s.b) = Sum.inr 1 :=
  cycle4_snd (by simp) (by simp)

lemma dartMap_r1 : s.dartMap (Sum.inr 1) = Sum.inl (G.op s.d) :=
  cycle4_thd (by simp) (by simp)

lemma dartMap_opd : s.dartMap (Sum.inl (G.op s.d)) = Sum.inl s.d :=
  cycle4_fth (by simpa using G.op_ne s.d) (by simpa using Ne.symm s.b_ne_op) (by simp)

lemma dartMap_inl {u : D} (h1 : u ≠ s.d) (h2 : u ≠ s.b) (h3 : u ≠ G.op s.d) :
    s.dartMap (Sum.inl u) = Sum.inl u :=
  cycle4_other (by simpa using h1) (by simpa using h2) (by simp) (by simpa using h3)

lemma dartMap_inr {k : Fin 6} (h : k ≠ 1) : s.dartMap (Sum.inr k) = Sum.inr k :=
  cycle4_other (by simp) (by simp) (by simpa using h) (by simp)

lemma perm_b : s.move.perm (Sum.inl s.b) = Sum.inr 1 := Equiv.swap_apply_left _ _

lemma perm_r1 : s.move.perm (Sum.inr 1) = Sum.inl s.b := Equiv.swap_apply_right _ _

lemma perm_inl {u : D} (h : u ≠ s.b) : s.move.perm (Sum.inl u) = Sum.inl u :=
  Equiv.swap_apply_of_ne_of_ne (by simpa using h) (by simp)

lemma perm_inr {k : Fin 6} (h : k ≠ 1) : s.move.perm (Sum.inr k) = Sum.inr k :=
  Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using h)

/-- **The slide off a loop.**  One Whitehead move takes the lollipop planted on the loop
of `d` to the lollipop planted on the edge of the third dart `b`. -/
def iso : Iso ((plant G s.d).move s.move) (plant G s.b) where
  dart := s.dartMap
  vtx := Equiv.refl _
  op_map := by
    intro z
    simp only [move_op, plant_op]
    rcases z with w | k
    · by_cases h1 : w = s.d
      · subst h1
        rw [s.dartMap_d, plantOp_inl_self, plantOp_inl_self,
          s.dartMap_inr (by decide)]
      by_cases h2 : w = s.b
      · subst h2
        rw [s.dartMap_b, plantOp_inl_of_ne G s.d s.b_ne s.b_ne_op]
        simp only [plantOp_inr, plantOpInr_one]
        rw [s.dartMap_inl s.opb_ne_d s.opb_ne_b s.opb_ne_opd]
      by_cases h3 : w = G.op s.d
      · subst h3
        rw [s.dartMap_opd, plantOp_inl_op, s.dartMap_r1,
          plantOp_inl_of_ne G s.b (Ne.symm s.b_ne) s.d_ne_opb]
      by_cases h4 : w = G.op s.b
      · subst h4
        rw [s.dartMap_inl s.opb_ne_d s.opb_ne_b s.opb_ne_opd, plantOp_inl_op,
          plantOp_inl_of_ne G s.d s.opb_ne_d s.opb_ne_opd, G.op_invol, s.dartMap_b]
      · have k1 : G.op w ≠ s.d := fun h => h3 (by rw [← h, G.op_invol])
        have k2 : G.op w ≠ s.b := fun h => h4 (by rw [← h, G.op_invol])
        have k3 : G.op w ≠ G.op s.d := fun h => h1 (G.op_injective h)
        rw [s.dartMap_inl h1 h2 h3, plantOp_inl_of_ne G s.b h2 h4,
          plantOp_inl_of_ne G s.d h1 h3, s.dartMap_inl k1 k2 k3]
    · rcases fin6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [s.dartMap_inr (by decide)]
        simp only [plantOp_inr, plantOpInr_zero]
        rw [s.dartMap_d]
      · rw [s.dartMap_r1, plantOp_inl_of_ne G s.b (Ne.symm s.b_ne_op) s.opd_ne_opb]
        simp only [plantOp_inr, plantOpInr_one]
        rw [G.op_invol, s.dartMap_opd]
      · rw [s.dartMap_inr (by decide)]
        simp only [plantOp_inr, plantOpInr_two]
        rw [s.dartMap_inr (k := 3) (by decide)]
      · rw [s.dartMap_inr (by decide)]
        simp only [plantOp_inr, plantOpInr_three]
        rw [s.dartMap_inr (k := 2) (by decide)]
      · rw [s.dartMap_inr (by decide)]
        simp only [plantOp_inr, plantOpInr_four]
        rw [s.dartMap_inr (k := 5) (by decide)]
      · rw [s.dartMap_inr (by decide)]
        simp only [plantOp_inr, plantOpInr_five]
        rw [s.dartMap_inr (k := 4) (by decide)]
  vert_map := by
    intro z
    simp only [move_vert, plant_vert, Equiv.refl_apply]
    rcases z with w | k
    · by_cases h1 : w = s.d
      · subst h1
        rw [s.dartMap_d, s.perm_inl (Ne.symm s.b_ne)]
        simp only [plantVert_inl, s.b_vert]
      by_cases h2 : w = s.b
      · subst h2
        rw [s.dartMap_b, s.perm_b]
      by_cases h3 : w = G.op s.d
      · subst h3
        rw [s.dartMap_opd, s.perm_inl (Ne.symm s.b_ne_op)]
        simp only [plantVert_inl, s.loop]
      · rw [s.dartMap_inl h1 h2 h3, s.perm_inl h2]
    · rcases fin6_cases k with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [s.dartMap_inr (by decide), s.perm_inr (by decide)]
      · rw [s.dartMap_r1, s.perm_r1]
        simp only [plantVert_inl, s.loop, s.b_vert]
      · rw [s.dartMap_inr (by decide), s.perm_inr (by decide)]
      · rw [s.dartMap_inr (by decide), s.perm_inr (by decide)]
      · rw [s.dartMap_inr (by decide), s.perm_inr (by decide)]
      · rw [s.dartMap_inr (by decide), s.perm_inr (by decide)]

/-- The loop slide as a reachability statement. -/
lemma reachesIso : ReachesIso (plant G s.d) (plant G s.b) :=
  ⟨(plant G s.d).move s.move, Reaches.move _ _, ⟨s.iso⟩⟩

end SlideLoopData

/-! ## Sliding a lollipop to an arbitrary edge

Iterating the slide along a path of the connected graph moves the lollipop to **any**
edge.  Formally: the relation `d ↦ d'` given by "the lollipop planted
on the edge of `d` reaches the lollipop planted on the edge of `d'`" is an equivalence
relation containing both generators of the dart connectivity relation, hence is total.
-/

lemma reachesIso_plant_of_vert_eq (G : CubicDartGraph D V) {p q : D}
    (h : G.vert p = G.vert q) : ReachesIso (plant G p) (plant G q) := by
  by_cases hpq : p = q
  · subst hpq; exact ReachesIso.refl _
  by_cases hloop : G.vert (G.op p) = G.vert p
  · obtain ⟨r, hr, hr1, hr2, hall⟩ :=
      G.exists_third (x := G.vert p) rfl hloop (Ne.symm (G.op_ne p))
    rcases hall q h.symm with h' | h' | h'
    · exact absurd h'.symm hpq
    · subst h'; exact ReachesIso.of_iso (plantOpIso G p)
    · subst h'
      exact SlideLoopData.reachesIso ⟨p, q, hloop, hr, hr1, hr2, hall⟩
  · obtain ⟨r, hr, hr1, hr2, hall⟩ := G.exists_third (x := G.vert p) rfl h.symm hpq
    exact SlideData.reachesIso
      ⟨p, q, r, hloop, h.symm, hr, Ne.symm hpq, hr1, Ne.symm hr2, hall⟩

/-- **Slide to any edge.**  A planted lollipop can be moved to any edge of the graph by
a sequence of Whitehead moves. -/
theorem reachesIso_plant_any (G : CubicDartGraph D V) (d d' : D) :
    ReachesIso (plant G d) (plant G d') := by
  have key : ∀ p q : D, Relation.EqvGen (DartRel G.op G.vert) p q →
      ReachesIso (plant G p) (plant G q) := by
    intro p q h
    induction h with
    | rel a b hab =>
        rcases hab with hab | hab
        · subst hab; exact ReachesIso.of_iso (plantOpIso G a)
        · exact reachesIso_plant_of_vert_eq G hab
    | refl a => exact ReachesIso.refl _
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2
  exact key d d' (G.conn d d')

/-! ## Lifting a move across a planted lollipop

A Whitehead move of `G` at an edge other than the one carrying the lollipop is
verbatim a Whitehead move of `plant G d`; combined with the slide, *every* move of `G`
lifts. -/

omit [Fintype D] [Fintype V] [DecidableEq V] in
lemma swap_inl_inl {β : Type*} [DecidableEq β] (a b x : D) :
    Equiv.swap (Sum.inl a : D ⊕ β) (Sum.inl b) (Sum.inl x) = Sum.inl (Equiv.swap a b x) := by
  by_cases h1 : x = a
  · subst h1; simp
  by_cases h2 : x = b
  · subst h2; simp
  · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using h1) (by simpa using h2),
      Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- The lift of a Whitehead move of `G` to `plant G d`, when the move is not at the edge
carrying the lollipop. -/
def plantLift {G : CubicDartGraph D V} (m : G.MoveData) (d : D) (h1 : m.base ≠ d)
    (h2 : m.base ≠ G.op d) : (plant G d).MoveData where
  base := Sum.inl m.base
  left := Sum.inl m.left
  right := Sum.inl m.right
  nonloop := by
    simp only [plant_op, plant_vert, plantOp_inl_of_ne G d h1 h2, plantVert_inl]
    simpa using m.nonloop
  left_vert := by simp only [plant_vert, plantVert_inl, m.left_vert]
  left_ne := by simpa using m.left_ne
  right_vert := by
    simp only [plant_vert, plant_op, plantOp_inl_of_ne G d h1 h2, plantVert_inl, m.right_vert]
  right_ne := by
    simp only [plant_op, plantOp_inl_of_ne G d h1 h2]
    simpa using m.right_ne

/-- Planting commutes with a move away from the planted edge. -/
lemma plant_move_comm {G : CubicDartGraph D V} (m : G.MoveData) (d : D) (h1 : m.base ≠ d)
    (h2 : m.base ≠ G.op d) :
    (plant G d).move (plantLift m d h1 h2) = plant (G.move m) d := by
  refine CubicDartGraph.ext' rfl (funext ?_)
  rintro (x | k)
  · show plantVert G ((plantLift m d h1 h2).perm (Sum.inl x)) = plantVert (G.move m) (Sum.inl x)
    show plantVert G (Equiv.swap (Sum.inl m.left) (Sum.inl m.right) (Sum.inl x))
      = plantVert (G.move m) (Sum.inl x)
    rw [swap_inl_inl]
    rfl
  · show plantVert G ((plantLift m d h1 h2).perm (Sum.inr k)) = plantVert (G.move m) (Sum.inr k)
    show plantVert G (Equiv.swap (Sum.inl m.left) (Sum.inl m.right) (Sum.inr k))
      = plantVert (G.move m) (Sum.inr k)
    rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]
    rfl

variable {D' V' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']

/-- Planting commutes with isomorphism. -/
def isoPlant {G : CubicDartGraph D V} {H : CubicDartGraph D' V'} (i : Iso G H) (d : D) :
    Iso (plant G d) (plant H (i.dart d)) where
  dart := Equiv.sumCongr i.dart (Equiv.refl (Fin 6))
  vtx := Equiv.sumCongr i.vtx (Equiv.refl (Fin 2))
  op_map := by
    have hop : H.op (i.dart d) = i.dart (G.op d) := i.op_map d
    rintro (x | k) <;> simp only [plant_op, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply]
    · by_cases h1 : x = d
      · subst h1; rw [plantOp_inl_self, plantOp_inl_self]; rfl
      by_cases h2 : x = G.op d
      · subst h2
        rw [← hop, plantOp_inl_op, plantOp_inl_op]; rfl
      · rw [plantOp_inl_of_ne G d h1 h2,
          plantOp_inl_of_ne H (i.dart d) (fun h => h1 (i.dart.injective h))
            (by rw [hop]; exact fun h => h2 (i.dart.injective h)), i.op_map]
        rfl
    · rcases fin6_cases k with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [plantOp_inr, plantOpInr_zero, plantOpInr_one, plantOpInr_two,
          plantOpInr_three, plantOpInr_four, plantOpInr_five, Sum.map_inl, Sum.map_inr,
          Equiv.refl_apply, hop]
  vert_map := by
    rintro (x | k) <;> simp only [plant_vert, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply, plantVert_inl, plantVert_inr, i.vert_map]

/-- Two darts of a cubic dart graph never exhaust it. -/
lemma exists_ne_two (G : CubicDartGraph D V) (x y : D) : ∃ z : D, z ≠ x ∧ z ≠ y := by
  have hle : ({x, y} : Finset D).card ≤ 2 :=
    le_trans (Finset.card_insert_le _ _) (by simp)
  have h2 := G.card_darts
  have hV : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨G.vert x⟩
  have hne : (({x, y} : Finset D)ᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    omega
  obtain ⟨z, hz⟩ := hne
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hz
  exact ⟨z, hz.1, hz.2⟩

/-- **Lift of a single move.**  A Whitehead move of `G` becomes a sequence of Whitehead
moves of `plant G d`, for any placement of the lollipop before and after. -/
theorem lift_move {G H : CubicDartGraph D V} (h : Move G H) (d d' : D) :
    ReachesIso (plant G d) (plant H d') := by
  obtain ⟨m, rfl⟩ := h
  obtain ⟨d₁, k1, k2⟩ := exists_ne_two G m.base (G.op m.base)
  have hb1 : m.base ≠ d₁ := Ne.symm k1
  have hb2 : m.base ≠ G.op d₁ := fun hh => k2 (by rw [hh, G.op_invol])
  have step2 : ReachesIso (plant G d₁) (plant (G.move m) d₁) := by
    refine ReachesIso.of_reaches ?_
    rw [← plant_move_comm m d₁ hb1 hb2]
    exact Reaches.move _ _
  exact ((reachesIso_plant_any G d d₁).trans step2).trans (reachesIso_plant_any _ _ _)

/-- **Lift of a sequence of moves.** -/
theorem lift_reaches {G H : CubicDartGraph D V} (h : Reaches G H) (d d' : D) :
    ReachesIso (plant G d) (plant H d') := by
  induction h generalizing d' with
  | refl => exact reachesIso_plant_any G d d'
  | tail _ hbc ih => exact (ih d).trans (lift_move hbc d d')

/-- **Lift, up to isomorphism.** -/
theorem lift_reachesIso {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (h : ReachesIso G H) (d : D) (d' : D') : ReachesIso (plant G d) (plant H d') := by
  obtain ⟨K, hGK, ⟨i⟩⟩ := h
  refine (lift_reaches hGK d (i.dart.symm d')).trans ?_
  have hi := isoPlant i (i.dart.symm d')
  rw [Equiv.apply_symm_apply] at hi
  exact ReachesIso.of_iso hi

/-- Planting on any edge of a graph already linked to a caterpillar gives
the next caterpillar type. -/
theorem plant_reachesIso_caterpillar {G : CubicDartGraph D V} (m : ℕ)
    (h : ReachesIso G (caterpillar m)) (d : D) :
    ReachesIso (plant G d) (caterpillar (m + 1)) :=
  lift_reachesIso h d (lastSpine m)

/-- A concrete genus-four consumer: two arbitrarily placed lollipops on
theta reach the genus-four caterpillar by actual Whitehead moves. -/
theorem thetaTwoLollipops_reachesIso_caterpillar :
    ReachesIso thetaTwoLollipops (caterpillarDarts 4) :=
  plant_reachesIso_caterpillar 1
    (plant_reachesIso_caterpillar 0 theta_reachesIso_dumbbell 0) (Sum.inl 0)

end CubicDarts
end DraismaVargas.Infrastructure

