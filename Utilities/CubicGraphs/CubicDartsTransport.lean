import Utilities.CubicGraphs.CubicDarts

/-!
# Transporting a Whitehead move backwards along an isomorphism

Context: when a tropical morphism is carried across a wall at which the
combinatorial type of its source changes (Vargas, Part II, arXiv:2609.09109,
the section `sec-constructions` on changing combinatorial type; see also
Draisma--Vargas Part I, arXiv:1909.12924, the subsection on properties
inherited by limits, where an isomorphism of gluing datums induces an
isomorphism of their graphs), the type change is recorded as a Whitehead move
of a fixed *ambient* graph, while the morphism comes with its own stable
graph, which is only isomorphic to the ambient one.

`Utilities.CubicGraphs.CubicDarts` has `CubicDartGraph.MoveData.transport i m`,
which pushes a move forward along `i : Iso G H`, and
`CubicDartGraph.Iso.move i m : Iso (G.move m) (H.move (m.transport i))`.  This
file supplies the *opposite* bookkeeping: the Whitehead move `m` lives on the
ambient graph `H`, the stable graph `G` is only isomorphic to it, and the
object that has to be produced is an isomorphism onto `H.move m` itself -- not
onto `H.move (m'.transport i)` for a move `m'` invented on `G`.

## What is proved

* `MoveData.ext'`: two moves with the same three darts are equal (the five
  remaining fields are propositions).
* `MoveData.transport_transport` and `MoveData.transport_symm_transport`: the
  round trip `(m.transport i).transport i.symm = m`, in both directions.
* `Iso.movePullback i m : Iso (G.move (m.transport i.symm)) (H.move m)`, with
  `movePullback_dart` and `movePullback_vtx` exposing its two components: the
  move pulled back to `G` and pushed forward again is `m` on the nose, so the
  isomorphism lands on the intended target graph.
* `Iso.movePullback_nonloop`: the pulled back move contracts the edge of
  `i.dart.symm m.base`.

## What is NOT proved

Nothing here concerns stable sources, incidence dictionaries or labellings,
and `MoveData.swap` is not used.  No structure is introduced, so non-vacuity
is witnessed by existing inhabitants: `CubicDarts.thetaMove` and
`CubicDarts.thetaMoveIso` give a concrete `MoveData` and `Iso`, and
`movePullback_theta` below is the round trip on them.

## Consumers

The Draisma--Vargas count, whose walk through trivalent types records each
type change on the ambient graph and needs an isomorphism onto the literal
moved graph.
-/

namespace DraismaVargas.Infrastructure.CubicDartsTransport

open DraismaVargas.Infrastructure.CubicDarts CubicDartGraph

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
variable {D' V' : Type*} [Fintype D'] [DecidableEq D'] [Fintype V'] [DecidableEq V']

/-- **A Whitehead move is its three darts.**  The remaining five fields of
`MoveData` are propositions, so proof irrelevance closes the goal. -/
theorem MoveData.ext' {G : CubicDartGraph D V} {m m' : G.MoveData}
    (hBase : m.base = m'.base) (hLeft : m.left = m'.left) (hRight : m.right = m'.right) :
    m = m' := by
  cases m
  cases m'
  cases hBase
  cases hLeft
  cases hRight
  rfl

/-- **The round trip on moves.**  Pushing a move of `G` forward to `H` and
pulling it back returns the original move. -/
theorem MoveData.transport_transport {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : G.MoveData) :
    (m.transport i).transport i.symm = m :=
  MoveData.ext' (i.dart.symm_apply_apply m.base) (i.dart.symm_apply_apply m.left)
    (i.dart.symm_apply_apply m.right)

/-- **The round trip on moves, read from the target.**  A move of `H` pulled
back to `G` and pushed forward again is the original move of `H`. -/
theorem MoveData.transport_symm_transport {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : H.MoveData) :
    (m.transport i.symm).transport i = m :=
  MoveData.ext' (i.dart.apply_symm_apply m.base) (i.dart.apply_symm_apply m.left)
    (i.dart.apply_symm_apply m.right)

/-- The transported permutation agrees with the original through the dart
bijection, in the pulled back direction. -/
theorem MoveData.perm_transport_symm {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : H.MoveData) (d : D) :
    i.dart ((m.transport i.symm).perm d) = m.perm (i.dart d) := by
  classical
  show i.dart (Equiv.swap (i.dart.symm m.left) (i.dart.symm m.right) d)
    = Equiv.swap m.left m.right (i.dart d)
  by_cases hLeft : d = i.dart.symm m.left
  · subst hLeft; simp
  by_cases hRight : d = i.dart.symm m.right
  · subst hRight; simp
  · have hLeft' : i.dart d ≠ m.left := fun h ↦ hLeft (by rw [← h, Equiv.symm_apply_apply])
    have hRight' : i.dart d ≠ m.right := fun h ↦ hRight (by rw [← h, Equiv.symm_apply_apply])
    rw [Equiv.swap_apply_of_ne_of_ne hLeft hRight,
      Equiv.swap_apply_of_ne_of_ne hLeft' hRight']

/-- **The pulled back move produces an isomorphic graph, on the nose.**  This
is the analogue of `Iso.move` whose target is the literal `H.move m`, not
`H.move` of a move manufactured on `G`; the round trip above says the two
agree. -/
def Iso.movePullback {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : H.MoveData) :
    Iso (G.move (m.transport i.symm)) (H.move m) where
  dart := i.dart
  vtx := i.vtx
  op_map x := i.op_map x
  vert_map x := by
    show H.vert (m.perm (i.dart x)) = i.vtx (G.vert ((m.transport i.symm).perm x))
    rw [← i.vert_map ((m.transport i.symm).perm x), MoveData.perm_transport_symm]

@[simp] theorem Iso.movePullback_dart {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : H.MoveData) : (Iso.movePullback i m).dart = i.dart := rfl

@[simp] theorem Iso.movePullback_vtx {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : H.MoveData) : (Iso.movePullback i m).vtx = i.vtx := rfl

/-- The pulled back move is described by the transported darts. -/
@[simp] theorem MoveData.transport_base {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : G.MoveData) : (m.transport i).base = i.dart m.base := rfl

@[simp] theorem MoveData.transport_left {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : G.MoveData) : (m.transport i).left = i.dart m.left := rfl

@[simp] theorem MoveData.transport_right {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : G.MoveData) : (m.transport i).right = i.dart m.right := rfl

/-- The pulled back move is not a loop contraction at its own base dart. -/
theorem Iso.movePullback_nonloop {G : CubicDartGraph D V} {H : CubicDartGraph D' V'}
    (i : Iso G H) (m : H.MoveData) :
    ¬ G.IsLoopDart (i.dart.symm m.base) := (m.transport i.symm).nonloop

/-- A concrete round trip: the theta graph's Whitehead move, pulled back along
the isomorphism onto the dumbbell and pushed forward again. -/
theorem movePullback_theta (m : dumbbell.MoveData) :
    (m.transport thetaMoveIso.symm).transport thetaMoveIso = m :=
  MoveData.transport_symm_transport thetaMoveIso m

end DraismaVargas.Infrastructure.CubicDartsTransport
