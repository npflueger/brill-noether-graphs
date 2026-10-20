module

public import DiagonalSecant.BridgeLift
public import DiagonalSecant.CMDictionary
public import DiagonalSecant.CMHairpin
public import DiagonalSecant.CMRetract
public import DiagonalSecant.CMRoot
public import DiagonalSecant.CMWalk
public import DiagonalSecant.CTTransport
public import DiagonalSecant.ClosureH
public import DiagonalSecant.CountAtActual
public import DiagonalSecant.CycleCorollary
public import DiagonalSecant.Defs
public import DiagonalSecant.Descent
public import DiagonalSecant.Main
public import DiagonalSecant.Model
public import DiagonalSecant.Parity
public import DiagonalSecant.Restrict
public import DiagonalSecant.TypedImage
public import DiagonalSecant.TypedMoments
public import DiagonalSecant.TypedPlacement
public import DiagonalSecant.TypedReach
public import DiagonalSecant.TypedRealisation
public import DiagonalSecant.TypedRows
public import DiagonalSecant.TypedTransport

/-!
# The diagonal secant theorem

* `DiagonalSecant.diagonalSecant` and `DiagonalSecant.bnExists_one_genus_sub_one`: on every
  connected graph `G` of genus `g ≥ 5` with `g ≡ 1, 2 (mod 4)`, and every vertex `u`, some
  effective divisor `F` of degree two makes `(g − 3)u + F` a divisor of degree `g − 1` and rank at
  least one; in particular `G` carries a pencil of degree `g − 1`.
* `DiagonalSecant.cycleSecant`: on every connected graph of genus `g ≥ 4` with `g ≡ 0, 1 (mod 4)`
  and vertices `u, v`, some effective `F` of degree two makes `(g − 2)u + F` of rank at least one
  with `(g − 2)u + F − 2v` winnable: a pencil of degree `g` with a `(g − 2)`-fold point at `u`
  and a double point at `v`.

Add an import line above whenever a module is added under `DiagonalSecant/`, or
`lake build DiagonalSecant` will silently skip it.
-/
