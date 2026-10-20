module

public import DraismaVargasMarkedCount.MarkedCountGeneral.DropTransport
public import DraismaVargasMarkedCount.MarkedCountGeneral.DropUnique
public import DraismaVargasMarkedCount.MarkedCountGeneral.LiftOpen

@[expose] public section

/-!
# The drop lemma: the drop and the lift on frames (statements I1–I6)

On `sub := subdivide core s`, whose last mark `v` (the new vertex) has type `0`:

* **I1** `dropFrame`: smooth the image `x_v` of `v` (a divalent change-`0` target vertex,
  `typeZero_image'`) by contracting the target edge `t'` that carries the occurrence at `v` on the
  row labelled `cs s`, and join the two marked rows through `v`;
* **I2** `dropFrame_iso`: the drop descends to classes;
* **I3** `openAt_dropFrame`: the coordinates of the drop are those of `κ` with `z_{t'} + z_{t''}`
  merged, so openness is kept;
* **I4** `typedAbsMult_dropFrame`: the multiplicity is kept;
* **I5** `exists_lift`: every member over `core` at the merged request is the drop of a member over
  `sub` at `y`, under the proviso supplied by `hGeneral`;
* **I6** `lift_unique`: two members over `sub` at `y` with isomorphic drops are isomorphic,
  including when `s` is a loop of `core`.

Module `Drop` assembles `typedCount_dropLast` from these six statements and nothing else.

## Where they are proved

I1–I4 are the statements of module `DropSmooth` (`dropFrame'`, `openAt_dropFrame'`,
`typedAbsMult_dropFrame'`, the last resting on `DropSmooth.rowDenominator_split`) and
`DropTransport` (`dropIso`); I5 is `LiftSmooth.existsLift` (modules `LiftDatum` to `LiftOpen`); I6
is `DropUnique.liftUnique` (resting on `DropSmooth.exists_loop_reversal` (module `DropUnique`) when `s` is a loop).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.MarkedCount
open GenusSixExistence.Tripod.Gadget (subdivide)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {types : Fin k → ℕ}

/-- **I1, the drop** (the *Drop* half of the drop lemma). A typed frame over
`subdivide core s` whose last mark has type `0` gives a typed frame over `core` with the other
marks and types.

*Construction.* `x := κ.markSource (last k)`'s target vertex is divalent of change `0`, with `r = 0`
at every source vertex over it and no other mark over it (`typeZero_image'`, for the marked cubic
core `isMarkedCubic_snoc hc s`). The datum is `GluingContraction.contractDatum κ.data` along `t'`,
the target edge of the occurrence at `v` on the row `κ.ident.row.symm (cs s)`
(`ContractionForest` holds since `P_x`, `P_{t'}` have the same blocks, so the public
`valid_contractDatum` applies); the marks are the images of the old marks; the marked rows are
those of `κ` with the two rows through `v` joined (`cs s, last p ↦ s`); the columns are the target
edges other than `t'`. The fields: the dictionary of module `DropContract`, and module `DropDet` for
`det_ne_zero`. -/
noncomputable def dropFrame (hc : IsMarkedCubic core mark) (s : Fin p)
    (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree) :
    TypedFrame core mark types degree :=
  dropFrame' hc κ

/-- **I2: the drop descends to classes.** *Proof sketch.* An isomorphism over the identity of `sub`
preserves the row labels, so it carries the canonical contracted edge `t'` of `κ₁` to that of
`κ₂`, and `GeometricContraction.contractDatumIso` contracts it; marks go to marks, and the two
over-core clauses descend through the dictionaries of module `DropContract` (rows: `ρ`, which is
natural in isomorphisms). -/
theorem dropFrame_iso (hc : IsMarkedCubic core mark) (s : Fin p)
    {κ₁ κ₂ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree}
    (iso : TypedFrameIso κ₁ κ₂) :
    Nonempty (TypedFrameIso (dropFrame hc s κ₁) (dropFrame hc s κ₂)) :=
  ⟨DropSmooth.dropIso hc iso⟩

/-- **I3: openness passes to the drop.** *Proof sketch.* With `z := κ.coordsAt y`, the vector
`z` with column `t'` deleted and `z_{t''} + z_{t'}` at the merged column solves the drop's
equations at `mergeRequest s y` (`coordsAt_eq_of_mulVec`): off the merged row, columns `t'` and
`t''` of `κ.matrix` agree; on the merged row, the passes of `h' ∪ h''` over `t'` and over `t''`
have equal weights. Every entry is a sum of positive entries of `z`. -/
theorem openAt_dropFrame (hc : IsMarkedCubic core mark) (s : Fin p)
    (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)
    {y : Fin (p + 1) → ℚ} (hOpen : κ.OpenAt y) :
    (dropFrame hc s κ).OpenAt (mergeRequest s y) :=
  DropSmooth.openAt_dropFrame' κ hc hOpen

/-- **I4: the drop keeps the multiplicity.** *Proof sketch.* `l*` is unchanged (`x_v` is
divalent; `v` has type `0`). `|det A_κ| = |det A_drop| / m` by replacing row `h''` by `h' + h''`
and column `t'` by `t' - t''` (the new column is `±(1/m) e_{h'}`), where `m` is the index of the
edges at `v`; and `D_κ = m D_drop` because the rows other than `h', h''` keep their entries and
`d(h') d(h'') = m d(h)` (the denominator step, `DropSmooth.rowDenominator_split`). -/
theorem typedAbsMult_dropFrame (hc : IsMarkedCubic core mark) (s : Fin p)
    (κ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree) :
    (dropFrame hc s κ).typedAbsMult = κ.typedAbsMult :=
  DropSmooth.typedAbsMult_dropFrame' κ hc

/-- **I5: the lift** (the *Lift* half of the drop lemma). *Proof sketch.* Walk the marked row
of slot `s` of `κ` from its end at `tail s` (module `DropWalk`): `e_1, …, e_N` with prefix lengths
`ℓ_{<i}` at `z := κ.coordsAt (mergeRequest s y)`. The lift at position `i` (module `LiftDatum`:
expand the target edge of `e_i`, put `v` on `e_i`) has the coordinates of `κ`, with
`z_{t'} = m (y(cs s) - ℓ_{<i})` and `z_{t''} = z_{t(e_i)} - z_{t'}`; its drop is isomorphic to `κ`.
Since `0 < y(cs s) < y(cs s) + y(last p) = ℓ_{≤ N}` (`hPositive`), some `i` has
`ℓ_{<i} ≤ y(cs s) < ℓ_{≤ i}`, and equality on the left (`i ≥ 2`) would give a frame over `sub`
with a zero coordinate at `y`, which `hGeneral` excludes (the proviso of the drop lemma). -/
theorem exists_lift (hc : IsMarkedCubic core mark) (s : Fin p) {y : Fin (p + 1) → ℚ}
    (hPositive : ∀ i, 0 < y i)
    (hGeneral : ∀ (κ' : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree)
      (col : Fin (p + 1)), κ'.coordsAt y col ≠ 0)
    (κ : TypedFrame core mark types degree) (hOpen : κ.OpenAt (mergeRequest s y)) :
    ∃ κ' : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree,
      κ'.OpenAt y ∧ Nonempty (TypedFrameIso (dropFrame hc s κ') κ) :=
  LiftSmooth.existsLift hc s hPositive hGeneral κ hOpen

/-- **I6: the lift is unique.** *Proof sketch.* The isomorphism of the drops maps the walk
of row `s` of the first drop from `tail s` to that of the second (if `s` is not a loop of `core`,
the start is the only end at `tail s`; if it is a loop, compose with the automorphism reversing the
loop row, module `LoopHairpin`). Openness of `κ₁` and `κ₂` at `y` puts `v` at the position `i` with
`ℓ_{<i} < y(cs s) < ℓ_{≤ i}` in both, so the isomorphism maps the merged occurrence to the merged
occurrence, and it extends over `x_v` (module `DropExtend`), carrying `v` to `v`. -/
theorem lift_unique (hc : IsMarkedCubic core mark) (s : Fin p) {y : Fin (p + 1) → ℚ}
    {κ₁ κ₂ : TypedFrame (subdivide core s) (snocMark mark) (snocType types 0) degree}
    (h₁ : κ₁.OpenAt y) (h₂ : κ₂.OpenAt y)
    (iso : TypedFrameIso (dropFrame hc s κ₁) (dropFrame hc s κ₂)) :
    Nonempty (TypedFrameIso κ₁ κ₂) :=
  DropSmooth.liftUnique hc h₁ h₂ iso

end DraismaVargas.Count.MarkedCountGeneral
