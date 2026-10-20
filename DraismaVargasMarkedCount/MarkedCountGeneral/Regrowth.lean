module

public import DraismaVargasMarkedCount.MarkedCountGeneral.Restriction
public import DraismaVargasMarkedCount.MarkedCountGeneral.RegrowIso

@[expose] public section

/-!
# The two-point ramified count, module 8: regrowth

**Regrowth** attaches to a typed frame `ψ` of type `aⱼ - 2Jⱼ` in degree `d - shed J`, with slope
sequences `s^{(j)}`, the caterpillar fibre at every mark at once (for two
marks this is the regrowth at one mark followed by the regrowth at the other, done in one step
as the ramification-one `Regrow` does for lollipops): new sheets `n_1, …, n_{shed J}` (degree `d`),
and at mark `j` the target path `x —t_1— x_1 — ⋯ — x_{a-1}` with a two-edge leaf branch `β_i` at
every `x_i` (and `β_a` at `x_{a-1}`), the blocks `P_1 ⊆ S` (`|P_1| = s_1 ≤ m(u)` by (D4′)),
`P_{i+1} = P_i ∪ {next new sheet}` at an ascent, `P_i` minus one element at a descent,
`S_i = P_i ∪ P_{i+1}` at `x_i`, a 2-subset `Q_i ⊆ S_i` over each bridge, `P_a` over `β_a`.

## Contents

* `regrowTailed`: the construction (`CatRegrow.catTarget`, `CatRegrow.CatBranching.regrowDatum`,
  `CatRegrow.fullDim`, `CatRegrow.ident`);
* `regrowTailed_respects`: regrowth descends to classes (`CatRegrow.datumIso`,
  `CatRegrow.overCore_vertex`, `CatRegrow.overCore_row`).

Both print `[propext, Classical.choice, Quot.sound]`. The construction is generic, in namespace
`CatRegrow`, over any datum `ψ` and any valid tail chains (modules `RegrowSheets` to
`RegrowMatrix`); the typed frame supplies one (`RegrowWindow`, `RegrowFrame`):

* `RegrowSheets`: `liftPart` (`Sheets.extendPartition`, new sheets singletons) and
  `blockPart` (one block, singletons);
* `RegrowTarget`: the target tails, named by the caterpillar slots and vertices (plus tips);
* `RegrowChain`: `TailChain` (the blocks `P_i`, `Q_i` and their names) and `TailChain.Valid`;
* `RegrowDatum`: `CatBranching`, `regrowDatum`, the source dictionary, Riemann--Hurwitz,
  connectedness, the genus;
* `RegrowDangling`, `RegrowSurvivors`: the dangling dictionary (a sheet that is a singleton over
  a region of the tree attached at one vertex dangles there) and the surviving valencies;
* `RegrowStable`: rows `StablePath ≃ MarkedStablePath ψ ⊕ TE c`, branch vertices
  `MarkedBranchVertex ψ ⊕ Σ j, CatVertex (c j)`, incidence counts, trivalence, path ends;
* `RegrowMatrix`: the block-diagonal length matrix;
* `RegrowWindow`: the window chain of a slope sequence (`P_i = sh [lo_i, lo_i + s_i)`);
* `RegrowFrame`: the sheets `Fin (d - shed J) ⊕ Fin (shed J) ≃ Fin d` (the decomposition `σ_B`,
  inverted),
  the line-up of the mark's block, and every field of `CatBranching` for a typed frame;
* `RegrowAssemble`: the frame's `fullDim` (dimension count, determinant) and `ident`;
* `RegrowIso`: isomorphisms extend over the tails, with one sheet permutation per tail.

**Saturation at degree `d`** (the edge and genus count of the caterpillar tails): the tails add
`Σⱼ (3aⱼ - 1)` target edges and genus `Σⱼ aⱼ`, the new sheets `shed J` to the degree, and the
typed excess `Σⱼ (aⱼ - 2Jⱼ - 1)` is absorbed (`CatRegrow.saturated`).
-/

namespace DraismaVargas.Count.MarkedCountGeneral

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.Count.MarkedCount
open DraismaVargas.Count.SegmentWalls (Frame)
open DraismaVargas.Count.GeometricSegmentWalls (FrameIso)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p k degree : ℕ} {core : Core n p} {mark : Fin k → Fin n} {c : Fin k → ℕ}

/-- **Regrowth**.

*Construction.* First add `shed J` new sheets to `ψ`, singletons everywhere (degree
`d = (d - shed J) + shed J`, using `IsTailDegree`, which gives `shed J ≤ d`); then attach the
target tail at every mark (`T.V ⊕ (Σⱼ tail vertices)`, as the ramification-one
`Regrow.regrowTarget`) with the partitions described in the module docstring. The fields of
`FullDimensionalSourcePresentation`:

* validity: Riemann--Hurwitz at `u_j` is `r⁺ = r_ψ(u_j) - (s_1 - 1) ≥ 0` by (D4′); `r(B_i) = 0`;
  `1, 2` at the lollipop vertices; `0` at the singletons; unchanged elsewhere over `x`;
  connectedness through the ascents (every new sheet joins the core at the vertex `B_i` where it
  is added);
* `saturated`: `|E(T)| = |E(T')| + Σ (3aⱼ - 1)`, `g(G) = g + Σ aⱼ`, from `ψ`'s typed `saturated`;
* the labelling and `det_ne_zero`: the matrix is `A_{ψ;u} ⊕ diag(1/sᵢ; 1/2; 2)`;
* `trivalent` (`u_j` gains one survivor, `e_1`), `pathEnds`.

Change-minimality is then derived by `FullDimensionalSourcePresentation` itself (from the
dimension count), so the local structure at a ramified mark (fold or transition) is not needed
here. The identification: the stable graph is the marked stable graph of `ψ` with the tails,
`B_i ↦ spine`, `A_i ↦ bulb`. -/
noncomputable def regrowTailed (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) (J : LowerIndex c)
    (κ : TypedFrame core mark (lowerType c J) (degree - shed J)) (s : SlopeData c J) :
    Frame T.H degree where
  target := CatRegrow.catTarget c κ.target (CatRegrow.branching hd J κ s).x
  data := (CatRegrow.branching hd J κ s).regrowDatum
  fullDim := CatRegrow.fullDim T hd J κ s hc
  ident := CatRegrow.ident T hd J κ s hc

/-- **Regrowth descends to classes**: the class does not depend on the choices. *Proof sketch.*
Each choice (`P_1 ⊆ S`, the sheet dropped at a descent, `Q_i`, the labels of the new sheets) is a
permutation of sheets inside one block at one target vertex, extended along the far side of that
vertex, hence an isomorphism of gluing data over the identity of the core; and an isomorphism of
typed frames extends over the tails (as the ramification-one `Regrow.regrowIso`). -/
theorem regrowTailed_respects (T : Tailed core mark c) (hc : IsMarkedCubic core mark)
    (hd : IsTailDegree n p c degree) (J : LowerIndex c)
    {κ κ' : TypedFrame core mark (lowerType c J) (degree - shed J)} (iso : TypedFrameIso κ κ')
    (s : SlopeData c J) :
    Nonempty (FrameIso (regrowTailed T hc hd J κ s) (regrowTailed T hc hd J κ' s)) :=
  ⟨⟨CatRegrow.datumIso hd J iso s,
    CatRegrow.overCore_vertex hd J iso s T hc _,
    CatRegrow.overCore_row hd J iso s T hc _⟩⟩

end DraismaVargas.Count.MarkedCountGeneral
