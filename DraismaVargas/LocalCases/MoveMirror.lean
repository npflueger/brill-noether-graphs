import DraismaVargas.LocalCases.OuterWalk

/-!
# The mirror of a Whitehead move, and the transport of a type-change link

Source: Vargas, Part II, arXiv:2609.09109, the combinatorial setup of the section on changing
combinatorial type (subsection `subsec-setup-determinants`): the labelling
convention (1) at a non-trivalent wall.  The contracted edge `h_1` of the
incoming type has two ends, the four edges of `H_0` at the merged vertex `A` are
distributed over those two ends, and the combinatorial resolutions of `H_0` are
the `2+2` partitions of those four edges.  At the row level a Whitehead move `m`
therefore prescribes a pair of survivors that straddles the two ends of `h_1`,
one from each end.

The construction is **valency-agnostic**: nothing below mentions a wall star,
an anchor, a candidate or a valency.

## The problem this module solves

`OuterWalk.TypeChangeLink m wd` mentions the move `m` only through the moved
graph `graph.move m`, in its `tracks` field.  The (H-*) conditions of the
prescribed candidates, on the other hand, name the pair of survivors the move
places at `graph.vert m.base` -- and each candidate family realises only *one*
of the two complementary pairs of its own `2+2` partition (at valency three the
`SimpleBase` inequality `k_beta + k_delta <= |A|` holds for exactly one of the
two complementary realisations, because the four survivor indices sum to
`2|A| + 1`).  `CubicDarts.MoveData.swap` does not repair this: it toggles the
orientation clause and the pair at `graph.vert m.base` together.

The remedy is the **mirror move**.  Write the star of `graph.vert m.base` as
`{m.base, m.left, b}` and the star of `graph.vert (graph.op m.base)` as
`{graph.op m.base, m.right, d}`; after the move the first star is
`{m.base, b, m.right}`.  The mirror move is `⟨m.base, b, d⟩`: it contracts the
same edge and exchanges the *other* dart at each end, so after it the first star
is `{m.base, m.left, d}` -- the complementary pair.  The two moved graphs are
isomorphic by the label-preserving isomorphism that exchanges the two ends.

## What is proved

* `thirdLeft`, `thirdRight` and their specifications: the third dart at each end
  of the contracted edge (`CubicDarts.CubicDartGraph.exists_third`), together
  with the exhaustion `z = base ∨ z = left ∨ z = thirdLeft` of the darts at
  `graph.vert m.base` and its companion at the other end.
* `mirror`: the mirror move `⟨m.base, thirdLeft m, thirdRight m⟩`.  It has the
  same `base`, so `label m.mirror.base` is *definitionally* `label m.base` and a
  `WallData` of the facet of `m` is a `WallData` of the facet of the mirror --
  which is why `TypeChangeLink (mirror m) wd` typechecks with the same `wd`.
* `mirror_ne_self` and `mirror_mirror`: the mirror is a genuinely different move
  (its `left` field is the third dart, not `m.left`), and mirroring twice
  returns `m` -- the correctness check of the construction, since the third dart
  at `graph.vert m.base` other than `m.base` and `thirdLeft m` is `m.left`.
* `moveMirrorIso : Iso (graph.move (mirror m)) (graph.move m)`: the
  isomorphism `(swap m.base (graph.op m.base), swap (graph.vert m.base)
  (graph.vert (graph.op m.base)))`.  `mirror_op_map` is the involution clause
  and `mirror_vert_map` the vertex clause, proved by the seven-case exhaustion
  of the darts (the three at each end of the contracted edge, and everything
  else, where both permutations are the identity).
* `tracksOfIso`: `InteriorGraphTracking.Tracks fd G label` transports along any
  isomorphism `G ≃ G'` that preserves `label` on darts (`Iso.trans` on the
  `iso` field; the `row_map` field is preserved because the labels are).
* `label_swap_base`: the swap of the two darts of the contracted edge preserves
  `label`, from `label (graph.op m.base) = label m.base` alone.
* **`linkOfMirror : TypeChangeLink (mirror m) wd → TypeChangeLink m wd`**: the
  deliverable.  Only the `tracks` field changes; `base`, `baseValid`,
  `candidate`, `outgoingFD` and `agree` do not mention the move at all.

## The hypotheses that remain explicit

1. `hL : label (graph.op m.base) = label m.base` is an explicit hypothesis of
   `label_swap_base` and `linkOfMirror`, exactly as in
   `NonTrivalentValencyFourDispatcher.linkOfSwap`.  At a wall datum it is free
   (`MovedIncidenceIso.label_op_of_tracks _ wd.fullDim wd.tracks m.base`), but
   that module is not imported here, so the caller supplies it.
2. Nothing else.  No wall valency, no star, no anchor, no candidate.

No structure and no `Prop` is introduced.  `thirdLeft`, `thirdRight` name darts
of the graph already in hand, `mirror` inhabits the existing
`CubicDarts.CubicDartGraph.MoveData`, `moveMirrorIso` the existing
`CubicDarts.Iso`, `tracksOfIso` the existing `InteriorGraphTracking.Tracks` and
`linkOfMirror` the existing `OuterWalk.TypeChangeLink`; `mirror_mirror` and
`mirror_ne_self` witness that the construction is the intended involution and
is not the identity.

## Consumers

The valency-three move-to-type dispatcher
(`DraismaVargas.LocalCases.NonTrivalentValencyThreeDispatcher`), which uses
`linkOfMirror` whenever the move puts at `graph.vert m.base` the complement of
the pair the realisable candidate of that partition names.  `tracksOfIso` is
also the general transport of a tracking along a label-preserving isomorphism of
ambient graphs.
-/

namespace DraismaVargas.LocalCases.MoveMirror

open DraismaVargas.Infrastructure
open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.InteriorGraphTracking
open DraismaVargas.LocalCases.OuterWalk

noncomputable section

/-! ## 1.  The third dart at each end of the contracted edge -/

section Third

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {G : CubicDartGraph D V} (m : G.MoveData)

/-- The third dart at `graph.vert m.base`, beside `m.base` and `m.left`. -/
def thirdLeft : D :=
  (G.exists_third (x := G.vert m.base) rfl m.left_vert m.base_ne_left).choose

private theorem thirdLeft_spec :
    G.vert (thirdLeft m) = G.vert m.base ∧ thirdLeft m ≠ m.base ∧ thirdLeft m ≠ m.left ∧
      ∀ z : D, G.vert z = G.vert m.base → z = m.base ∨ z = m.left ∨ z = thirdLeft m :=
  (G.exists_third (x := G.vert m.base) rfl m.left_vert m.base_ne_left).choose_spec

@[simp] theorem thirdLeft_vert : G.vert (thirdLeft m) = G.vert m.base := (thirdLeft_spec m).1

theorem thirdLeft_ne_base : thirdLeft m ≠ m.base := (thirdLeft_spec m).2.1

theorem thirdLeft_ne_left : thirdLeft m ≠ m.left := (thirdLeft_spec m).2.2.1

/-- The three darts at `graph.vert m.base`. -/
theorem eq_base_or_left_or_thirdLeft (z : D) (hz : G.vert z = G.vert m.base) :
    z = m.base ∨ z = m.left ∨ z = thirdLeft m := (thirdLeft_spec m).2.2.2 z hz

/-- The third dart at `graph.vert (graph.op m.base)`, beside `graph.op m.base`
and `m.right`. -/
def thirdRight : D :=
  (G.exists_third (x := G.vert (G.op m.base)) rfl m.right_vert m.opBase_ne_right).choose

private theorem thirdRight_spec :
    G.vert (thirdRight m) = G.vert (G.op m.base) ∧ thirdRight m ≠ G.op m.base ∧
      thirdRight m ≠ m.right ∧
      ∀ z : D, G.vert z = G.vert (G.op m.base) →
        z = G.op m.base ∨ z = m.right ∨ z = thirdRight m :=
  (G.exists_third (x := G.vert (G.op m.base)) rfl m.right_vert m.opBase_ne_right).choose_spec

@[simp] theorem thirdRight_vert : G.vert (thirdRight m) = G.vert (G.op m.base) :=
  (thirdRight_spec m).1

theorem thirdRight_ne_opBase : thirdRight m ≠ G.op m.base := (thirdRight_spec m).2.1

theorem thirdRight_ne_right : thirdRight m ≠ m.right := (thirdRight_spec m).2.2.1

/-- The three darts at `graph.vert (graph.op m.base)`. -/
theorem eq_opBase_or_right_or_thirdRight (z : D) (hz : G.vert z = G.vert (G.op m.base)) :
    z = G.op m.base ∨ z = m.right ∨ z = thirdRight m := (thirdRight_spec m).2.2.2 z hz

/-! ### The two ends are distinct, so the two triples are disjoint -/

theorem thirdLeft_ne_opBase : thirdLeft m ≠ G.op m.base := by
  intro h
  exact m.nonloop (by rw [← h, thirdLeft_vert])

theorem thirdLeft_ne_right : thirdLeft m ≠ m.right := by
  intro h
  exact m.nonloop (by rw [← m.right_vert, ← h, thirdLeft_vert])

theorem thirdRight_ne_base : thirdRight m ≠ m.base := by
  intro h
  exact m.nonloop (by rw [← thirdRight_vert, h])

theorem thirdRight_ne_left : thirdRight m ≠ m.left := by
  intro h
  exact m.nonloop (by rw [← thirdRight_vert, h, m.left_vert])

end Third

/-! ## 2.  The mirror move -/

section Mirror

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {G : CubicDartGraph D V} (m : G.MoveData)

/-- **The mirror move**: the same contracted edge, with the *other* dart
exchanged at each end.  `graph.move (mirror m)` is isomorphic to `graph.move m`
(`moveMirrorIso`), but the pair of darts it places at `graph.vert m.base` is the
complement of the pair `m` places there. -/
def mirror : G.MoveData where
  base := m.base
  left := thirdLeft m
  right := thirdRight m
  nonloop := m.nonloop
  left_vert := thirdLeft_vert m
  left_ne := thirdLeft_ne_base m
  right_vert := thirdRight_vert m
  right_ne := thirdRight_ne_opBase m

@[simp] theorem mirror_base : (mirror m).base = m.base := rfl

@[simp] theorem mirror_left : (mirror m).left = thirdLeft m := rfl

@[simp] theorem mirror_right : (mirror m).right = thirdRight m := rfl

/-- Two Whitehead moves with the same three darts are equal: the remaining
fields are propositions. -/
theorem moveData_ext {m m' : G.MoveData} (hb : m.base = m'.base) (hl : m.left = m'.left)
    (hr : m.right = m'.right) : m = m' := by
  revert hb hl hr
  cases m
  cases m'
  intro hb hl hr
  dsimp only at hb hl hr
  subst hb
  subst hl
  subst hr
  rfl

/-- **The mirror is a different move**: it exchanges the third dart at the base
end, not `m.left`. -/
theorem mirror_ne_self : mirror m ≠ m := by
  intro h
  exact thirdLeft_ne_left m (congrArg CubicDartGraph.MoveData.left h)

/-- **Mirroring is an involution.**  The third dart at `graph.vert m.base`
beside `m.base` and `thirdLeft m` is `m.left`, and symmetrically at the other
end. -/
theorem mirror_mirror : mirror (mirror m) = m := by
  refine moveData_ext rfl ?_ ?_
  · show thirdLeft (mirror m) = m.left
    rcases eq_base_or_left_or_thirdLeft m (thirdLeft (mirror m))
      (thirdLeft_vert (mirror m)) with h | h | h
    · exact absurd h (thirdLeft_ne_base (mirror m))
    · exact h
    · exact absurd h (thirdLeft_ne_left (mirror m))
  · show thirdRight (mirror m) = m.right
    rcases eq_opBase_or_right_or_thirdRight m (thirdRight (mirror m))
      (thirdRight_vert (mirror m)) with h | h | h
    · exact absurd h (thirdRight_ne_opBase (mirror m))
    · exact h
    · exact absurd h (thirdRight_ne_right (mirror m))

/-! ### The isomorphism `graph.move (mirror m) ≅ graph.move m` -/

/-- The involution clause: swapping the two darts of the contracted edge
commutes with `op`. -/
theorem mirror_op_map (x : D) :
    (G.move m).op (Equiv.swap m.base (G.op m.base) x) =
      Equiv.swap m.base (G.op m.base) ((G.move (mirror m)).op x) := by
  classical
  show G.op (Equiv.swap m.base (G.op m.base) x) = Equiv.swap m.base (G.op m.base) (G.op x)
  by_cases h1 : x = m.base
  · subst h1
    rw [Equiv.swap_apply_left, Equiv.swap_apply_right, G.op_op]
  · by_cases h2 : x = G.op m.base
    · subst h2
      rw [Equiv.swap_apply_right, G.op_op, Equiv.swap_apply_left]
    · have h3 : G.op x ≠ m.base := by
        intro h
        exact h2 (by rw [← h, G.op_op])
      have h4 : G.op x ≠ G.op m.base := fun h ↦ h1 (G.op_injective h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne h3 h4]

/-- The vertex clause: swapping the two darts of the contracted edge intertwines
the two moved vertex maps with the exchange of the two ends. -/
theorem mirror_vert_map (x : D) :
    (G.move m).vert (Equiv.swap m.base (G.op m.base) x) =
      Equiv.swap (G.vert m.base) (G.vert (G.op m.base)) ((G.move (mirror m)).vert x) := by
  classical
  show G.vert (m.perm (Equiv.swap m.base (G.op m.base) x)) =
    Equiv.swap (G.vert m.base) (G.vert (G.op m.base)) (G.vert ((mirror m).perm x))
  by_cases hP : G.vert x = G.vert m.base
  · rcases eq_base_or_left_or_thirdLeft m x hP with rfl | rfl | rfl
    · rw [Equiv.swap_apply_left, m.perm_opBase, show (mirror m).perm m.base = m.base from
        (mirror m).perm_base, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne m.left_ne (Ne.symm m.opBase_ne_left), m.perm_left,
        m.right_vert, (mirror m).perm_of_ne (Ne.symm (thirdLeft_ne_left m))
          (Ne.symm (thirdRight_ne_left m)), m.left_vert, Equiv.swap_apply_left]
    · rw [Equiv.swap_apply_of_ne_of_ne (thirdLeft_ne_base m) (thirdLeft_ne_opBase m),
        m.perm_of_ne (thirdLeft_ne_left m) (thirdLeft_ne_right m), thirdLeft_vert,
        show (mirror m).perm (thirdLeft m) = thirdRight m from (mirror m).perm_left,
        thirdRight_vert, Equiv.swap_apply_right]
  · by_cases hQ : G.vert x = G.vert (G.op m.base)
    · rcases eq_opBase_or_right_or_thirdRight m x hQ with rfl | rfl | rfl
      · rw [Equiv.swap_apply_right, m.perm_base, show (mirror m).perm (G.op m.base) = G.op m.base
          from (mirror m).perm_opBase, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm m.base_ne_right) m.right_ne, m.perm_right,
          m.left_vert, (mirror m).perm_of_ne (Ne.symm (thirdLeft_ne_right m))
            (Ne.symm (thirdRight_ne_right m)), m.right_vert, Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne (thirdRight_ne_base m) (thirdRight_ne_opBase m),
          m.perm_of_ne (thirdRight_ne_left m) (thirdRight_ne_right m), thirdRight_vert,
          show (mirror m).perm (thirdRight m) = thirdLeft m from (mirror m).perm_right,
          thirdLeft_vert, Equiv.swap_apply_left]
    · have hxb : x ≠ m.base := fun h ↦ hP (by rw [h])
      have hxo : x ≠ G.op m.base := fun h ↦ hQ (by rw [h])
      have hxl : x ≠ m.left := fun h ↦ hP (by rw [h, m.left_vert])
      have hxr : x ≠ m.right := fun h ↦ hQ (by rw [h, m.right_vert])
      have hxtl : x ≠ thirdLeft m := fun h ↦ hP (by rw [h, thirdLeft_vert])
      have hxtr : x ≠ thirdRight m := fun h ↦ hQ (by rw [h, thirdRight_vert])
      rw [Equiv.swap_apply_of_ne_of_ne hxb hxo, m.perm_of_ne hxl hxr,
        (mirror m).perm_of_ne hxtl hxtr, Equiv.swap_apply_of_ne_of_ne hP hQ]

/-- **The mirror move produces an isomorphic graph.**  The isomorphism exchanges
the two ends of the contracted edge and, with them, its two darts. -/
def moveMirrorIso : CubicDartGraph.Iso (G.move (mirror m)) (G.move m) where
  dart := Equiv.swap m.base (G.op m.base)
  vtx := Equiv.swap (G.vert m.base) (G.vert (G.op m.base))
  op_map := mirror_op_map m
  vert_map := mirror_vert_map m

@[simp] theorem moveMirrorIso_dart (x : D) :
    (moveMirrorIso m).dart x = Equiv.swap m.base (G.op m.base) x := rfl

/-! ### The two pairs of darts the two moves place at `G.vert m.base` -/

theorem thirdLeft_mirror : thirdLeft (mirror m) = m.left :=
  congrArg CubicDartGraph.MoveData.left (mirror_mirror m)

theorem thirdRight_mirror : thirdRight (mirror m) = m.right :=
  congrArg CubicDartGraph.MoveData.right (mirror_mirror m)

/-- **The pair of darts the move places at `G.vert m.base` beside `m.base`**:
the third dart at that end, and the dart brought over from the other end. -/
theorem movedStar_eq_pair :
    (Finset.univ.filter fun c ↦ (G.move m).vert c = G.vert m.base).erase m.base =
      {thirdLeft m, m.right} := by
  classical
  ext d
  rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, -, hv⟩
    by_cases hdl : d = m.left
    · subst hdl
      refine absurd ?_ m.nonloop
      rw [← m.right_vert, ← m.perm_left]
      exact hv
    · by_cases hdr : d = m.right
      · exact Or.inr hdr
      · refine Or.inl ?_
        rcases eq_base_or_left_or_thirdLeft m d
            (by rw [← m.perm_of_ne hdl hdr]; exact hv) with h | h | h
        · exact absurd h hne
        · exact absurd h hdl
        · exact h
  · rintro (rfl | rfl)
    · refine ⟨thirdLeft_ne_base m, Finset.mem_univ _, ?_⟩
      show G.vert (m.perm (thirdLeft m)) = G.vert m.base
      rw [m.perm_of_ne (thirdLeft_ne_left m) (thirdLeft_ne_right m), thirdLeft_vert]
    · refine ⟨Ne.symm m.base_ne_right, Finset.mem_univ _, ?_⟩
      show G.vert (m.perm m.right) = G.vert m.base
      rw [m.perm_right, m.left_vert]

/-- **The mirror move places the complementary pair there**: `m.left`, which the
move itself sends away, and the third dart at the other end. -/
theorem movedStar_mirror_eq_pair :
    (Finset.univ.filter fun c ↦ (G.move (mirror m)).vert c = G.vert m.base).erase m.base =
      {m.left, thirdRight m} := by
  have h := movedStar_eq_pair (mirror m)
  rw [thirdLeft_mirror m] at h
  exact h

/-- The four darts at the two ends of the contracted edge, other than its own
two darts, are `m.left`, `thirdLeft m`, `m.right`, `thirdRight m`, and the two
moves take complementary pairs of them. -/
theorem thirdLeft_ne_left' : m.left ≠ thirdLeft m := (thirdLeft_ne_left m).symm

theorem right_ne_thirdRight : m.right ≠ thirdRight m := (thirdRight_ne_right m).symm

end Mirror

/-! ## 3.  Transporting a tracking along a label-preserving isomorphism -/

section Transport

variable {coordinate D V : Type*} [Fintype coordinate] [DecidableEq coordinate]
  [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {target : CFGraph} {degree : ℕ} {data : GluingDatum target degree}

/-- **A tracking transports along any label-preserving isomorphism of ambient
graphs.**  `Tracks fd G label` is an isomorphism `ofDatum ≃ G` together with the
row equation for `label`; composing with `j` keeps the row equation exactly when
`j` preserves `label`. -/
def tracksOfIso {fd : FullDimensionalSourcePresentation data coordinate}
    {G G' : CubicDartGraph D V} {label : D → coordinate}
    (t : Tracks fd G label) (j : CubicDartGraph.Iso G G')
    (hj : ∀ d : D, label (j.dart d) = label d) :
    Tracks fd G' label where
  iso := t.iso.trans j
  row_map d := by
    show label (j.dart (t.iso.dart d)) = _
    rw [hj]
    exact t.row_map d

end Transport

/-! ## 4.  The link of the mirror move is a link of the move -/

section Link

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  {graph : CubicDartGraph D V}

/-- The swap of the two darts of the contracted edge preserves the chart label:
the two darts of one edge of the tracked graph carry the same stable row. -/
theorem label_swap_base {coordinate : Type*} {label : D → coordinate} (m : graph.MoveData)
    (hL : label (graph.op m.base) = label m.base) (d : D) :
    label (Equiv.swap m.base (graph.op m.base) d) = label d := by
  classical
  by_cases h1 : d = m.base
  · subst h1
    rw [Equiv.swap_apply_left]
    exact hL
  · by_cases h2 : d = graph.op m.base
    · subst h2
      rw [Equiv.swap_apply_right]
      exact hL.symm
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

variable {coordinate : Type} [Fintype coordinate] [DecidableEq coordinate]
  {degree : ℕ} {label : D → coordinate} (m : graph.MoveData)

/-- **A link for the mirror move is a link for the move.**  The two moves
contract the same edge, so the wall payload is literally unchanged (`m.base` is
the same dart, hence so is the facet `label m.base` and the whole `WallData`);
the moved graphs are isomorphic by `moveMirrorIso`, which preserves `label`, so
only the `tracks` field is transported.  The base stage, the candidate, its
presentation and the common-minor agreement do not mention the move. -/
def linkOfMirror {arrival : FacetArrival degree graph label (label m.base)}
    (wd : WallData arrival) (hL : label (graph.op m.base) = label m.base)
    (link : TypeChangeLink (mirror m) wd) : TypeChangeLink m wd where
  base := link.base
  baseValid := link.baseValid
  candidate := link.candidate
  outgoingFD := link.outgoingFD
  tracks := tracksOfIso link.tracks (moveMirrorIso m) (label_swap_base m hL)
  agree := link.agree

/-- The `Nonempty` form, which is how the dispatcher consumes it. -/
theorem nonempty_typeChangeLink_of_mirror {arrival : FacetArrival degree graph label (label m.base)}
    (wd : WallData arrival) (hL : label (graph.op m.base) = label m.base)
    (link : Nonempty (TypeChangeLink (mirror m) wd)) : Nonempty (TypeChangeLink m wd) :=
  link.map (linkOfMirror m wd hL)

end Link

end

end DraismaVargas.LocalCases.MoveMirror
