import DraismaVargas.LocalCases.OrientedTraversal

/-!
# Injectivity of `vertexClass` is `Faithful`

Completing a terminal face needs the canonical map
`RowDictionary.vertexClass dict topology`, from the refined core vertices to
the contraction classes of the quotient source, to be a bijection onto the
kept classes.  That splits into a global count -- the refinement exhausts the
kept classes, which `TerminalExhausts` reduces to a genus identity -- and
injectivity, a local condition.  This file settles the local half:
`injective_vertexClass_of_faithful` is the injectivity field of
`TerminalExhausts.TerminalCertificate`.

## The relationship to `Faithful`, first

`StrongRefinement.Faithful dictionary : Function.Injective dictionary.vertexAt`
is not derivable from the fields of a row dictionary and a strong presentation:
moving a core vertex that no slot touches onto another core vertex (`reassign`)
leaves a row dictionary whose placement is not injective.  **That verdict
transfers to `vertexClass`, and the two conditions are in fact the same one.**

* `faithful_of_injective` (§1) — injectivity of `vertexClass` *implies*
  `Faithful`, always.  The stable core vertices enter through `Sum.inl` and
  `classOf` is a further quotient, so injectivity downstairs is injectivity
  upstairs.  Hence the same move defeats injectivity of `vertexClass`:
  `exists_not_injective` (§2).
* `injective_vertexClass_iff` (§5) — conversely, **for a spanning placement
  injectivity of `vertexClass` is exactly `Faithful`**: the quotient source
  separates the refined core vertices exactly when the dictionary separates
  the stable ones.
* `exists_faithful_not_injective` (§5) — and `Spanning` is not removable: a
  core vertex no slot touches can be placed on an interior breakpoint, keeping
  `vertexAt` injective while `vertexClass` collapses.

So the injectivity verdict is: **not derivable, and not a new condition** — it
is `Faithful` and `Spanning`, and nothing about the row breakpoints or about
the contraction has to be carried.

## Where the mathematics is

Two facts beyond `Faithful` are needed, and **both are proved here**.

* *The interior meeting vertices of distinct row positions give distinct
  classes.*  §3 proves the source-side statement outright, with no hypothesis:
  a breakpoint of row `i` names an interior walk position
  (`breakpoint_lt`), interior walk vertices have surviving valency two
  (`rowWalk_succ_valency`), and at such a vertex only the two occurrences the
  walk joins there can meet (`eq_of_incident_interior`, from
  `W4StableSource.exists_unique_other_of_nonDanglingValency_eq_two`).  A
  repeated vertex — within one row (`rowWalk_interior_inj`) or across two
  (`rowWalk_interior_row_eq`, using `Decomposes.disjoint`) — would be a third
  surviving occurrence at a divalent vertex.  The row ends are excluded because
  `IsPathEnd` forbids valency two there.  `injective_sourceVertex` collects it:
  under `Faithful` and `Spanning` the refined core vertices sit on pairwise
  distinct quotient-source vertices.
* *The placement stays injective after the contraction.* §4. A contraction class
  is a set of quotient-source vertices joined by a walk through the face's zero
  occurrences (`reflTransGen_zeroStep_of_classOf_eq`: the canonical `rep` is
  `compFold` over the zero set). The zero set is *not* the dangling set — a face
  may contract an interior occurrence of a stable path, and a dangling
  occurrence may have positive length — so the argument is the **zero-run
  confinement**. Excursions of a zero walk into pendant trees return through the
  same bridge (`exists_step_avoiding_set`, the last departure from a set, with
  `nonDanglingValency_eq_zero_of_mem_side`: nothing on a dangling side survives
  pruning), so between two vertices that meet surviving occurrences the walk
  uses surviving zero occurrences only
  (`reflTransGen_survivingZeroStep_of_reflTransGen_zeroStep`). At an interior
  row vertex the only surviving occurrences are the two row neighbours
  (`eq_of_incident_interior`), so a surviving zero walk stays inside one row
  between two consecutive positive occurrences, or between a row end and the
  first (last) positive occurrence — it can never traverse a whole row, since
  every row has a positive occurrence (`positiveRow_ne_nil`). `Near` names those
  zero runs for each refined core vertex, `near_step` shows they are closed
  under surviving zero steps and `eq_of_near` that no other refined core vertex
  lies on them: stable placements have surviving valency `≠ 2` (`Spanning`),
  breakpoints sit strictly between consecutive positive occurrences. Then
  `eq_of_classOf_eq`: two refined core vertices whose source vertices are
  identified by the contraction are equal, which is the claim `H(M₀) = H(M)`
  read on the surviving vertices. The dangling-side lemmas
  (`nonDanglingValency_eq_zero_of_danglingSide`, `exists_step_avoiding`,
  `mem_side_of_avoiding`, `eq_of_reflTransGen_danglingStep`) are used here and
  by `PrunedContractionFibre`.

The edge multiplicities are not about `vertexClass` and are not treated here.
-/

namespace DraismaVargas.LocalCases.ClassInjectivity

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.TraversalPresentation
open DraismaVargas.LocalCases.OrientedTraversal

open Utilities
open Utilities.Certificate
open DraismaVargas.LocalCases.BalancedGlobal
open DraismaVargas.LocalCases.BalancedGlobal.Candidate
open DraismaVargas.LocalCases.InputRefinementData
open DraismaVargas.LocalCases.RefinementCore

variable {target : CFGraph} {degree : ℕ}
  {gluing : GluingDatum target degree} {wall : target.V}
  {candidate : Candidate target degree gluing wall}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  {coordinates : coordinate → ℚ}
  {n p : ℕ} {spec : SubdivisionGraph.Spec n p}
  {strong : TraversalPresentation.StrongPresentation candidate.datum coordinate}
  {face : ClearedFace candidate strong.toPresentation coordinates}
  {iface : InputInterface spec strong.toPresentation coordinates}

/-! ## 1.  The relationship to `Faithful` -/

/-- **Injectivity of `vertexClass` implies `Faithful`.**  The stable core
vertices enter `vertexClass` through `Sum.inl`, and `classOf` is a further
quotient of the quotient-source vertices, so an injective `vertexClass`
separates the placements of distinct core vertices already on the source. -/
theorem faithful_of_injective (dict : RowDictionary strong spec iface)
    {topology : ClearedFace.SourceContractionTopology face}
    (hInj : Function.Injective (RowDictionary.vertexClass dict topology)) :
    StrongRefinement.Faithful (RowDictionary.coreDictionary dict) := by
  intro v w hEq
  refine Sum.inl_injective (hInj ?_)
  show classOf topology (dict.vertexAt v) = classOf topology (dict.vertexAt w)
  exact congrArg _ hEq

/-! ## 2.  Injectivity is not derivable -/

/-- Moving a core vertex no stable slot touches — to *anywhere* — leaves a row
dictionary. -/
def reassignTo (dict : RowDictionary strong spec iface) (v : Fin n)
    (u : candidate.datum.SourceVertex)
    (hTail : ∀ i : Fin p, spec.core.tail i ≠ v)
    (hHead : ∀ i : Fin p, spec.core.head i ≠ v) :
    RowDictionary strong spec iface where
  vertexAt := Function.update dict.vertexAt v u
  tail_eq i := by
    rw [Function.update_of_ne (hTail i)]
    exact dict.tail_eq i
  head_eq i := by
    rw [Function.update_of_ne (hHead i)]
    exact dict.head_eq i

@[simp] theorem reassignTo_vertexAt (dict : RowDictionary strong spec iface)
    (v : Fin n) (u : candidate.datum.SourceVertex)
    (hTail : ∀ i : Fin p, spec.core.tail i ≠ v)
    (hHead : ∀ i : Fin p, spec.core.head i ≠ v) :
    (reassignTo dict v u hTail hHead).vertexAt =
      Function.update dict.vertexAt v u := rfl

/-- The move onto another core vertex, which makes the placement
non-injective. -/
def reassign (dict : RowDictionary strong spec iface) (v w : Fin n)
    (hTail : ∀ i : Fin p, spec.core.tail i ≠ v)
    (hHead : ∀ i : Fin p, spec.core.head i ≠ v) :
    RowDictionary strong spec iface :=
  reassignTo dict v (dict.vertexAt w) hTail hHead

@[simp] theorem reassign_vertexAt (dict : RowDictionary strong spec iface)
    (v w : Fin n) (hTail : ∀ i : Fin p, spec.core.tail i ≠ v)
    (hHead : ∀ i : Fin p, spec.core.head i ≠ v) :
    (reassign dict v w hTail hHead).vertexAt =
      Function.update dict.vertexAt v (dict.vertexAt w) := rfl

/-- Moving one point of an injective map to a value nothing else takes keeps it
injective. -/
theorem injective_update {V : Type*} {f : Fin n → V} (hf : Function.Injective f)
    (v : Fin n) (u : V) (hFree : ∀ t : Fin n, t ≠ v → f t ≠ u) :
    Function.Injective (Function.update f v u) := by
  intro a b hab
  by_cases ha : a = v <;> by_cases hb : b = v
  · rw [ha, hb]
  · rw [ha, Function.update_self, Function.update_of_ne hb] at hab
    exact absurd hab.symm (hFree b hb)
  · rw [hb, Function.update_self, Function.update_of_ne ha] at hab
    exact absurd hab (hFree a ha)
  · rw [Function.update_of_ne ha, Function.update_of_ne hb] at hab
    exact hf hab

/-- and its canonical map is not injective. -/
theorem not_injective_reassign (dict : RowDictionary strong spec iface)
    {topology : ClearedFace.SourceContractionTopology face} {v w : Fin n}
    (hTail : ∀ i : Fin p, spec.core.tail i ≠ v)
    (hHead : ∀ i : Fin p, spec.core.head i ≠ v) (hNe : v ≠ w) :
    ¬ Function.Injective
      (RowDictionary.vertexClass (reassign dict v w hTail hHead) topology) := by
  intro hInj
  refine hNe (faithful_of_injective _ hInj ?_)
  show Function.update dict.vertexAt v (dict.vertexAt w) v =
    Function.update dict.vertexAt v (dict.vertexAt w) w
  rw [Function.update_self, Function.update_of_ne (Ne.symm hNe)]

/-- **The verdict transfers.**  Whenever the stable specification leaves one
core vertex untouched by every slot — nothing in `Spec`, `StrongPresentation`
or `RowDictionary` forbids it, and `StrongRefinement.specFolded` is an
instance — every row dictionary has a sibling whose canonical `vertexClass` is
not injective.  So no argument from the fields of `RowDictionary` and a strong
presentation can prove injectivity, nor, by the same move, `Faithful`. -/
theorem exists_not_injective (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face) {v : Fin n}
    (hTail : ∀ i : Fin p, spec.core.tail i ≠ v)
    (hHead : ∀ i : Fin p, spec.core.head i ≠ v) (hCard : 1 < n) :
    ∃ other : RowDictionary strong spec iface,
      ¬ Function.Injective (RowDictionary.vertexClass other topology) := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by simpa using hCard) v
  exact ⟨reassign dict v w hTail hHead,
    not_injective_reassign dict hTail hHead (Ne.symm hw)⟩

/-! ## 3.  The breakpoints, on the source -/

section Interior

open RowDictionary

/-- **Three surviving occurrences cannot meet at a divalent vertex.**  The one
local fact `meet_eq_walkVertex_succ` turns on, isolated. -/
theorem not_three_incident {data : GluingDatum target degree}
    {w : data.SourceVertex} (hVal : nonDanglingValency data w = 2)
    {a b c : data.SourceEdge} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : ¬ IsDangling data a) (hb : ¬ IsDangling data b) (hc : ¬ IsDangling data c)
    (ia : Incident data a w) (ib : Incident data b w) (ic : Incident data c w) :
    False := by
  obtain ⟨other, -, hUnique⟩ :=
    exists_unique_other_of_nonDanglingValency_eq_two data hVal ha ia
  exact hbc ((hUnique b ⟨hab.symm, hb, ib⟩).trans (hUnique c ⟨hac.symm, hc, ic⟩).symm)

/-- A breakpoint of row `i` names an *interior* position of the walk: the
position after the positive occurrence it follows, which is before the
positive occurrence it precedes. -/
theorem breakpoint_lt
    (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)) :
    breakPosition y + 1 < (row (strong := strong) (iface := iface) y.1).length :=
  breakPosition_succ_lt y

/-- The walk vertex after an interior position has surviving valency two. -/
theorem rowWalk_succ_valency {i : Fin p} {k : ℕ}
    (hk : k + 1 < (row (strong := strong) (iface := iface) i).length) :
    nonDanglingValency candidate.datum (rowWalk strong iface i (k + 1)) = 2 :=
  walkVertex_succ_valency (row_nodup i) (row_survives i) (row_chain i)
    (row_head_isPathEnd i) hk

/-- The occurrence before an interior walk position meets it. -/
theorem rowWalk_succ_incident {i : Fin p} {k : ℕ}
    (hk : k < (row (strong := strong) (iface := iface) i).length) :
    Incident candidate.datum (row (strong := strong) (iface := iface) i)[k]
      (rowWalk strong iface i (k + 1)) :=
  walkVertex_succ_incident hk

/-- **Only the two occurrences the walk joins there meet an interior walk
vertex.**  Anything else would be a third surviving occurrence at a divalent
vertex. -/
theorem eq_of_incident_interior {i : Fin p} {k : ℕ}
    (hk : k + 1 < (row (strong := strong) (iface := iface) i).length)
    {e : candidate.datum.SourceEdge} (he : ¬ IsDangling candidate.datum e)
    (hInc : Incident candidate.datum e (rowWalk strong iface i (k + 1))) :
    e = (row (strong := strong) (iface := iface) i)[k] ∨
      e = (row (strong := strong) (iface := iface) i)[k + 1] := by
  by_contra hContra
  obtain ⟨hNe1, hNe2⟩ := not_or.mp hContra
  have hklt : k < (row (strong := strong) (iface := iface) i).length := Nat.lt_of_succ_lt hk
  have hEdgeNe : (row (strong := strong) (iface := iface) i)[k] ≠
      (row (strong := strong) (iface := iface) i)[k + 1] := by
    intro hEq
    exact absurd ((row_nodup (strong := strong) (iface := iface) i).getElem_inj_iff.mp hEq)
      (by omega)
  exact not_three_incident (rowWalk_succ_valency hk) hNe1 hNe2 hEdgeNe he
    (row_survives i _ (List.getElem_mem hklt)) (row_survives i _ (List.getElem_mem hk))
    hInc (rowWalk_succ_incident hklt)
    (rowWalk_incident (strong := strong) (iface := iface) hk)

/-- **Distinct interior positions of one row give distinct vertices.** -/
theorem rowWalk_interior_inj {i : Fin p} {k l : ℕ}
    (hk : k + 1 < (row (strong := strong) (iface := iface) i).length)
    (hl : l + 1 < (row (strong := strong) (iface := iface) i).length)
    (hEq : rowWalk strong iface i (k + 1) = rowWalk strong iface i (l + 1)) :
    k = l := by
  have hllt : l < (row (strong := strong) (iface := iface) i).length := Nat.lt_of_succ_lt hl
  have hFirst := eq_of_incident_interior hk
    (row_survives i _ (List.getElem_mem hllt))
    (hEq ▸ rowWalk_succ_incident (strong := strong) (iface := iface) hllt)
  have hSecond := eq_of_incident_interior hk
    (row_survives i _ (List.getElem_mem hl))
    (hEq ▸ rowWalk_incident (strong := strong) (iface := iface) hl)
  have hIndex : ∀ {a b : ℕ} (_ha : a < (row (strong := strong) (iface := iface) i).length)
      (_hb : b < (row (strong := strong) (iface := iface) i).length),
      (row (strong := strong) (iface := iface) i)[a] =
        (row (strong := strong) (iface := iface) i)[b] → a = b :=
    fun _ha _hb hab ↦
      (row_nodup (strong := strong) (iface := iface) i).getElem_inj_iff.mp hab
  have hIdx1 : l = k ∨ l = k + 1 := by
    rcases hFirst with h | h
    · exact Or.inl (hIndex hllt (Nat.lt_of_succ_lt hk) h)
    · exact Or.inr (hIndex hllt hk h)
  have hIdx2 : l + 1 = k ∨ l + 1 = k + 1 := by
    rcases hSecond with h | h
    · exact Or.inl (hIndex hl (Nat.lt_of_succ_lt hk) h)
    · exact Or.inr (hIndex hl hk h)
  omega

/-- **Distinct rows give distinct interior vertices.**  The rows of a
`Decomposes` presentation are disjoint, so a shared interior vertex would carry
a third surviving occurrence. -/
theorem rowWalk_interior_row_eq {i j : Fin p} {k l : ℕ}
    (hk : k + 1 < (row (strong := strong) (iface := iface) i).length)
    (hl : l + 1 < (row (strong := strong) (iface := iface) j).length)
    (hEq : rowWalk strong iface i (k + 1) = rowWalk strong iface j (l + 1)) :
    i = j := by
  by_contra hNe
  have hllt : l < (row (strong := strong) (iface := iface) j).length := Nat.lt_of_succ_lt hl
  have hMem : (row (strong := strong) (iface := iface) j)[l] ∈
      row (strong := strong) (iface := iface) j := List.getElem_mem hllt
  have hIn := eq_of_incident_interior hk (row_survives j _ hMem)
    (hEq ▸ rowWalk_succ_incident (strong := strong) (iface := iface) hllt)
  refine strong.decomposes.disjoint (iface.slot i) (iface.slot j)
    (fun hSlot ↦ hNe (iface.slot.injective hSlot))
    ((row (strong := strong) (iface := iface) j)[l]) ?_ hMem
  rcases hIn with hIn | hIn
  · exact hIn ▸ List.getElem_mem (Nat.lt_of_succ_lt hk)
  · exact hIn ▸ List.getElem_mem hk

/-- The two ends of a displayed row are path ends: neither has surviving
valency two. -/
theorem start_valency_ne_two (i : Fin p) :
    nonDanglingValency candidate.datum (strong.start (iface.slot i)) ≠ 2 :=
  (row_head_isPathEnd (strong := strong) (iface := iface) i
    (List.length_pos_of_ne_nil (strong.path_ne_nil _))).2

theorem finish_valency_ne_two (i : Fin p) :
    nonDanglingValency candidate.datum (strong.finish (iface.slot i)) ≠ 2 :=
  (row_getLast_isPathEnd (strong := strong) (iface := iface) i
    (List.length_pos_of_ne_nil (strong.path_ne_nil _))).2

/-- A spanning placement lands only on row ends, so never on an interior
vertex of a walk. -/
theorem vertexAt_valency_ne_two (dict : RowDictionary strong spec iface)
    (hSpanning : StrongRefinement.Spanning (coreDictionary dict)) (v : Fin n) :
    nonDanglingValency candidate.datum (dict.vertexAt v) ≠ 2 := by
  rcases hSpanning v with ⟨i, hi⟩ | ⟨i, hi⟩
  · show nonDanglingValency candidate.datum (dict.vertexAt v) ≠ 2
    rw [show dict.vertexAt v = strong.start (iface.slot i) from hi]
    exact start_valency_ne_two i
  · show nonDanglingValency candidate.datum (dict.vertexAt v) ≠ 2
    rw [show dict.vertexAt v = strong.finish (iface.slot i) from hi]
    exact finish_valency_ne_two i

/-! ### The canonical map, before the contraction -/

/-- **The refined core vertices, named on the quotient source.**  `vertexClass`
is this map followed by the contraction. -/
noncomputable def sourceVertex (dict : RowDictionary strong spec iface) :
    RefinedVertex (segmentData iface face) → candidate.datum.SourceVertex
  | Sum.inl v => dict.vertexAt v
  | Sum.inr y => breakVertex y

theorem vertexClass_eq_classOf (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (x : RefinedVertex (segmentData iface face)) :
    vertexClass dict topology x = classOf topology (sourceVertex dict x) := by
  match x with
  | Sum.inl _ => rfl
  | Sum.inr _ => rfl

/-- **Distinct breakpoints sit at distinct vertices.**  Their walk positions
are interior, so a shared vertex forces the same row and the same position,
hence the same positive occurrence. -/
theorem breakVertex_injective
    {y z : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1)}
    (hEq : breakVertex y = breakVertex z) : y = z := by
  obtain ⟨i, k⟩ := y
  obtain ⟨j, l⟩ := z
  have hEq' : rowWalk strong iface i (breakPosition ⟨i, k⟩ + 1) =
      rowWalk strong iface j (breakPosition ⟨j, l⟩ + 1) := hEq
  have hi : i = j :=
    rowWalk_interior_row_eq (breakpoint_lt ⟨i, k⟩) (breakpoint_lt ⟨j, l⟩) hEq'
  subst hi
  have hkl : breakPosition ⟨i, k⟩ = breakPosition ⟨i, l⟩ :=
    rowWalk_interior_inj (breakpoint_lt ⟨i, k⟩) (breakpoint_lt ⟨i, l⟩) hEq'
  have hIdx := position_injective (iface := iface) (face := face) i hkl
  have hval := congrArg Fin.val hIdx
  exact congrArg (Sigma.mk i) (Fin.ext hval)

/-- **The heart, and it is derivable.**  Given only that the placement is
injective and spanning — the two conditions `StrongRefinement` isolates for
`vertexAt` — the stable core vertices and *all* the row breakpoints sit on
pairwise distinct quotient-source vertices. Nothing about the breakpoints has to
be assumed: the interior meeting vertices of distinct row positions are distinct
because a surviving valency-two vertex carries only two surviving occurrences,
and they avoid the row ends because those are path ends. -/
theorem injective_sourceVertex (dict : RowDictionary strong spec iface)
    (hFaithful : StrongRefinement.Faithful (coreDictionary dict))
    (hSpanning : StrongRefinement.Spanning (coreDictionary dict)) :
    Function.Injective (sourceVertex (face := face) dict) := by
  intro x y hEq
  match x, y with
  | Sum.inl u, Sum.inl v => exact congrArg Sum.inl (hFaithful hEq)
  | Sum.inl u, Sum.inr y =>
      have hEq' : dict.vertexAt u = breakVertex y := hEq
      refine absurd ?_ (vertexAt_valency_ne_two dict hSpanning u)
      rw [hEq']
      exact nonDanglingValency_breakVertex y
  | Sum.inr y, Sum.inl v =>
      have hEq' : breakVertex y = dict.vertexAt v := hEq
      refine absurd ?_ (vertexAt_valency_ne_two dict hSpanning v)
      rw [← hEq']
      exact nonDanglingValency_breakVertex y
  | Sum.inr y, Sum.inr z =>
      exact congrArg Sum.inr (breakVertex_injective hEq)

end Interior


/-! ## 4.  The contraction separates the surviving vertices -/

section Separation

open DraismaVargas.LocalCases.DanglingDescent
open DraismaVargas.LocalCases.StableLocalProperties
open DraismaVargas.LocalCases.ZeroForestBridge
open DraismaVargas.LocalCases.ZeroForestPreservation
open Utilities.Certificate.ContractionForestCensusGeneral
open RowDictionary

/-! ### Two generic facts about walks -/

/-- A walk in a symmetric relation runs backwards. -/
theorem reflTransGen_symm {α : Type*} {R : α → α → Prop}
    (hSymm : ∀ {a b : α}, R a b → R b a) {x y : α}
    (h : Relation.ReflTransGen R x y) : Relation.ReflTransGen R y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hSymm hbc) ih

/-- **The last departure.**  A walk between distinct vertices can be taken to
leave its source by one step and never return to it. -/
theorem exists_step_avoiding {α : Type*} {R : α → α → Prop}
    (hSymm : ∀ {a b : α}, R a b → R b a) {u v : α}
    (h : Relation.ReflTransGen R u v) (hNe : u ≠ v) :
    ∃ z, R u z ∧
      Relation.ReflTransGen (fun a b ↦ R a b ∧ a ≠ u ∧ b ≠ u) z v := by
  have key : ∀ {y : α}, Relation.ReflTransGen R y u → y ≠ u →
      ∃ z, Relation.ReflTransGen (fun a b ↦ R a b ∧ a ≠ u ∧ b ≠ u) y z ∧ R z u := by
    intro y hy
    induction hy using Relation.ReflTransGen.head_induction_on with
    | refl => exact fun hne ↦ absurd rfl hne
    | head hstep hrest ih =>
        intro hne
        rename_i a c
        by_cases hc : c = u
        · exact ⟨a, Relation.ReflTransGen.refl, hc ▸ hstep⟩
        · obtain ⟨z, hWalk, hLast⟩ := ih hc
          exact ⟨z, Relation.ReflTransGen.head ⟨hstep, hne, hc⟩ hWalk, hLast⟩
  obtain ⟨z, hWalk, hLast⟩ := key (reflTransGen_symm hSymm h) (Ne.symm hNe)
  exact ⟨z, hSymm hLast,
    reflTransGen_symm (fun {_ _} hab ↦ ⟨hSymm hab.1, hab.2.2, hab.2.1⟩) hWalk⟩

/-- **A walk that never returns to the outer endpoint stays on the side.**  The
cut has one crossing occurrence and it ends at the outer endpoint. -/
theorem mem_side_of_avoiding {G : CFGraph} {x y : G.V}
    (cut : Utilities.SeparatingEdgeCut G x y) {w : G.V}
    (h : Relation.ReflTransGen
      (fun a b : G.V ↦ 0 < num_edges G a b ∧ b ≠ y) x w) :
    w ∈ cut.side := by
  induction h with
  | refl => exact cut.left_mem
  | @tail b c _ hbc ih =>
      by_contra hc
      have hCount := cut.cross_num_edges b c ih hc
      rw [if_neg fun hPair ↦ hbc.2 hPair.2] at hCount
      omega

/-- A walk inside an induced subgraph is a walk of the ambient graph that never
leaves the inducing set. -/
theorem reflTransGen_of_reach_induced {G : CFGraph} (S : Finset G.V)
    (hS : S.Nonempty) {a b : (Utilities.inducedSubgraph G S hS).V}
    (h : Reach (Utilities.inducedSubgraph G S hS) a b) :
    Relation.ReflTransGen
      (fun x z : G.V ↦ 0 < num_edges G x z ∧ x ∈ S ∧ z ∈ S) a.val b.val := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
      refine ih.tail ⟨?_, c.2, d.2⟩
      have heq : num_edges (Utilities.inducedSubgraph G S hS) c d
          = num_edges G c.val d.val :=
        Utilities.num_edges_inducedSubgraph G S hS c d
      omega

/-! ### Dangling cuts kill the surviving valency -/

variable {data : GluingDatum target degree}

/-- Positive edge multiplicity is carried by an actual occurrence. -/
theorem exists_sourceEnds_of_num_edges_pos (data : GluingDatum target degree)
    {a b : data.SourceVertex} (hPos : 0 < num_edges data.sourceGraph a b) :
    ∃ e : data.SourceEdge,
      data.sourceEnds e = (a, b) ∨ data.sourceEnds e = (b, a) := by
  by_contra hNone
  have hZero : num_edges data.sourceGraph a b = 0 := by
    rw [GluingDatum.SheetRelabeling.num_edges_sourceGraph_eq_sum]
    refine Finset.sum_eq_zero fun e _ ↦ ?_
    exact if_neg fun hEnds ↦ hNone ⟨e, hEnds⟩
  omega

/-- **The inner endpoint of a dangling cut has no surviving occurrence.**  The
crossing occurrence is dangling by the cut, and every other occurrence there is
dangling by `DanglingDescent.danglingSideDescent`. -/
theorem nonDanglingValency_eq_zero_of_danglingSide (data : GluingDatum target degree)
    {inner outer : data.SourceVertex}
    (cut : DanglingSide data.sourceGraph inner outer) :
    nonDanglingValency data inner = 0 := by
  obtain ⟨crossing, hCrossing⟩ :=
    exists_sourceEnds_of_num_edges_pos data
      (by rw [cut.toSeparatingEdgeCut.num_edges_endpoints]; omega)
  rw [← card_nonDanglingIncident, Finset.card_eq_zero,
    Finset.eq_empty_iff_forall_notMem]
  intro e he
  rw [mem_nonDanglingIncident] at he
  refine he.1 ?_
  by_cases hEq : e = crossing
  · exact hEq ▸ isDangling_of_danglingSide data hCrossing cut
  · obtain ⟨first, second, smaller, hEnds, -⟩ :=
      danglingSideDescent data inner outer cut crossing e hCrossing he.2 hEq
    exact isDangling_of_danglingSide data hEnds smaller

/-- **Every vertex of a dangling side has no surviving occurrence.**  Descent on
the size of the side: the inner endpoint is the previous lemma, and any other
vertex of the side lies beyond a strictly smaller dangling cut, reached by the
first step of a walk inside the side that never comes back. -/
theorem nonDanglingValency_eq_zero_of_mem_side (data : GluingDatum target degree) :
    ∀ N : ℕ, ∀ (inner outer : data.SourceVertex)
      (cut : DanglingSide data.sourceGraph inner outer),
      cut.side.card ≤ N → ∀ w ∈ cut.side, nonDanglingValency data w = 0 := by
  intro N
  induction N with
  | zero =>
      intro inner outer cut hCard _ _
      have hpos : 0 < cut.side.card := Finset.card_pos.mpr ⟨inner, cut.left_mem⟩
      have hle : cut.side.card ≤ 0 := hCard
      omega
  | succ N ih =>
      intro inner outer cut hCard w hw
      by_cases hwInner : w = inner
      · exact hwInner ▸ nonDanglingValency_eq_zero_of_danglingSide data cut
      · have hReach : Reach (Utilities.inducedSubgraph data.sourceGraph cut.side
              ⟨inner, cut.left_mem⟩) ⟨inner, cut.left_mem⟩ ⟨w, hw⟩ :=
          reach_of_graph_connected cut.side_connected _ _
        have hWalk := reflTransGen_of_reach_induced cut.side
          ⟨inner, cut.left_mem⟩ hReach
        obtain ⟨first, hStep, hAvoid⟩ :=
          exists_step_avoiding
            (R := fun x z : data.sourceGraph.V ↦
              0 < num_edges data.sourceGraph x z ∧ x ∈ cut.side ∧ z ∈ cut.side)
            (fun {_ _} hab ↦
              ⟨by rw [num_edges_symmetric]; exact hab.1, hab.2.2, hab.2.1⟩)
            hWalk (Ne.symm hwInner)
        obtain ⟨smaller, hLess⟩ :=
          exists_danglingSide_of_mem_side cut hStep.2.2 hStep.1
        have hIn : w ∈ smaller.side :=
          mem_side_of_avoiding smaller.toSeparatingEdgeCut
            (Relation.ReflTransGen.mono
              (fun _ _ hab ↦ ⟨hab.1.1, hab.2.2⟩) _ _ hAvoid)
        exact ih first inner smaller (by omega) w hIn

/-! ### Walks through contracted occurrences -/

/-- One step of a walk through occurrences the face contracts. -/
def DanglingStep (data : GluingDatum target degree) (a b : data.SourceVertex) : Prop :=
  ∃ e : data.SourceEdge, IsDangling data e ∧
    (data.sourceEnds e = (a, b) ∨ data.sourceEnds e = (b, a))

theorem danglingStep_symm {a b : data.SourceVertex} (h : DanglingStep data a b) :
    DanglingStep data b a := by
  obtain ⟨e, hDangling, hEnds⟩ := h
  exact ⟨e, hDangling, hEnds.symm⟩

theorem num_edges_pos_of_danglingStep {a b : data.SourceVertex}
    (h : DanglingStep data a b) : 0 < num_edges data.sourceGraph a b := by
  obtain ⟨e, -, hEnds⟩ := h
  exact num_edges_pos_of_sourceEnds data hEnds

/-- **The contraction identifies no two vertices that still carry a surviving
occurrence.**  Follow the walk from its last departure from `u`: its first step
is a dangling occurrence, whose cut cannot be at `u` because `u` survives, so
`u` is the *outer* endpoint; the rest of the walk never returns to `u`, so it
stays on the dangling side, where nothing survives. -/
theorem eq_of_reflTransGen_danglingStep (data : GluingDatum target degree)
    {u v : data.SourceVertex} (hu : nonDanglingValency data u ≠ 0)
    (hv : nonDanglingValency data v ≠ 0)
    (h : Relation.ReflTransGen (DanglingStep data) u v) : u = v := by
  by_contra hNe
  obtain ⟨first, hStep, hAvoid⟩ := exists_step_avoiding danglingStep_symm h hNe
  obtain ⟨e, hDangling, hEnds⟩ := hStep
  have hCut : Nonempty (DanglingSide data.sourceGraph u first) ∨
      Nonempty (DanglingSide data.sourceGraph first u) := by
    rcases hEnds with hEnds | hEnds <;> rcases hDangling with hd | hd <;>
      rw [hEnds] at hd
    · exact Or.inl hd
    · exact Or.inr hd
    · exact Or.inr hd
    · exact Or.inl hd
  rcases hCut with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    exact hu (nonDanglingValency_eq_zero_of_danglingSide data cut)
  · obtain ⟨cut⟩ := hSide
    refine hv (nonDanglingValency_eq_zero_of_mem_side data cut.side.card first u cut
      le_rfl v ?_)
    exact mem_side_of_avoiding cut.toSeparatingEdgeCut
      (Relation.ReflTransGen.mono
        (fun _ _ hab ↦ ⟨num_edges_pos_of_danglingStep hab.1, hab.2.2⟩) _ _ hAvoid)

/-- A vertex meeting a surviving occurrence has positive surviving valency. -/
theorem nonDanglingValency_ne_zero_of_incident (data : GluingDatum target degree)
    {e : data.SourceEdge} {w : data.SourceVertex} (he : ¬ IsDangling data e)
    (hInc : Incident data e w) : nonDanglingValency data w ≠ 0 := by
  intro hZero
  rw [← card_nonDanglingIncident, Finset.card_eq_zero] at hZero
  have hMem : e ∈ nonDanglingIncident data w :=
    (mem_nonDanglingIncident data w e).mpr ⟨he, hInc⟩
  rw [hZero] at hMem
  exact absurd hMem (Finset.notMem_empty e)

/-! ### The contraction, read on the source: zero steps -/

/-- One step of a walk through occurrences the face contracts. -/
def ZeroStep (face : ClearedFace candidate strong.toPresentation coordinates)
    (a b : candidate.datum.SourceVertex) : Prop :=
  ∃ e : candidate.datum.SourceEdge, face.realization.sourceLength e = 0 ∧
    (candidate.datum.sourceEnds e = (a, b) ∨ candidate.datum.sourceEnds e = (b, a))

/-- One step through a **surviving** contracted occurrence. -/
def SurvivingZeroStep (face : ClearedFace candidate strong.toPresentation coordinates)
    (a b : candidate.datum.SourceVertex) : Prop :=
  ∃ e : candidate.datum.SourceEdge, ¬ IsDangling candidate.datum e ∧
    face.realization.sourceLength e = 0 ∧
    (candidate.datum.sourceEnds e = (a, b) ∨ candidate.datum.sourceEnds e = (b, a))

theorem num_edges_pos_of_zeroStep {a b : candidate.datum.SourceVertex}
    (h : ZeroStep face a b) : 0 < num_edges candidate.datum.sourceGraph a b := by
  obtain ⟨e, -, hEnds⟩ := h
  exact num_edges_pos_of_sourceEnds candidate.datum hEnds

theorem incident_fst_of_sourceEnds {e : candidate.datum.SourceEdge}
    {a b : candidate.datum.SourceVertex}
    (hEnds : candidate.datum.sourceEnds e = (a, b) ∨ candidate.datum.sourceEnds e = (b, a)) :
    Incident candidate.datum e a := by
  rcases hEnds with hEnds | hEnds
  · exact Or.inl (by rw [hEnds])
  · exact Or.inr (by rw [hEnds])

theorem incident_snd_of_sourceEnds {e : candidate.datum.SourceEdge}
    {a b : candidate.datum.SourceVertex}
    (hEnds : candidate.datum.sourceEnds e = (a, b) ∨ candidate.datum.sourceEnds e = (b, a)) :
    Incident candidate.datum e b := by
  rcases hEnds with hEnds | hEnds
  · exact Or.inr (by rw [hEnds])
  · exact Or.inl (by rw [hEnds])

/-- The two ends of an occurrence are distinct: the quotient source is
loopless. -/
theorem sourceEnds_fst_ne_snd (e : candidate.datum.SourceEdge) :
    (candidate.datum.sourceEnds e).1 ≠ (candidate.datum.sourceEnds e).2 := by
  have h := TraversalPresentation.otherEnd_ne candidate.datum e (candidate.datum.sourceEnds e).1
  unfold otherEnd at h
  rw [if_pos rfl] at h
  exact h.symm

/-- The far end of an occurrence entered at one of its named ends is the
other named end. -/
theorem otherEnd_eq_of_sourceEnds {e : candidate.datum.SourceEdge}
    {a b : candidate.datum.SourceVertex}
    (hEnds : candidate.datum.sourceEnds e = (a, b) ∨ candidate.datum.sourceEnds e = (b, a)) :
    otherEnd candidate.datum e a = b := by
  unfold otherEnd
  have hne := sourceEnds_fst_ne_snd e
  rcases hEnds with hEnds | hEnds <;> rw [hEnds] at hne ⊢
  · rw [if_pos (rfl : (a, b).1 = a)]
  · have hne' : ¬ ((b, a).1 = a) := hne
    rw [if_neg hne']

/-- Entering an occurrence at one end and leaving by the other returns. -/
theorem otherEnd_otherEnd {e : candidate.datum.SourceEdge} {v : candidate.datum.SourceVertex}
    (hInc : Incident candidate.datum e v) :
    otherEnd candidate.datum e (otherEnd candidate.datum e v) = v := by
  have hne := sourceEnds_fst_ne_snd e
  rcases hInc with hInc | hInc
  · unfold otherEnd
    rw [if_pos hInc, if_neg hne]
    exact hInc
  · unfold otherEnd
    rw [if_neg (show ¬ ((candidate.datum.sourceEnds e).1 = v) from
      fun h ↦ hne (h.trans hInc.symm)), if_pos rfl]
    exact hInc

/-- **A contraction class is a set of vertices joined by contracted
occurrences.**  The canonical representative map is the union-find fold over
the face's zero set (`PrunedContractedSpecResidues.classOf_eq_iff`), and a
census walk through those slots is a walk of zero steps. -/
theorem reflTransGen_zeroStep_of_classOf_eq
    (topology : ClearedFace.SourceContractionTopology face)
    {u v : candidate.datum.SourceVertex}
    (hClass : classOf topology u = classOf topology v) :
    Relation.ReflTransGen (ZeroStep face) u v := by
  have hReach :=
    (ClearedFace.SourceContractionTopology.classOf_eq_iff topology u v).mp hClass
  have hWalk := (reachIn_iff_reflTransGen_slotStep candidate.datum face.realization
    face.realization.sourceZeroSet _ _).mp hReach
  have hId : ∀ x : candidate.datum.SourceVertex,
      sourceVertexOf candidate.datum (TerminalContraction.vertexIndex candidate.datum x) = x :=
    fun x ↦ Equiv.symm_apply_apply _ x
  rw [hId, hId] at hWalk
  refine Relation.ReflTransGen.mono (fun a b hab ↦ ?_) _ _ hWalk
  obtain ⟨slot, hSlot, hEnds⟩ := hab
  refine ⟨face.realization.sourceEdgeAt slot,
    (GluingDatum.NonnegativeIntegralRealization.mem_sourceZeroSet
      face.realization slot).mp hSlot, ?_⟩
  rcases hEnds with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h2 h1)

/-- **The last departure from a set.**  A walk from inside a set to outside
it can be taken to leave the set by one step and never return to it. -/
theorem exists_step_avoiding_set {α : Type*} {R : α → α → Prop} {C : Set α}
    {u v : α} (h : Relation.ReflTransGen R u v) (hu : u ∈ C) :
    v ∉ C → ∃ a ∈ C, ∃ b ∉ C, R a b ∧
      Relation.ReflTransGen (fun x y ↦ R x y ∧ x ∉ C ∧ y ∉ C) b v := by
  induction h with
  | refl => exact fun hv ↦ absurd hu hv
  | @tail y x _ hyx ih =>
      intro hx
      by_cases hy : y ∈ C
      · exact ⟨y, hy, x, hx, hyx, Relation.ReflTransGen.refl⟩
      · obtain ⟨a, ha, b, hb, hab, hWalk⟩ := ih hy
        exact ⟨a, ha, b, hb, hab, hWalk.tail ⟨hyx, hy, hx⟩⟩

/-- **Excursions into pendant trees return through their bridge.**  A walk of
zero steps between two vertices that each meet a surviving occurrence can be
taken through surviving zero occurrences only: at the last departure from the
surviving-reachable set the step is a dangling occurrence, its outer endpoint
is the surviving vertex left, and the rest of the walk, which never returns to
it, stays on the dangling side, where nothing survives. -/
theorem reflTransGen_survivingZeroStep_of_reflTransGen_zeroStep
    {u v : candidate.datum.SourceVertex}
    (hu : nonDanglingValency candidate.datum u ≠ 0)
    (hv : nonDanglingValency candidate.datum v ≠ 0)
    (h : Relation.ReflTransGen (ZeroStep face) u v) :
    Relation.ReflTransGen (SurvivingZeroStep face) u v := by
  by_contra hNot
  obtain ⟨a, ha, b, hb, hab, hAvoid⟩ := exists_step_avoiding_set
    (C := {a | Relation.ReflTransGen (SurvivingZeroStep face) u a}) h
    Relation.ReflTransGen.refl hNot
  obtain ⟨e, hZero, hEnds⟩ := hab
  have hDangling : IsDangling candidate.datum e := by
    by_contra hSurvives
    exact hb (Relation.ReflTransGen.tail ha ⟨e, hSurvives, hZero, hEnds⟩)
  have haVal : nonDanglingValency candidate.datum a ≠ 0 := by
    rcases Relation.ReflTransGen.cases_tail ha with hau | ⟨c, -, hca⟩
    · rw [hau]; exact hu
    · obtain ⟨e', hSurvives', -, hEnds'⟩ := hca
      exact nonDanglingValency_ne_zero_of_incident candidate.datum hSurvives'
        (incident_snd_of_sourceEnds hEnds')
  have hCut : Nonempty (DanglingSide candidate.datum.sourceGraph a b) ∨
      Nonempty (DanglingSide candidate.datum.sourceGraph b a) := by
    rcases hEnds with hEnds | hEnds <;> rcases hDangling with hd | hd <;>
      rw [hEnds] at hd
    · exact Or.inl hd
    · exact Or.inr hd
    · exact Or.inr hd
    · exact Or.inl hd
  rcases hCut with hSide | hSide
  · obtain ⟨cut⟩ := hSide
    exact haVal (nonDanglingValency_eq_zero_of_danglingSide candidate.datum cut)
  · obtain ⟨cut⟩ := hSide
    refine hv (nonDanglingValency_eq_zero_of_mem_side candidate.datum cut.side.card b a cut
      le_rfl v ?_)
    refine mem_side_of_avoiding cut.toSeparatingEdgeCut
      (Relation.ReflTransGen.mono (fun x y hxy ↦ ⟨num_edges_pos_of_zeroStep hxy.1, ?_⟩)
        _ _ hAvoid)
    intro hya
    exact hxy.2.2 (hya ▸ ha)

/-! ### Zero-run confinement

A surviving zero step at an interior walk vertex moves one position along the
row; at a row end it enters a row starting or ending there.  `Near dict x`
names the vertices such steps can reach from the refined core vertex `x`
without crossing a positive occurrence: for a breakpoint, the walk positions
strictly after the positive occurrence it follows and at most the one it
precedes; for a stable placement, the placement itself, the initial runs of
the rows starting there and the final runs of the rows ending there. -/

/-- The zero-run neighbourhood of a refined core vertex. -/
def Near (dict : RowDictionary strong spec iface) :
    RefinedVertex (segmentData iface face) → candidate.datum.SourceVertex → Prop
  | Sum.inl w, a => a = dict.vertexAt w ∨
      (∃ (j : Fin p) (k : ℕ), rowWalk strong iface j 0 = dict.vertexAt w ∧ 0 < k ∧
        (∀ m : Fin (positiveRow iface face j).length, k ≤ position j m) ∧
        a = rowWalk strong iface j k) ∨
      (∃ (j : Fin p) (k : ℕ),
        rowWalk strong iface j (row (strong := strong) (iface := iface) j).length =
          dict.vertexAt w ∧
        (∀ m : Fin (positiveRow iface face j).length, position j m < k) ∧
        k < (row (strong := strong) (iface := iface) j).length ∧
        a = rowWalk strong iface j k)
  | Sum.inr y, a => ∃ k : ℕ, breakPosition y < k ∧ k ≤ position y.1 (breakIndexSucc y) ∧
      a = rowWalk strong iface y.1 k

/-- Every row has a positive occurrence, so a first positive position. -/
theorem exists_positiveIndex (j : Fin p) :
    Nonempty (Fin (positiveRow iface face j).length) :=
  ⟨⟨0, List.length_pos_of_ne_nil (positiveRow_ne_nil (iface := iface) (face := face) j)⟩⟩

/-- A refined core vertex lies in its own neighbourhood. -/
theorem near_self (dict : RowDictionary strong spec iface)
    (x : RefinedVertex (segmentData iface face)) : Near dict x (sourceVertex dict x) := by
  match x with
  | Sum.inl w => exact Or.inl rfl
  | Sum.inr y =>
      refine ⟨breakPosition y + 1, Nat.lt_succ_self _, ?_, rfl⟩
      have h : position y.1 (breakIndex y) < position y.1 (breakIndexSucc y) :=
        position_lt_position_iff.mpr (by rw [Fin.lt_def]; simp)
      unfold breakPosition
      omega

/-- An interior walk vertex determines its row and its position. -/
theorem interior_eq {i j : Fin p} {k l : ℕ} (hk : 0 < k)
    (hk' : k < (row (strong := strong) (iface := iface) i).length) (hl : 0 < l)
    (hl' : l < (row (strong := strong) (iface := iface) j).length)
    (hEq : rowWalk strong iface i k = rowWalk strong iface j l) : i = j ∧ k = l := by
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have hij : i = j := rowWalk_interior_row_eq hk' hl' hEq
  subst hij
  exact ⟨rfl, congrArg (· + 1) (rowWalk_interior_inj hk' hl' hEq)⟩

/-- A walk position carrying a vertex of surviving valency `≠ 2` is a row
end. -/
theorem eq_zero_or_eq_length_of_valency_ne_two {j : Fin p} {t : ℕ}
    (ht : t ≤ (row (strong := strong) (iface := iface) j).length)
    (hVal : nonDanglingValency candidate.datum (rowWalk strong iface j t) ≠ 2) :
    t = 0 ∨ t = (row (strong := strong) (iface := iface) j).length := by
  by_contra hContra
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact hVal (rowWalk_succ_valency (by omega))

/-- The walk ends at the row's finish vertex, given a faithful dictionary
(which separates start from finish). -/
theorem rowWalk_length_of_faithful (dict : RowDictionary strong spec iface)
    (hFaithful : StrongRefinement.Faithful (coreDictionary dict)) (j : Fin p) :
    rowWalk strong iface j (row (strong := strong) (iface := iface) j).length =
      strong.finish (iface.slot j) :=
  rowWalk_length (Or.inr (StrongRefinement.start_ne_finish_of_faithful dict hFaithful j).symm)

/-- A surviving zero step, located on the row of its occurrence: it moves one
position along that row. -/
theorem step_along_row {a b : candidate.datum.SourceVertex}
    (hStep : SurvivingZeroStep face a b) :
    ∃ (j : Fin p) (t : ℕ) (ht : t < (row (strong := strong) (iface := iface) j).length),
      face.realization.sourceLength (row (strong := strong) (iface := iface) j)[t] = 0 ∧
        ((a = rowWalk strong iface j t ∧ b = rowWalk strong iface j (t + 1)) ∨
          (a = rowWalk strong iface j (t + 1) ∧ b = rowWalk strong iface j t)) := by
  obtain ⟨e, hSurvives, hZero, hEnds⟩ := hStep
  obtain ⟨r, hr⟩ := strong.decomposes.surviving_mem e hSurvives
  have hMem : e ∈ row (strong := strong) (iface := iface) (iface.slot.symm r) := by
    show e ∈ strong.toPresentation.path (iface.slot (iface.slot.symm r))
    rw [Equiv.apply_symm_apply]; exact hr
  obtain ⟨t, ht, hte⟩ := List.mem_iff_getElem.mp hMem
  refine ⟨iface.slot.symm r, t, ht, by rw [hte]; exact hZero, ?_⟩
  have hb : b = otherEnd candidate.datum e a := (otherEnd_eq_of_sourceEnds hEnds).symm
  have hInc : Incident candidate.datum e a := incident_fst_of_sourceEnds hEnds
  rw [← hte] at hb hInc
  rcases eq_or_eq_otherEnd candidate.datum
    (rowWalk_incident (strong := strong) (iface := iface) ht) hInc with hCase | hCase
  · refine Or.inl ⟨hCase, ?_⟩
    rw [hb, hCase, rowWalk_succ ht]
  · refine Or.inr ⟨by rw [hCase, rowWalk_succ ht], ?_⟩
    rw [hb, hCase, otherEnd_otherEnd (rowWalk_incident (strong := strong) (iface := iface) ht)]

/-- **The neighbourhoods are closed under surviving zero steps.** -/
theorem near_step (dict : RowDictionary strong spec iface)
    (hFaithful : StrongRefinement.Faithful (coreDictionary dict))
    (hSpanning : StrongRefinement.Spanning (coreDictionary dict))
    (x : RefinedVertex (segmentData iface face)) {a b : candidate.datum.SourceVertex}
    (hNear : Near dict x a) (hStep : SurvivingZeroStep face a b) : Near dict x b := by
  obtain ⟨j, t, ht, hZero, hCross⟩ := step_along_row hStep
  -- the vertex `a` seen from the row of the step
  have hStart : ∀ {k : ℕ} {i : Fin p}, 0 < k →
      k < (row (strong := strong) (iface := iface) i).length →
      rowWalk strong iface i k = rowWalk strong iface j 0 → False := by
    intro k i hk hk' hEq
    have h := rowWalk_succ_valency (i := i) (k := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega, hEq] at h
    exact start_valency_ne_two j h
  have hFinish : ∀ {k : ℕ} {i : Fin p}, 0 < k →
      k < (row (strong := strong) (iface := iface) i).length →
      rowWalk strong iface i k =
        rowWalk strong iface j (row (strong := strong) (iface := iface) j).length → False := by
    intro k i hk hk' hEq
    have h := rowWalk_succ_valency (i := i) (k := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega, hEq, rowWalk_length_of_faithful dict hFaithful j] at h
    exact finish_valency_ne_two j h
  -- an interior vertex of any row is not a placement
  have hPlace : ∀ {k : ℕ} {i : Fin p} {w : Fin n}, 0 < k →
      k < (row (strong := strong) (iface := iface) i).length →
      rowWalk strong iface i k = dict.vertexAt w → False := by
    intro k i w hk hk' hEq
    have h := rowWalk_succ_valency (i := i) (k := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega, hEq] at h
    exact vertexAt_valency_ne_two dict hSpanning w h
  -- a zero position is no positive position
  have hNotPos : ∀ m : Fin (positiveRow iface face j).length, position j m ≠ t := by
    intro m hm
    have h := sourceLength_position_pos (iface := iface) (face := face) j m
    subst hm
    omega
  cases x with
  | inr y =>
      obtain ⟨k, hk₁, hk₂, rfl⟩ := hNear
      have hkpos : 0 < k := by omega
      have hklt : k < (row (strong := strong) (iface := iface) y.1).length := by
        have := position_lt y.1 (breakIndexSucc y); omega
      rcases hCross with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · -- entered at position `t`, leave at `t + 1`
        have ht0 : 0 < t := by
          by_contra h0
          exact hStart hkpos hklt (by rw [ha, show t = 0 by omega])
        obtain ⟨hij, hkt⟩ := interior_eq hkpos hklt ht0 ht ha
        subst hij
        refine ⟨k + 1, by omega, ?_, by rw [hb, hkt]⟩
        have : position y.1 (breakIndexSucc y) ≠ k := by rw [hkt]; exact hNotPos _
        omega
      · -- entered at position `t + 1`, leave at `t`
        have ht1 : t + 1 < (row (strong := strong) (iface := iface) j).length := by
          by_contra h
          have hEq : t + 1 = (row (strong := strong) (iface := iface) j).length := by omega
          exact hFinish hkpos hklt (by rw [ha, hEq])
        obtain ⟨hij, hkt⟩ := interior_eq hkpos hklt (Nat.succ_pos t) ht1 ha
        subst hij
        refine ⟨t, ?_, by omega, hb⟩
        have : position y.1 (breakIndex y) ≠ t := hNotPos _
        unfold breakPosition at hk₁ ⊢
        omega
  | inl w =>
      rcases hNear with rfl | ⟨j', k, hStartEq, hkpos, hLe, rfl⟩ | ⟨j', k, hFinishEq, hLt, hklt, rfl⟩
      · -- at the placement itself
        have hVal := vertexAt_valency_ne_two dict hSpanning w
        rcases hCross with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · rw [ha] at hVal
          rcases eq_zero_or_eq_length_of_valency_ne_two ht.le hVal with rfl | rfl
          · refine Or.inr (Or.inl ⟨j, 1, ha.symm, Nat.one_pos, fun m ↦ ?_, hb⟩)
            have := hNotPos m
            omega
          · omega
        · rw [ha] at hVal
          rcases eq_zero_or_eq_length_of_valency_ne_two (by omega) hVal with h | h
          · omega
          · refine Or.inr (Or.inr ⟨j, t, by rw [← h]; exact ha.symm, fun m ↦ ?_, ht, hb⟩)
            have := position_lt (iface := iface) (face := face) j m
            have := hNotPos m
            omega
      · -- on the initial run of a row starting at the placement
        obtain ⟨m₀⟩ := exists_positiveIndex (iface := iface) (face := face) j'
        have hklt : k < (row (strong := strong) (iface := iface) j').length := by
          have := hLe m₀; have := position_lt j' m₀; omega
        rcases hCross with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have ht0 : 0 < t := by
            by_contra h0
            exact hStart hkpos hklt (by rw [ha, show t = 0 by omega])
          obtain ⟨hij, hkt⟩ := interior_eq hkpos hklt ht0 ht ha
          subst hij
          refine Or.inr (Or.inl ⟨j', k + 1, hStartEq, by omega, fun m ↦ ?_, by rw [hb, hkt]⟩)
          have := hLe m
          have : position j' m ≠ k := by rw [hkt]; exact hNotPos m
          omega
        · have ht1 : t + 1 < (row (strong := strong) (iface := iface) j).length := by
            by_contra h
            have hEq : t + 1 = (row (strong := strong) (iface := iface) j).length := by omega
            exact hFinish hkpos hklt (by rw [ha, hEq])
          obtain ⟨hij, hkt⟩ := interior_eq hkpos hklt (Nat.succ_pos t) ht1 ha
          subst hij
          rcases Nat.eq_zero_or_pos t with rfl | ht0
          · exact Or.inl (by rw [hb, hStartEq])
          · refine Or.inr (Or.inl ⟨j', t, hStartEq, ht0, fun m ↦ ?_, hb⟩)
            have := hLe m
            omega
      · -- on the final run of a row ending at the placement
        obtain ⟨m₀⟩ := exists_positiveIndex (iface := iface) (face := face) j'
        have hkpos : 0 < k := by have := hLt m₀; omega
        rcases hCross with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have ht0 : 0 < t := by
            by_contra h0
            exact hStart hkpos hklt (by rw [ha, show t = 0 by omega])
          obtain ⟨hij, hkt⟩ := interior_eq hkpos hklt ht0 ht ha
          subst hij
          by_cases hLast : k + 1 = (row (strong := strong) (iface := iface) j').length
          · have hEq : t + 1 = (row (strong := strong) (iface := iface) j').length := by omega
            exact Or.inl (by rw [hb, hEq, hFinishEq])
          · refine Or.inr (Or.inr ⟨j', k + 1, hFinishEq, fun m ↦ ?_, by omega, by rw [hb, hkt]⟩)
            have := hLt m
            omega
        · have ht1 : t + 1 < (row (strong := strong) (iface := iface) j).length := by
            by_contra h
            have hEq : t + 1 = (row (strong := strong) (iface := iface) j).length := by omega
            exact hFinish hkpos hklt (by rw [ha, hEq])
          obtain ⟨hij, hkt⟩ := interior_eq hkpos hklt (Nat.succ_pos t) ht1 ha
          subst hij
          refine Or.inr (Or.inr ⟨j', t, hFinishEq, fun m ↦ ?_, by omega, hb⟩)
          have := hLt m
          have := hNotPos m
          omega

/-- **No other refined core vertex lies on a neighbourhood.** -/
theorem eq_of_near (dict : RowDictionary strong spec iface)
    (hFaithful : StrongRefinement.Faithful (coreDictionary dict))
    (hSpanning : StrongRefinement.Spanning (coreDictionary dict))
    (x y : RefinedVertex (segmentData iface face))
    (hNear : Near dict x (sourceVertex dict y)) : x = y := by
  -- an interior vertex of a row is no placement
  have hPlace : ∀ {k : ℕ} {i : Fin p} {w : Fin n}, 0 < k →
      k < (row (strong := strong) (iface := iface) i).length →
      dict.vertexAt w = rowWalk strong iface i k → False := by
    intro k i w hk hk' hEq
    have h := rowWalk_succ_valency (i := i) (k := k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega, ← hEq] at h
    exact vertexAt_valency_ne_two dict hSpanning w h
  -- a run position is interior
  have hInitial : ∀ {j : Fin p} {k : ℕ}, 0 < k →
      (∀ m : Fin (positiveRow iface face j).length, k ≤ position j m) →
      k < (row (strong := strong) (iface := iface) j).length := by
    intro j k _ hLe
    obtain ⟨m₀⟩ := exists_positiveIndex (iface := iface) (face := face) j
    have := hLe m₀; have := position_lt j m₀; omega
  have hFinal : ∀ {j : Fin p} {k : ℕ},
      (∀ m : Fin (positiveRow iface face j).length, position j m < k) → 0 < k := by
    intro j k hLt
    obtain ⟨m₀⟩ := exists_positiveIndex (iface := iface) (face := face) j
    have := hLt m₀; omega
  cases x with
  | inl w =>
      cases y with
      | inl w' =>
          rcases hNear with h | ⟨j, k, -, hkpos, hLe, h⟩ | ⟨j, k, -, hLt, hklt, h⟩
          · exact congrArg Sum.inl (hFaithful h).symm
          · exact absurd h (fun h ↦ hPlace hkpos (hInitial hkpos hLe) h)
          · exact absurd h (fun h ↦ hPlace (hFinal hLt) hklt h)
      | inr y' =>
          have hpos := breakpoint_lt (iface := iface) (face := face) y'
          rcases hNear with h | ⟨j, k, -, hkpos, hLe, h⟩ | ⟨j, k, -, hLt, hklt, h⟩
          · exact absurd h.symm (fun h ↦ hPlace (Nat.succ_pos _) hpos h)
          · obtain ⟨hij, hk⟩ := interior_eq hkpos (hInitial hkpos hLe) (Nat.succ_pos _) hpos h.symm
            subst hij
            have := hLe (breakIndex y')
            unfold breakPosition at hk
            omega
          · obtain ⟨hij, hk⟩ := interior_eq (hFinal hLt) hklt (Nat.succ_pos _) hpos h.symm
            subst hij
            have := hLt (breakIndexSucc y')
            have hMono : position y'.1 (breakIndex y') < position y'.1 (breakIndexSucc y') :=
              position_lt_position_iff.mpr (by rw [Fin.lt_def]; simp)
            unfold breakPosition at hk
            omega
  | inr z =>
      obtain ⟨k, hk₁, hk₂, h⟩ := hNear
      have hklt : k < (row (strong := strong) (iface := iface) z.1).length := by
        have := position_lt z.1 (breakIndexSucc z); omega
      cases y with
      | inl w' => exact absurd h (fun h ↦ hPlace (by omega) hklt h)
      | inr y' =>
          have hpos := breakpoint_lt (iface := iface) (face := face) y'
          obtain ⟨hij, hk⟩ := interior_eq (by omega) hklt (Nat.succ_pos _) hpos h.symm
          obtain ⟨i, kz⟩ := z
          obtain ⟨i', ky⟩ := y'
          have hii : i = i' := hij
          subst hii
          have h1 : position i (breakIndex ⟨i, kz⟩) < k := hk₁
          have h2 : k ≤ position i (breakIndexSucc ⟨i, kz⟩) := hk₂
          have h3 : k = position i (breakIndex ⟨i, ky⟩) + 1 := hk
          have h₁' := position_le_position_iff.mp
            (show position i (breakIndex ⟨i, kz⟩) ≤ position i (breakIndex ⟨i, ky⟩) by omega)
          have h₂' := position_lt_position_iff.mp
            (show position i (breakIndex ⟨i, ky⟩) < position i (breakIndexSucc ⟨i, kz⟩) by omega)
          rw [Fin.le_def] at h₁'
          rw [Fin.lt_def] at h₂'
          simp only [breakIndex_val, breakIndexSucc_val] at h₁' h₂'
          exact congrArg (fun t ↦ Sum.inr (Sigma.mk i t)) (Fin.ext (by omega))

/-- Every refined core vertex sits on a quotient-source vertex that still
carries a surviving occurrence. -/
theorem sourceVertex_valency_ne_zero (dict : RowDictionary strong spec iface)
    (hSpanning : StrongRefinement.Spanning (coreDictionary dict))
    (x : RefinedVertex (segmentData iface face)) :
    nonDanglingValency candidate.datum (sourceVertex dict x) ≠ 0 := by
  match x with
  | Sum.inl v =>
      show nonDanglingValency candidate.datum (dict.vertexAt v) ≠ 0
      rcases hSpanning v with ⟨i, hi⟩ | ⟨i, hi⟩
      · rw [show dict.vertexAt v = strong.start (iface.slot i) from hi]
        exact (nonDanglingValency_start_pos i).ne'
      · rw [show dict.vertexAt v = strong.finish (iface.slot i) from hi]
        exact (nonDanglingValency_finish_pos i).ne'
  | Sum.inr y =>
      show nonDanglingValency candidate.datum (breakVertex y) ≠ 0
      rw [nonDanglingValency_breakVertex y]
      omega

/-- **The placement stays injective after the contraction.**  Two refined core
vertices whose source vertices the face's contraction identifies are equal:
the zero walk joining them uses surviving zero occurrences only, hence stays on
the first vertex's zero runs, on which no other refined core vertex lies. -/
theorem eq_of_classOf_eq (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hFaithful : StrongRefinement.Faithful (coreDictionary dict))
    (hSpanning : StrongRefinement.Spanning (coreDictionary dict))
    {x y : RefinedVertex (segmentData iface face)}
    (hClass : classOf topology (sourceVertex dict x) = classOf topology (sourceVertex dict y)) :
    x = y := by
  have hWalk := reflTransGen_survivingZeroStep_of_reflTransGen_zeroStep
    (sourceVertex_valency_ne_zero dict hSpanning x)
    (sourceVertex_valency_ne_zero dict hSpanning y)
    (reflTransGen_zeroStep_of_classOf_eq topology hClass)
  have key : ∀ b, Relation.ReflTransGen (SurvivingZeroStep face) (sourceVertex dict x) b →
      Near dict x b := by
    intro b h
    induction h with
    | refl => exact near_self dict x
    | tail _ hStep ih => exact near_step dict hFaithful hSpanning x ih hStep
  exact eq_of_near dict hFaithful hSpanning x y (key _ hWalk)

end Separation


/-! ## 5.  The verdict -/

section Verdict

open RowDictionary

/-- A row end meets the first occurrence of its row, which survives. -/
theorem start_valency_ne_zero (i : Fin p) :
    nonDanglingValency candidate.datum (strong.start (iface.slot i)) ≠ 0 :=
  (nonDanglingValency_start_pos (iface := iface) i).ne'

theorem finish_valency_ne_zero (i : Fin p) :
    nonDanglingValency candidate.datum (strong.finish (iface.slot i)) ≠ 0 :=
  (nonDanglingValency_finish_pos (iface := iface) i).ne'

/-- **`Faithful` is the whole of it.**  For a spanning placement, injectivity of
the canonical `vertexClass` follows from injectivity of `vertexAt` alone: the
breakpoints take care of themselves (§3) and the contraction identifies none of
these vertices (§4). -/
theorem injective_vertexClass_of_faithful (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hFaithful : StrongRefinement.Faithful (coreDictionary dict))
    (hSpanning : StrongRefinement.Spanning (coreDictionary dict)) :
    Function.Injective (vertexClass dict topology) := by
  intro x y hEq
  refine eq_of_classOf_eq dict topology hFaithful hSpanning ?_
  rw [← vertexClass_eq_classOf, ← vertexClass_eq_classOf]
  exact hEq

/-- **The verdict.**  With the placement spanning, injectivity of `vertexClass`
*is* `StrongRefinement.Faithful` — neither stronger nor weaker.  So the local
half of the bijectivity hypothesis is exactly that condition, and nothing about
the row breakpoints or the contraction has to be carried. -/
theorem injective_vertexClass_iff (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hSpanning : StrongRefinement.Spanning (coreDictionary dict)) :
    Function.Injective (vertexClass dict topology) ↔
      StrongRefinement.Faithful (coreDictionary dict) :=
  ⟨faithful_of_injective dict, fun hFaithful ↦
    injective_vertexClass_of_faithful dict topology hFaithful hSpanning⟩

/-- **`Spanning` cannot be dropped.**  A core vertex no stable slot touches may
be placed on an interior breakpoint of a row; the placement stays *faithful* —
it is still injective — and yet `vertexClass` identifies that core vertex with
the breakpoint.  So injectivity of `vertexClass` is strictly stronger than
`Faithful` in general, and §5's equivalence is sharp: it is the spanning
hypothesis, not the faithful one, that the breakpoints need. -/
theorem exists_faithful_not_injective (dict : RowDictionary strong spec iface)
    (topology : ClearedFace.SourceContractionTopology face)
    (hFaithful : StrongRefinement.Faithful (coreDictionary dict)) {v : Fin n}
    (hTail : ∀ i : Fin p, spec.core.tail i ≠ v)
    (hHead : ∀ i : Fin p, spec.core.head i ≠ v)
    (y : Σ i : Fin p, Fin (((segmentData iface face).segments i).length - 1))
    (hFree : ∀ t : Fin n, t ≠ v → dict.vertexAt t ≠ breakVertex y) :
    ∃ other : RowDictionary strong spec iface,
      StrongRefinement.Faithful (coreDictionary other) ∧
        ¬ Function.Injective (vertexClass other topology) := by
  refine ⟨reassignTo dict v (breakVertex y) hTail hHead,
    injective_update hFaithful v _ hFree, fun hInj ↦ ?_⟩
  have hClash : vertexClass (reassignTo dict v (breakVertex y) hTail hHead)
        topology (Sum.inl v) =
      vertexClass (reassignTo dict v (breakVertex y) hTail hHead) topology (Sum.inr y) := by
    show classOf topology (Function.update dict.vertexAt v (breakVertex y) v) = _
    rw [Function.update_self]
    rfl
  exact absurd (hInj hClash) (by simp)

end Verdict

end DraismaVargas.LocalCases.ClassInjectivity
