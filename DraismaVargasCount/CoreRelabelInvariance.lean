module

public import DraismaVargasCount.CoreChainSites

@[expose] public section

/-!
# Relabelling invariance of the open odd count

**Source.**  Vargas, Part II (arXiv:2609.09109), section *Invariance of the count
via continuous deformation*: the count is carried from core to core, and a chain
of Whitehead moves reaches the target core only up to relabelling.

`CoreChainSites.RelabelInvariant degree` is an equivariance statement about
`GeometricFibre.openOddCount` under a slot permutation, a vertex permutation and
per-slot orientation flips; `CoreChainSites.exists_siteChain` is stated without
it.  This file proves it.  `CoreChainSites.RelabelInvariant degree` holds for
every `degree`, with no hypothesis whatsoever, and the two theorems that use it
(`exists_siteChain_to_target`, `odd_of_chain`) are restated here with that
hypothesis discharged.

## Why it is cheap, and where the work actually is

A `FibreMember core y degree` mentions `core` in exactly two places: the
identification `ident : CoreIdentification core data` of the stable graph of the
gluing datum with the core, and the realization equation `A_φ z = y ∘ ident.row`.
Everything else -- the target tree, the gluing datum, the full-dimensionality
receipt, the coordinate vector -- is *independent of the core*.

So a relabelling does not move a member at all: it only re-reads the label.
`relabelMember` keeps `target`, `data`, `fullDim` and `coords` on the nose and
replaces `ident.vertex` by `ident.vertex.trans vtx` and `ident.row` by
`ident.row.trans slot`.  The three obligations are then:

* the identification's `incidence` field, which needs exactly
  `coreIncidence c' (vtx v) (slot e) = coreIncidence c v e` -- the *only*
  property of the relabelling that is used anywhere in this file;
* the realization equation, which survives because
  `y' (slot (ident.row x)) = y (ident.row x)` is the hypothesis `hy`;
* descent to the quotient, which is free: `GeometricMemberIso` is a
  `GeometricDatumIso` of the *data* together with two conditions saying the
  identifications agree, and postcomposing both sides of those conditions with
  `vtx` resp. `slot` is `congrArg`.

`Open` and `IsOdd` then cost nothing at all -- `Open` reads `coords`, and
`multNat` reads `fullDim`, and neither field moved -- so the induced bijection of
`GeometricFibre`s restricts to the open odd classes and `Nat.card` is equal.

Because only the incidence identity is used, the invariance is packaged over an
`Relabel` datum (slot permutation + vertex permutation + incidence identity) that
is deliberately *smaller* than `CoreOfDarts.CoreIso`.  `Relabel.ofCoreIso` and
`Relabel.toCoreIso` show the two are nonetheless interchangeable: the per-slot
orientation flag of a `CoreIso` is recovered from the incidence identity, so
nothing is gained or lost either way and the invariance is proved at exactly the
strength `CoreChainSites.RelabelInvariant` asks for.

## The `ReachesIso`/`Reaches` gap, settled

`exists_chain` ends at a core `CoreIso`-related to the target because
`CubicDarts.reachesIso_of_genus_eq` concludes `ReachesIso`, not `Reaches`.

**The gap is real and it does not obstruct the count.**  It is bridged, not closed: the
count does not distinguish the two ends of a `CoreIso`, which is what
`relabelInvariant` says, so no `Reaches`-level connectivity theorem is needed by
the count.

For the record, §9 pins down what a `Reaches`-level statement would have to say.
`exists_perm_of_reaches` proves that a whole Whitehead chain keeps `op` and
replaces `vert` by `vert ∘ π` for a single permutation `π` of *darts*; on cores
that is `exists_perm_of_step_chain`.  Since any two cubic cores on the same `n`
and `p` have all vertex fibres of size three, `c'.vert = c.vert ∘ π` does hold
for *some* `π` of darts (a counting remark, not formalized here), so the missing
`Reaches`-level statement is precisely:
*every such `π` is a product of legal Whitehead transpositions, each legal for
the graph it is applied to.*  That is a statement about the Whitehead move
groupoid acting on **labelled** cores; it is not proved in this library, and this
file removes the count's need for it.

## What is proved here

* `Relabel`, `Relabel.symm`, `Relabel.ofCoreIso`, `Relabel.toCoreIso` -- the
  minimal relabelling interface and its equivalence with `CoreIso`.
* `relabelIdent`, `relabelMember`, `relabelIso`, `relabelCls`, `relabelEquiv` --
  the relabelling of a member, of an isomorphism over the core, and of the
  geometric fibre, and the fact that it is a bijection.
* `relabelCls_open`, `relabelCls_isOdd`, `relabelOpenOddEquiv`,
  `openOddCount_relabel` -- openness and the parity of the multiplicity are
  untouched, so the count is.
* `relabelInvariant` -- **`CoreChainSites.RelabelInvariant degree`, for every
  `degree`, unconditionally.**
* `exists_siteChain_to_target`, `odd_of_chain` -- the two consequences for chains
  of sites, with the relabelling hypothesis discharged.
* `exists_perm_of_reaches`, `exists_perm_of_step_chain` -- the structure of a
  Whitehead chain, as described above.

## What is NOT proved here -- every hypothesis

* **`CoreChainSites.StepSupply`** (the parity at trivalent walls and at type
  changes together) is a hypothesis of `exists_siteChain_to_target` and
  `odd_of_chain`, exactly as in `CoreChainSites`.  Nothing here produces a link
  at an actual wall, and nothing here assumes a wall is trivalent.
* **`2 ≤ p + 1 - n`**, the genus bound of `reachesIso_of_genus_eq`, is a
  hypothesis of those two theorems.  `openOddCount_relabel` and
  `relabelInvariant` themselves assume *nothing*: no genus bound, no cubicity,
  no connectedness, no genericity of the request, no nonemptiness of the fibre.
* **No `Reaches`-level connectivity statement is proved.**  §9 says exactly what
  one would have to say; it is not claimed, and the count does not need it.
* No genericity of the requests is asserted or used.  `openOddCount` is a
  cardinality, never a parity: nothing here claims it is odd.

Consumers: the chains of sites of `CoreChainSites`, and through them
`CountSchedule.C34`.
-/

namespace DraismaVargas.Count.CoreRelabel

open DraismaVargas.Infrastructure
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.CoreOfDarts (CoreIso)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p degree : ℕ}

/-! ## 1.  The incidence-preserving relabelling datum -/

/-- A relabelling of one core by another: a slot permutation and a vertex
permutation that together preserve every incidence multiplicity. -/
structure Relabel (c c' : Core n p) where
  /-- the slot permutation -/
  slot : Fin p ≃ Fin p
  /-- the vertex permutation -/
  vtx : Fin n ≃ Fin n
  /-- incidence multiplicities are matched -/
  incidence : ∀ (v : Fin n) (e : Fin p), coreIncidence c' (vtx v) (slot e) = coreIncidence c v e

namespace Relabel

variable {c c' : Core n p}

/-- The inverse relabelling. -/
def symm (d : Relabel c c') : Relabel c' c where
  slot := d.slot.symm
  vtx := d.vtx.symm
  incidence := by
    intro v e
    have h := d.incidence (d.vtx.symm v) (d.slot.symm e)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact h.symm

@[simp] theorem symm_slot (d : Relabel c c') : d.symm.slot = d.slot.symm := rfl
@[simp] theorem symm_vtx (d : Relabel c c') : d.symm.vtx = d.vtx.symm := rfl

/-- The inverse of the inverse is the original, definitionally. -/
theorem symm_symm (d : Relabel c c') : d.symm.symm = d := rfl

end Relabel

/-- A `CoreIso` preserves incidence multiplicities. -/
theorem coreIncidence_coreIso {c c' : Core n p} (i : CoreIso c c') (v : Fin n) (e : Fin p) :
    coreIncidence c' (i.vtx v) (i.slot e) = coreIncidence c v e := by
  rcases i.orientation e with ⟨ht, hh⟩ | ⟨hh, ht⟩
  · rw [coreIncidence, coreIncidence, ht, hh]
    simp only [Equiv.apply_eq_iff_eq]
  · rw [coreIncidence, coreIncidence, ht, hh]
    simp only [Equiv.apply_eq_iff_eq]
    exact Nat.add_comm _ _

/-- Every core relabelling in the sense of `CoreOfDarts.CoreIso` is one here. -/
def Relabel.ofCoreIso {c c' : Core n p} (i : CoreIso c c') : Relabel c c' where
  slot := i.slot
  vtx := i.vtx
  incidence := coreIncidence_coreIso i

@[simp] theorem Relabel.ofCoreIso_slot {c c' : Core n p} (i : CoreIso c c') :
    (Relabel.ofCoreIso i).slot = i.slot := rfl

/-! ## 1a.  `Relabel` is exactly `CoreIso`, so nothing is lost either way -/

theorem coreIncidence_eq (core : Core n p) (v : Fin n) (e : Fin p) :
    coreIncidence core v e =
      (if core.tail e = v then 1 else 0) + (if core.head e = v then 1 else 0) := rfl

/-- If the image slot's tail is not the image of the slot's tail, its head is. -/
theorem Relabel.head_eq_of_tail_ne {c c' : Core n p} (d : Relabel c c') (e : Fin p)
    (h : c'.tail (d.slot e) ≠ d.vtx (c.tail e)) :
    c'.head (d.slot e) = d.vtx (c.tail e) := by
  by_contra hc
  have key := d.incidence (c.tail e) e
  rw [coreIncidence_eq, coreIncidence_eq, ite_eq_right h, ite_eq_right hc] at key
  split_ifs at key with h1 h2 <;> omega

/-- **Nothing is lost in passing to `Relabel`**: an incidence-preserving pair of
permutations already carries the per-slot orientation flag, so it is a
`CoreOfDarts.CoreIso`.  Together with `Relabel.ofCoreIso` this says the two
interfaces are interchangeable, and the invariance below is therefore proved at
exactly the strength `CoreChainSites.RelabelInvariant` asks for. -/
def Relabel.toCoreIso {c c' : Core n p} (d : Relabel c c') : CoreIso c c' where
  slot := d.slot
  vtx := d.vtx
  flip := fun e ↦ !decide (c'.tail (d.slot e) = d.vtx (c.tail e))
  tail_map := by
    intro e
    by_cases h : c'.tail (d.slot e) = d.vtx (c.tail e)
    · simp only [h, decide_true, Bool.not_true]
      exact h
    · simp only [h, decide_false, Bool.not_false]
      exact d.head_eq_of_tail_ne e h
  head_map := by
    intro e
    by_cases h : c'.tail (d.slot e) = d.vtx (c.tail e)
    · simp only [h, decide_true, Bool.not_true, Bool.not_false]
      show c'.head (d.slot e) = d.vtx (c.head e)
      have key := d.incidence (c.head e) e
      rw [coreIncidence_eq, coreIncidence_eq, ite_eq_left (rfl : c.head e = c.head e)] at key
      by_contra hc
      rw [ite_eq_right hc] at key
      by_cases hl : c.tail e = c.head e
      · rw [ite_eq_left hl] at key
        split_ifs at key <;> omega
      · have hne : c'.tail (d.slot e) ≠ d.vtx (c.head e) := by
          rw [h]
          exact fun hx ↦ hl (d.vtx.injective hx)
        rw [ite_eq_right hl, ite_eq_right hne] at key
        omega
    · simp only [h, decide_false, Bool.not_false, Bool.not_true]
      show c'.tail (d.slot e) = d.vtx (c.head e)
      have hhead := d.head_eq_of_tail_ne e h
      have key := d.incidence (c.head e) e
      rw [coreIncidence_eq, coreIncidence_eq, ite_eq_left (rfl : c.head e = c.head e)] at key
      by_contra hc
      rw [ite_eq_right hc] at key
      by_cases hl : c.tail e = c.head e
      · rw [ite_eq_left hl,
          ite_eq_left (by rw [hhead, hl] : c'.head (d.slot e) = d.vtx (c.head e))] at key
        omega
      · have hne : c'.head (d.slot e) ≠ d.vtx (c.head e) := fun hx ↦
          hl (d.vtx.injective (hhead.symm.trans hx))
        rw [ite_eq_right hl, ite_eq_right hne] at key
        omega

/-! ## 2.  Relabelling a member -/

variable {c c' : Core n p} {y y' : Fin p → ℚ}

/-- The core identification, relabelled. -/
def relabelIdent (d : Relabel c c') {target : CFGraph.{0}} {data : GluingDatum target degree}
    (id0 : CoreIdentification c data) : CoreIdentification c' data where
  vertex := id0.vertex.trans d.vtx
  row := id0.row.trans d.slot
  incidence := by
    intro branch slot
    have h := id0.incidence branch (d.slot.symm slot)
    have key := d.incidence (id0.vertex branch) (d.slot.symm slot)
    rw [Equiv.apply_symm_apply] at key
    simp only [Equiv.symm_trans_apply, Equiv.trans_apply]
    rw [h, key]

/-- **A member of the fibre, relabelled.**  Target, datum, full-dimensionality
receipt and coordinates are untouched; only the identification with the core
moves. -/
def relabelMember (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e)
    (m : FibreMember c y degree) : FibreMember c' y' degree where
  target := m.target
  data := m.data
  fullDim := m.fullDim
  ident := relabelIdent d m.ident
  coords := m.coords
  realizes := by
    refine m.realizes.trans ?_
    funext row
    exact (hy _).symm

/-! ## 3.  The relabelling descends to the geometric fibre -/

/-- Relabelling carries an isomorphism over the core to an isomorphism over the
relabelled core: the gluing datum is untouched, so the same `GeometricDatumIso`
serves, and the two `over`-conditions are the old ones composed with the two
permutations. -/
def relabelIso (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e)
    {first second : FibreMember c y degree} (iso : GeometricMemberIso first second) :
    GeometricMemberIso (relabelMember d hy first) (relabelMember d hy second) where
  datum := iso.datum
  overCore_vertex branch := congrArg d.vtx (iso.overCore_vertex branch)
  overCore_row path := congrArg d.slot (iso.overCore_row path)

/-- **The relabelling on classes.** -/
def relabelCls (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e) :
    GeometricFibre c y degree → GeometricFibre c' y' degree := fun x ↦
  Quotient.liftOn x (fun m ↦ GeometricFibre.cls (relabelMember d hy m))
    fun _ _ h ↦ h.elim fun iso ↦
      GeometricFibre.cls_eq_cls_iff.mpr ⟨relabelIso d hy iso⟩

@[simp] theorem relabelCls_cls (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e)
    (m : FibreMember c y degree) :
    relabelCls d hy (GeometricFibre.cls m) = GeometricFibre.cls (relabelMember d hy m) := rfl

/-- The request transported by the inverse relabelling. -/
theorem symm_request (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e) :
    ∀ e, y (d.symm.slot e) = y' e := by
  intro e
  have h := hy (d.slot.symm e)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-! ## 4.  The relabelling is a bijection -/

/-- The round trip on a member is the identity up to an isomorphism over the
core: the datum is literally unchanged, and the two permutations cancel. -/
def relabelRoundTrip (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e)
    (m : FibreMember c y degree) :
    GeometricMemberIso (relabelMember d.symm (symm_request d hy) (relabelMember d hy m)) m where
  datum := GeometricDatumIso.refl m.data
  overCore_vertex branch := (d.vtx.symm_apply_apply (m.ident.vertex branch)).symm
  overCore_row path := by
    show m.ident.row ((GeometricDatumIso.refl m.data).stablePathEquiv m.fullDim.valid.1 path) =
      d.slot.symm (d.slot (m.ident.row path))
    rw [GeometricDatumIso.stablePathEquiv_refl]
    exact (d.slot.symm_apply_apply (m.ident.row path)).symm

theorem relabelCls_symm_relabelCls (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e)
    (x : GeometricFibre c y degree) :
    relabelCls d.symm (symm_request d hy) (relabelCls d hy x) = x := by
  induction x using Quotient.inductionOn with
  | h m => exact GeometricFibre.cls_eq_cls_iff.mpr ⟨relabelRoundTrip d hy m⟩

theorem relabelCls_relabelCls_symm (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e)
    (z : GeometricFibre c' y' degree) :
    relabelCls d hy (relabelCls d.symm (symm_request d hy) z) = z :=
  relabelCls_symm_relabelCls d.symm (symm_request d hy) z

/-- **The relabelling of the geometric fibre, as an equivalence.** -/
def relabelEquiv (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e) :
    GeometricFibre c y degree ≃ GeometricFibre c' y' degree where
  toFun := relabelCls d hy
  invFun := relabelCls d.symm (symm_request d hy)
  left_inv := relabelCls_symm_relabelCls d hy
  right_inv := relabelCls_relabelCls_symm d hy

/-! ## 5.  Openness and the parity of the multiplicity are untouched -/

theorem relabelCls_open (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e)
    (x : GeometricFibre c y degree) :
    (relabelCls d hy x).Open ↔ x.Open := by
  induction x using Quotient.inductionOn with
  | h m => exact Iff.rfl

theorem relabelCls_isOdd (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e)
    (x : GeometricFibre c y degree) :
    (relabelCls d hy x).IsOdd ↔ x.IsOdd := by
  induction x using Quotient.inductionOn with
  | h m => exact Iff.rfl

/-- The relabelling restricted to the open, odd-multiplicity classes. -/
def relabelOpenOddEquiv (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e) :
    {x : GeometricFibre c y degree // x.Open ∧ x.IsOdd} ≃
      {x : GeometricFibre c' y' degree // x.Open ∧ x.IsOdd} :=
  (relabelEquiv d hy).subtypeEquiv fun x ↦
    and_congr (relabelCls_open d hy x).symm (relabelCls_isOdd d hy x).symm

/-! ## 6.  The invariance of the count -/

/-- **The open odd count is a relabelling invariant.** -/
theorem openOddCount_relabel (d : Relabel c c') (hy : ∀ e, y' (d.slot e) = y e) (degree : ℕ) :
    GeometricFibre.openOddCount c y degree = GeometricFibre.openOddCount c' y' degree :=
  Nat.card_congr (relabelOpenOddEquiv d hy)

/-! ## 7.  `CoreChainSites.RelabelInvariant`, discharged -/

/-- **`CoreChainSites.RelabelInvariant`, proved.** -/
theorem relabelInvariant (degree : ℕ) : CoreChainSites.RelabelInvariant degree := by
  intro n p c c' i y
  refine openOddCount_relabel (Relabel.ofCoreIso i) ?_ degree
  intro e
  exact congrArg y (i.slot.symm_apply_apply e)

/-! ## 8.  The chain consequences, with `RelabelInvariant` discharged -/

open DraismaVargas.LocalCases.CoreOfDarts (CubicCore)
open DraismaVargas.Count.CountSchedule (Site)

/-- `CoreChainSites.exists_siteChain_to_target` with its relabelling hypothesis
discharged: only `StepSupply` (the parity at trivalent walls and at type
changes) remains. -/
theorem exists_siteChain_to_target (hsupply : CoreChainSites.StepSupply degree n p)
    (hGenus : 2 ≤ p + 1 - n) (c c' : CubicCore n p) (y : Fin p → ℚ) :
    ∃ y' : Fin p → ℚ, Relation.ReflTransGen (Site.Link (degree := degree))
      (CoreChainSites.siteOf degree c y) (CoreChainSites.siteOf degree c' y') :=
  CoreChainSites.exists_siteChain_to_target (relabelInvariant degree) hsupply hGenus c c' y

/-- `CoreChainSites.odd_of_chain` with its relabelling hypothesis discharged. -/
theorem odd_of_chain (hsupply : CoreChainSites.StepSupply degree n p)
    (hGenus : 2 ≤ p + 1 - n) (c c' : CubicCore n p) (y : Fin p → ℚ)
    (hodd : Odd (GeometricFibre.openOddCount c.core y degree)) :
    ∃ y' : Fin p → ℚ, Odd (GeometricFibre.openOddCount c'.core y' degree) :=
  CoreChainSites.odd_of_chain (relabelInvariant degree) hsupply hGenus c c' y hodd

/-! ## 9.  What a `Reaches`-level statement would have to say -/

open DraismaVargas.Infrastructure.CubicDarts
open DraismaVargas.Infrastructure.CubicDarts.CubicDartGraph
open DraismaVargas.LocalCases.CubicCoreDarts (vertex)
open DraismaVargas.LocalCases.CoreOfDarts (Step)

/-- **Exactly what a Whitehead chain does.**  Every `Reaches` chain keeps the
edge involution and replaces the vertex map by its precomposition with a single
permutation of darts.  This is the machine-checked form of the informal remark
that a move "changes `vert` alone". -/
theorem exists_perm_of_reaches {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V]
    [DecidableEq V] {G H : CubicDartGraph D V} (h : Reaches G H) :
    ∃ π : Equiv.Perm D, H.op = G.op ∧ ∀ d, H.vert d = G.vert (π d) := by
  induction h with
  | refl => exact ⟨Equiv.refl D, rfl, fun _ ↦ rfl⟩
  | tail _ hmove ih =>
      obtain ⟨π, hop, hvert⟩ := ih
      obtain ⟨m, rfl⟩ := hmove
      exact ⟨m.perm.trans π, hop, fun d ↦ hvert (m.perm d)⟩

/-- The same fact on cores: a chain of core Whitehead steps moves the dart-to-vertex
map by precomposition with a dart permutation, and by nothing else. -/
theorem exists_perm_of_step_chain {c c' : CubicCore n p}
    (h : Relation.ReflTransGen Step c c') :
    ∃ π : Equiv.Perm (Fin p × Bool), ∀ d, vertex c'.core d = vertex c.core (π d) := by
  have hreach : Reaches c.graph c'.graph :=
    Relation.ReflTransGen.lift CubicCore.graph (fun _ _ hs ↦ hs) _ _ h
  obtain ⟨π, _, hvert⟩ := exists_perm_of_reaches hreach
  exact ⟨π, hvert⟩

end DraismaVargas.Count.CoreRelabel
