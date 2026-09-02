import Utilities.Subdivision.ContractionForestCensusGeneral
import Utilities.Subdivision.CubicCore
import Utilities.Subdivision.DegenerateSlopeScript

/-!
# The canonical divisor of a closed subdivision face

On a **cubic** ordered core, the canonical divisor of every nonloopy forest
face is the core-class divisor of the **all-ones** weight:

```text
canonical_divisor d.graph = d.coreClassDivisor (fun _ => 1).
```

The computation is a two-line count once the bookkeeping is in place.  A
contracted class `C` holding `k` core vertices is spanned by exactly `k - 1`
zero-length slots, each of which absorbs two of the `3k` slot ends of `C`, so
the class has degree `3k - 2(k-1) = k + 2` and canonical value `k`; an
interior vertex of a surviving slot has degree two and canonical value zero.

The only nontrivial input is `card_classZeroSlots_add_one`: the zero slots
*inside one class* number exactly one less than the class.  That is the
localization of the `DegSpec.forest` cardinality equation, and it needs the
representative map to be genuine zero-slot reachability — the bare `forest`
field alone cannot see it, because it is a single global equation.

## Why this file exists

Two consumers, at two different genera.

* `deg (coreClassDivisor w) = ∑ w` and `genus d.graph = p - n + 1`, so on a
  cubic core the *complementary* weight `1 - w` has degree `(n - ∑ w)`.  When
  `∑ w = p - n = genus - 1` both weights sit at the Serre-self-dual degree and
  `rank_coreClassDivisor_eq_complement` says they have **equal rank on every
  face**.  A degree-four witness on a genus-five cubic core therefore comes
  with a second, disjointly supported one for free, and likewise a
  degree-three witness on a genus-four cubic core.
* Nothing here is specific to genus five, to `LowGenus`, or to a divisor of
  any particular degree.
-/

namespace Utilities.Certificate.DegenerateSpec.DegSpec

open Utilities
open Finset
open Utilities.Certificate.ContractionForestCensusGeneral

variable {n p : ℕ} (d : DegSpec n p)

/-! ## The degree of a vertex, as a sum over unit steps -/

/-- Every unit step contributes one to the degree of each of its two ends.
This is the degree counterpart of `prin_eq_sum_steps`. -/
theorem vertex_degree_eq_sum_steps (x : d.Vertex) :
    vertex_degree d.graph x =
      ∑ s : d.Step,
        ((if d.stepLeft s.1 s.2 = x then (1 : ℤ) else 0) +
          (if d.stepRight s.1 s.2 = x then (1 : ℤ) else 0)) := by
  classical
  change (∑ u : d.graph.V, (num_edges d.graph x u : ℤ)) = _
  simp_rw [d.num_edges_eq_sum_steps]
  push_cast
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _hs
  rcases s with ⟨e, o⟩
  have hne := d.stepLeft_ne_stepRight e o
  by_cases hleft : d.stepLeft e o = x
  · subst x
    simp only [unitEdge, Prod.mk.injEq]
    simp [hne.symm]
  · by_cases hright : d.stepRight e o = x
    · subst x
      simp only [unitEdge, Prod.mk.injEq]
      simp [hne]
    · simp only [unitEdge, Prod.mk.injEq]
      simp [hleft, hright]

/-! ## Classes and the zero slots inside them -/

/-- The core vertices identified with `r` by the contraction. -/
def classOf (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => d.rep v = d.rep r

/-- The vanishing slots whose (identified) endpoints lie in the class of `r`. -/
def classZeroSlots (r : Fin n) : Finset (Fin p) :=
  Finset.univ.filter fun e : Fin p =>
    d.length e = 0 ∧ d.rep (d.core.tail e) = d.rep r

@[simp] theorem mem_classOf {r v : Fin n} :
    v ∈ d.classOf r ↔ d.rep v = d.rep r := by
  simp [classOf]

@[simp] theorem mem_classZeroSlots {r : Fin n} {e : Fin p} :
    e ∈ d.classZeroSlots r ↔
      d.length e = 0 ∧ d.rep (d.core.tail e) = d.rep r := by
  simp [classZeroSlots]

theorem classOf_rep (r : Fin n) : d.classOf (d.rep r) = d.classOf r := by
  ext v; simp [d.rep_idem]

theorem classZeroSlots_rep (r : Fin n) :
    d.classZeroSlots (d.rep r) = d.classZeroSlots r := by
  ext e; simp [d.rep_idem]

/-- Both endpoints of a vanishing slot inside a class lie in that class. -/
theorem head_mem_classOf_of_mem_classZeroSlots {r : Fin n} {e : Fin p}
    (he : e ∈ d.classZeroSlots r) : d.rep (d.core.head e) = d.rep r := by
  rw [d.mem_classZeroSlots] at he
  rw [← d.rep_zero e he.1]
  exact he.2

/-! ## The degree of a contracted class -/

/-- Only the two ends of a *surviving* slot can meet a contracted class. -/
theorem vertex_degree_coreVertex_eq_positive_ends (r : Fin n) :
    vertex_degree d.graph (d.coreVertex r) =
      ∑ e : Fin p,
        (if 0 < d.length e then
            ((if d.rep (d.core.tail e) = d.rep r then (1 : ℤ) else 0) +
              (if d.rep (d.core.head e) = d.rep r then (1 : ℤ) else 0))
          else 0) := by
  classical
  rw [d.vertex_degree_eq_sum_steps]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro e _he
  rcases Nat.eq_zero_or_pos (d.length e) with hzero | hpos
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro o _
    exact absurd o.isLt (by omega)
  rw [if_pos hpos]
  rw [Finset.sum_add_distrib]
  congr 1
  · -- the unique step whose left end is a core vertex is the first one
    have hFirst : (∑ o : Fin (d.length e),
        (if d.stepLeft e o = d.coreVertex r then (1 : ℤ) else 0)) =
        (if d.rep (d.core.tail e) = d.rep r then (1 : ℤ) else 0) := by
      rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin (d.length e))]
      · unfold DegSpec.stepLeft
        rw [dif_pos rfl]
        simp [d.coreVertex_eq_iff]
      · intro o _ hne
        have hoval : o.val ≠ 0 := fun h => hne (Fin.ext (by simp [h]))
        unfold DegSpec.stepLeft
        rw [dif_neg hoval]
        simp [DegSpec.coreVertex, DegSpec.interiorVertex]
      · intro h; exact absurd (Finset.mem_univ _) h
    exact hFirst
  · have hLast : (∑ o : Fin (d.length e),
        (if d.stepRight e o = d.coreVertex r then (1 : ℤ) else 0)) =
        (if d.rep (d.core.head e) = d.rep r then (1 : ℤ) else 0) := by
      rw [Finset.sum_eq_single (⟨d.length e - 1, by omega⟩ : Fin (d.length e))]
      · unfold DegSpec.stepRight
        rw [dif_pos (by simp; omega)]
        simp [d.coreVertex_eq_iff]
      · intro o _ hne
        have hoval : o.val + 1 ≠ d.length e := by
          intro h
          exact hne (Fin.ext (by simp; omega))
        unfold DegSpec.stepRight
        rw [dif_neg hoval]
        simp [DegSpec.coreVertex, DegSpec.interiorVertex]
      · intro h; exact absurd (Finset.mem_univ _) h
    exact hLast

/-- Regrouping the slot ends of a class by its members. -/
theorem sum_incidenceDegree_classOf (r : Fin n) :
    (∑ v ∈ d.classOf r, (d.core.incidenceDegree v : ℤ)) =
      ∑ e : Fin p,
        ((if d.rep (d.core.tail e) = d.rep r then (1 : ℤ) else 0) +
          (if d.rep (d.core.head e) = d.rep r then (1 : ℤ) else 0)) := by
  classical
  unfold ExplicitPotential.Core.incidenceDegree
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro e _he
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_ite_eq (d.classOf r) (d.core.tail e) (fun _ => (1 : ℤ))]
    simp [d.mem_classOf]
  · rw [Finset.sum_ite_eq (d.classOf r) (d.core.head e) (fun _ => (1 : ℤ))]
    simp [d.mem_classOf]

/-- **The degree of a contracted class.**  Its members' slot ends, less two
for every vanishing slot absorbed inside the class. -/
theorem vertex_degree_coreVertex (r : Fin n) :
    vertex_degree d.graph (d.coreVertex r) =
      (∑ v ∈ d.classOf r, (d.core.incidenceDegree v : ℤ)) -
        2 * ((d.classZeroSlots r).card : ℤ) := by
  classical
  rw [d.vertex_degree_coreVertex_eq_positive_ends, d.sum_incidenceDegree_classOf]
  have hcard : ((d.classZeroSlots r).card : ℤ)
      = ∑ e : Fin p, (if e ∈ d.classZeroSlots r then (1 : ℤ) else 0) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul,
      mul_one]
  rw [hcard, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro e _he
  by_cases hz : d.length e = 0
  · have hhead : d.rep (d.core.head e) = d.rep (d.core.tail e) :=
      (d.rep_zero e hz).symm
    have hmem : e ∈ d.classZeroSlots r ↔ d.rep (d.core.tail e) = d.rep r := by
      simp [d.mem_classZeroSlots, hz]
    rw [if_neg (by omega)]
    by_cases htail : d.rep (d.core.tail e) = d.rep r <;>
      simp [hhead, htail, hmem]
  · have hpos : 0 < d.length e := by omega
    have hmem : e ∉ d.classZeroSlots r := by
      simp [d.mem_classZeroSlots, hz]
    rw [if_pos hpos, if_neg hmem]
    ring

/-! ## Each class is spanned by its own zero slots

`DegSpec.forest` is one global equation and cannot see a single class.  The
localization below is what makes the canonical computation pointwise, and it
is the only place where the representative map has to be *genuine* zero-slot
reachability rather than an arbitrary idempotent map. -/

/-- A zero-slot path inside one class never leaves it, so reachability through
*all* zero slots restricts to reachability through the class's own. -/
theorem reachIn_classZeroSlots {F : Finset (Fin p)}
    (hF : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    (hRep : ∀ x y : Fin n, d.rep x = d.rep y ↔ ReachIn d.core F x y)
    {r x y : Fin n} (hx : d.rep x = d.rep r) (h : ReachIn d.core F x y) :
    ReachIn d.core (d.classZeroSlots r) x y := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hprefix hlast ih =>
      refine Relation.ReflTransGen.tail ih ?_
      obtain ⟨e, he, hbc⟩ := hlast
      have heF : e ∈ F := (mem_edgeList F e).mp he
      have hzero : d.length e = 0 := (hF e).mp heF
      have hrepb : d.rep b = d.rep r :=
        ((hRep x b).mpr hprefix).symm.trans hx
      have hmem : e ∈ d.classZeroSlots r := by
        refine (d.mem_classZeroSlots).mpr ⟨hzero, ?_⟩
        rcases hbc with ⟨htail, -⟩ | ⟨hhead, -⟩
        · rw [htail]; exact hrepb
        · rw [d.rep_zero e hzero, hhead]; exact hrepb
      exact ⟨e, (mem_edgeList _ e).mpr hmem, hbc⟩

/-- Contracting only a class's own zero slots already merges that class, so it
leaves at most `n - |class| + 1` vertex classes. -/
theorem card_image_compFold_classZeroSlots_add_card_classOf_le {F : Finset (Fin p)}
    (hF : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    (hRep : ∀ x y : Fin n, d.rep x = d.rep y ↔ ReachIn d.core F x y)
    (r : Fin n) :
    (Finset.univ.image (compFold d.core (d.classZeroSlots r))).card
        + (d.classOf r).card ≤ n + 1 := by
  classical
  set g := compFold d.core (d.classZeroSlots r) with hg
  set S : Finset (Fin n) :=
    (Finset.univ.filter fun v : Fin n => ¬ d.rep v = d.rep r) ∪ {r} with hS
  have hmerge : ∀ v : Fin n, d.rep v = d.rep r → g v = g r := by
    intro v hv
    refine (compFold_iff d.core (d.classZeroSlots r) v r).mpr ?_
    exact d.reachIn_classZeroSlots hF hRep hv ((hRep v r).mp hv)
  have himage : Finset.univ.image g = S.image g := by
    refine Finset.Subset.antisymm ?_ (Finset.image_subset_image (by simp [hS]))
    intro z hz
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hz
    by_cases hv : d.rep v = d.rep r
    · rw [hmerge v hv]
      exact Finset.mem_image_of_mem g (by simp [hS])
    · exact Finset.mem_image_of_mem g (by simp [hS, hv])
  have hScard : S.card ≤
      (Finset.univ.filter fun v : Fin n => ¬ d.rep v = d.rep r).card + 1 := by
    refine le_trans (Finset.card_union_le _ _) ?_
    simp
  have hsplit :
      (Finset.univ.filter fun v : Fin n => d.rep v = d.rep r).card +
          (Finset.univ.filter fun v : Fin n => ¬ d.rep v = d.rep r).card
        = (Finset.univ : Finset (Fin n)).card :=
    Finset.card_filter_add_card_filter_not _
  have hn : (Finset.univ : Finset (Fin n)).card = n := by simp
  have hle : (Finset.univ.image g).card ≤ S.card := by
    rw [himage]; exact Finset.card_image_le
  have hclass : (d.classOf r).card
      = (Finset.univ.filter fun v : Fin n => d.rep v = d.rep r).card := rfl
  omega

/-- **One class, one spanning tree.**  The vanishing slots inside a class are
exactly one fewer than the class itself. -/
theorem card_classZeroSlots_add_one {F : Finset (Fin p)}
    (hF : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    (hRep : ∀ x y : Fin n, d.rep x = d.rep y ↔ ReachIn d.core F x y)
    (r : Fin n) :
    (d.classZeroSlots r).card + 1 = (d.classOf r).card := by
  classical
  set R : Finset (Fin n) := Finset.univ.image d.rep with hR
  set Z : Finset (Fin p) := Finset.univ.filter fun e : Fin p => d.length e = 0
    with hZ
  have hrepR : ∀ b ∈ R, d.rep b = b := by
    intro b hb
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hb
    exact d.rep_idem v
  -- the classes tile the core vertices
  have hclassSum : ∑ b ∈ R, (d.classOf b).card = n := by
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := d.rep) (s := (Finset.univ : Finset (Fin n))) (t := R)
      (fun v _ => Finset.mem_image_of_mem d.rep (Finset.mem_univ v))
    have hcongr : ∀ b ∈ R,
        ((Finset.univ : Finset (Fin n)).filter fun v => d.rep v = b).card
          = (d.classOf b).card := by
      intro b hb
      unfold classOf
      rw [hrepR b hb]
    rw [Finset.sum_congr rfl hcongr] at hfib
    simpa using hfib.symm
  -- the class zero slots tile the zero slots
  have hzeroSum : ∑ b ∈ R, (d.classZeroSlots b).card = Z.card := by
    have hmem : ∀ e ∈ Z, d.rep (d.core.tail e) ∈ R := by
      intro e _
      exact Finset.mem_image_of_mem d.rep (Finset.mem_univ _)
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := fun e : Fin p => d.rep (d.core.tail e)) (s := Z) (t := R) hmem
    have hcongr : ∀ b ∈ R,
        (Z.filter fun e => d.rep (d.core.tail e) = b).card
          = (d.classZeroSlots b).card := by
      intro b hb
      unfold classZeroSlots
      rw [hrepR b hb, hZ]
      congr 1
      ext e
      simp [Finset.mem_filter]
    rw [Finset.sum_congr rfl hcongr] at hfib
    exact hfib.symm
  -- the forest equation
  have hforest : R.card + Z.card = n := d.forest
  have hpoint : ∀ b ∈ R, (d.classOf b).card ≤ (d.classZeroSlots b).card + 1 := by
    intro b _
    have := d.card_image_compFold_classZeroSlots_add_card_classOf_le hF hRep b
    have hge := card_le_card_image_compFold_add_card d.core (d.classZeroSlots b)
    omega
  have hsum : ∑ b ∈ R, (d.classOf b).card
      = ∑ b ∈ R, ((d.classZeroSlots b).card + 1) := by
    rw [Finset.sum_add_distrib, hzeroSum, hclassSum]
    simp
    omega
  have heq := (Finset.sum_eq_sum_iff_of_le hpoint).mp hsum
  have hmemR : d.rep r ∈ R := Finset.mem_image_of_mem d.rep (Finset.mem_univ r)
  have := heq (d.rep r) hmemR
  rw [d.classOf_rep, d.classZeroSlots_rep] at this
  omega

/-! ## The canonical divisor of a face -/

/-- A subdivision-interior vertex is two-valent on every face. -/
theorem vertex_degree_interiorVertex (e : Fin p) (o : Fin (d.length e - 1)) :
    vertex_degree d.graph (d.interiorVertex e o) = 2 := by
  classical
  have hlt : o.val + 1 < d.length e := by have := o.isLt; omega
  rw [d.vertex_degree_eq_sum_steps, Fintype.sum_sigma]
  rw [Finset.sum_eq_single e]
  · rw [Finset.sum_add_distrib]
    have hLeft : (∑ k : Fin (d.length e),
        (if d.stepLeft e k = d.interiorVertex e o then (1 : ℤ) else 0)) = 1 := by
      rw [Finset.sum_eq_single (⟨o.val + 1, hlt⟩ : Fin (d.length e))]
      · unfold DegSpec.stepLeft
        rw [dif_neg (by simp)]
        simp [DegSpec.interiorVertex]
      · intro k _ hne
        unfold DegSpec.stepLeft
        by_cases hk : k.val = 0
        · rw [dif_pos hk]; simp [DegSpec.coreVertex, DegSpec.interiorVertex]
        · rw [dif_neg hk]
          refine if_neg ?_
          simp only [DegSpec.interiorVertex, Sum.inr.injEq]
          intro hcontra
          apply hne
          have hval : k.val - 1 = o.val :=
            congrArg (fun t : d.Interior => t.2.val) hcontra
          apply Fin.ext
          show k.val = o.val + 1
          omega
      · intro h; exact absurd (Finset.mem_univ _) h
    have hRight : (∑ k : Fin (d.length e),
        (if d.stepRight e k = d.interiorVertex e o then (1 : ℤ) else 0)) = 1 := by
      rw [Finset.sum_eq_single (⟨o.val, by omega⟩ : Fin (d.length e))]
      · unfold DegSpec.stepRight
        rw [dif_neg (by simp; omega)]
        simp [DegSpec.interiorVertex]
      · intro k _ hne
        unfold DegSpec.stepRight
        by_cases hk : k.val + 1 = d.length e
        · rw [dif_pos hk]; simp [DegSpec.coreVertex, DegSpec.interiorVertex]
        · rw [dif_neg hk]
          refine if_neg ?_
          simp only [DegSpec.interiorVertex, Sum.inr.injEq]
          intro hcontra
          exact hne (Fin.ext (by
            have := congrArg (fun t : d.Interior => t.2.val) hcontra
            simpa using this))
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hLeft, hRight]; norm_num
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro k _
    have hleft : d.stepLeft f k ≠ d.interiorVertex e o := by
      unfold DegSpec.stepLeft
      split_ifs
      · simp [DegSpec.coreVertex, DegSpec.interiorVertex]
      · simp only [DegSpec.interiorVertex, ne_eq, Sum.inr.injEq]
        intro hcontra
        exact hfe (congrArg (fun t : d.Interior => t.1) hcontra)
    have hright : d.stepRight f k ≠ d.interiorVertex e o := by
      unfold DegSpec.stepRight
      split_ifs
      · simp [DegSpec.coreVertex, DegSpec.interiorVertex]
      · simp only [DegSpec.interiorVertex, ne_eq, Sum.inr.injEq]
        intro hcontra
        exact hfe (congrArg (fun t : d.Interior => t.1) hcontra)
    simp [hleft, hright]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The canonical divisor of a face of a cubic core.**  It is the core-class
divisor of the all-ones weight: a class of `k` core vertices carries `k`. -/
theorem canonical_divisor_eq_coreClassDivisor_one (hCubic : d.core.Cubic)
    {F : Finset (Fin p)} (hF : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    (hRep : ∀ x y : Fin n, d.rep x = d.rep y ↔ ReachIn d.core F x y) :
    canonical_divisor d.graph = d.coreClassDivisor (fun _ => 1) := by
  classical
  funext x
  rcases x with cls | interior
  · obtain ⟨r, hr⟩ := cls
    have hVertex : (Sum.inl ⟨r, hr⟩ : d.Vertex) = d.coreVertex r := by
      unfold DegSpec.coreVertex
      congr 1
      exact Subtype.ext hr.symm
    rw [hVertex]
    show vertex_degree d.graph (d.coreVertex r) - 2 = _
    rw [d.vertex_degree_coreVertex, d.coreClassDivisor_coreVertex]
    have hthree : (∑ v ∈ d.classOf r, (d.core.incidenceDegree v : ℤ))
        = 3 * ((d.classOf r).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun v _ => by rw [hCubic v])]
      simp [Finset.sum_const, mul_comm]
    have hspan := d.card_classZeroSlots_add_one hF hRep r
    have hones : (∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep r),
        (1 : ℤ)) = ((d.classOf r).card : ℤ) := by
      simp [classOf]
    rw [hthree, hones]
    have hspanZ : ((d.classZeroSlots r).card : ℤ) + 1 = ((d.classOf r).card : ℤ) :=
      by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ) hspan
    linarith
  · obtain ⟨e, o⟩ := interior
    change vertex_degree d.graph (d.interiorVertex e o) - 2 = _
    rw [d.vertex_degree_interiorVertex e o]
    simp [DegSpec.coreClassDivisor]

/-! ## Serre duality between complementary core weights -/

/-- Complementary core weights subtract. -/
theorem coreClassDivisor_one_sub (w : Fin n → ℤ) :
    d.coreClassDivisor (fun _ => 1) - d.coreClassDivisor w
      = d.coreClassDivisor (fun v => 1 - w v) := by
  funext x
  rcases x with cls | interior
  · show (∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = cls.val), (1 : ℤ)) -
      (∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = cls.val), w v) = _
    rw [← Finset.sum_sub_distrib]
    rfl
  · show (0 : ℤ) - 0 = 0
    ring

/-- **Riemann--Roch between complementary core weights on a face.** -/
theorem rank_coreClassDivisor_sub_rank_complement (hCubic : d.core.Cubic)
    {F : Finset (Fin p)} (hF : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    (hRep : ∀ x y : Fin n, d.rep x = d.rep y ↔ ReachIn d.core F x y)
    (hConnected : graph_connected d.graph) (w : Fin n → ℤ) :
    rank d.graph (d.coreClassDivisor w)
        - rank d.graph (d.coreClassDivisor fun v => 1 - w v)
      = (∑ v : Fin n, w v) - ((p : ℤ) - (n : ℤ) + 1) + 1 := by
  have hRR := riemann_roch_for_graphs hConnected (d.coreClassDivisor w)
  rw [d.canonical_divisor_eq_coreClassDivisor_one hCubic hF hRep,
    d.coreClassDivisor_one_sub w, d.deg_coreClassDivisor, d.genus_graph] at hRR
  linarith

/-- **Complementary core weights of degree `g - 1` have equal rank on every
face.**  On a cubic core `genus = p - n + 1`, so the hypothesis says exactly
that the weight has the Serre-self-dual degree. -/
theorem rank_coreClassDivisor_eq_complement (hCubic : d.core.Cubic)
    {F : Finset (Fin p)} (hF : ∀ e : Fin p, e ∈ F ↔ d.length e = 0)
    (hRep : ∀ x y : Fin n, d.rep x = d.rep y ↔ ReachIn d.core F x y)
    (hConnected : graph_connected d.graph) (w : Fin n → ℤ)
    (hDeg : (∑ v : Fin n, w v) = (p : ℤ) - (n : ℤ)) :
    rank d.graph (d.coreClassDivisor w)
      = rank d.graph (d.coreClassDivisor fun v => 1 - w v) := by
  have h := d.rank_coreClassDivisor_sub_rank_complement hCubic hF hRep
    hConnected w
  rw [hDeg] at h
  linarith

end Utilities.Certificate.DegenerateSpec.DegSpec
