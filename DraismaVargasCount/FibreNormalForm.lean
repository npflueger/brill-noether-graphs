import DraismaVargasCount.TargetNormalForm
import DraismaVargasCount.TransportMultiplicity

/-!
# Finiteness of the labelled fibre, from the normal form and the transport

**Source.**  Vargas, Part II (arXiv:2609.09109), the remark following the
symmetry formula (S) (`eq-S`): the set `F(d,g)` of combinatorial types is
finite and all automorphism groups are finite, so (S) implies that every fibre
`Π⁻¹(H)` is finite.  This file proves the corresponding statement for the
labelled fibre from two pieces: (1) the normal form for the target,
`Count.TargetNormalForm`; (2) the transport of a gluing datum with its induced
stable dictionary, `Count.Transport` and
`DraismaVargasCount.TransportMultiplicity`.

## What is proved

* `instFiniteStablePath`, `instFiniteBranchVertex`,
  `instFiniteStableLengthMatrixLabelling`, `instFiniteCoreIdentification` --
  the four finiteness facts the index needs.  A stable labelling is two
  bijections and a core identification is two bijections and a proposition, so
  both are finite over a fixed datum.
* `TargetIndex`, `indexTarget`, `Raw` -- **the finite index.**  A normal-form
  target on `p` occurrences, a gluing datum on it (finite by
  `GluingDatum.instFinite` of `DraismaVargasCount.Fibre`), its stable
  labelling and its core identification.  The coordinate vector is
  deliberately absent.
* `MatchesRaw`, `matchesRaw_unique` -- the index determines the member.  The
  coordinate vector is the one remaining degree of freedom and `coords_unique`
  (through `coords_injective`) removes it: the length matrix is nonsingular, so
  the realization equation has one solution.
* `exists_matching_normalForm` -- every member is carried, by
  `FibreMember.transport` along `NormalForm.datumIso`, to a member over a
  normal-form target in the same class of the labelled fibre (`cls_transport`).
* `instFiniteFibre` -- **`Finite (Count.Fibre core y degree)`, unconditional**:
  the hypotheses are exactly the ones a `FibreMember` already carries
  (`FullDimensionalSourcePresentation.targetConnected` and `.targetGenus` give
  the target's connectivity and genus zero, and its labelling gives the
  occurrence count `p`).  No hypothesis about the core, the request `y` or the
  degree is used, and no descent statement is assumed.
* `catRaw`, `catRaw_spec` -- non-vacuity: the caterpillar member
  `FibreCaterpillar.caterpillarMember` names an index, realized by a member of
  its own class.
* `instFintypeFibre` -- the same fact as a `Fintype`, built from `Finite` by
  choice, hence **noncomputable**: it enumerates nothing.  `Finite` is the
  honest form and is what the paper states; the `Fintype` exists only so that
  `Count.oddCount_eq_card_filter`, which is stated with a `Fintype`
  instance argument, can be applied.

## Scope

* No bound on the number of classes, and no enumeration: `family` chooses a
  representative for each index by `Classical.choice` and the fallback branch is
  never inspected.
* Nothing about oddness or multiplicity.  `Count.oddCount` is well defined
  without this file; `oddCount_pos_of_hasOddMult` needs exactly the `Finite`
  instance proved here, and `Count.isOddClass_cls_iff` needs `AbsMultDescends`
  (the multiplicity descends to the fibre), which is `absMultDescends` in
  `DraismaVargasCount.TransportMultiplicity`, not this file.

## Implementation note

`MatchesRaw`'s uniqueness proof destructures `Count.FibreMember` positionally;
a new field on that structure needs one line changed here.

## Consumers

`Count.oddCount_pos_of_hasOddMult` and `Count.oddCount_eq_card_filter`, and
every later statement that counts classes of the labelled fibre.
-/


namespace DraismaVargas.Count.FibreNormalForm

open DraismaVargas.Infrastructure
open DraismaVargas.Count.Transport
open DraismaVargas.Count.TargetNormalForm
open DraismaVargas.LocalCases
open DraismaVargas.LocalCases.W4StableSource
open DraismaVargas.LocalCases.FullDimensionalSource
open DraismaVargas.LocalCases.StableGraphIncidence (BranchVertex)
open Utilities.Certificate.ExplicitPotential (Core)

variable {n p : ℕ}

/-! ## 1. Four finiteness facts -/

instance instFiniteStablePath {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) : Finite (StablePath data) := by
  have : Finite (NonDanglingEdge data) := by
    unfold NonDanglingEdge
    infer_instance
  unfold StablePath
  infer_instance

instance instFiniteBranchVertex {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) : Finite (BranchVertex data) := by
  unfold BranchVertex
  infer_instance

instance instFiniteStableLengthMatrixLabelling {target : CFGraph} {degree : ℕ}
    (data : GluingDatum target degree) (coordinate : Type) [Finite coordinate] :
    Finite (StableLengthMatrixLabelling data coordinate) := by
  refine Finite.of_injective
    (fun labelling : StableLengthMatrixLabelling data coordinate =>
      (labelling.targetEdge, labelling.row)) ?_
  rintro ⟨ta, ra⟩ ⟨tb, rb⟩ hab
  have h1 : ta = tb := congrArg Prod.fst hab
  have h2 : ra = rb := congrArg Prod.snd hab
  rw [h1, h2]

instance instFiniteCoreIdentification (core : Core n p) {target : CFGraph.{0}} {degree : ℕ}
    (data : GluingDatum target degree) : Finite (CoreIdentification core data) := by
  refine Finite.of_injective
    (fun ident : CoreIdentification core data => (ident.vertex, ident.row)) ?_
  rintro ⟨va, ra, ia⟩ ⟨vb, rb, ib⟩ hab
  have h1 : va = vb := congrArg Prod.fst hab
  have h2 : ra = rb := congrArg Prod.snd hab
  subst h1
  subst h2
  rfl

/-! ## 2. The finite index of normal-form data -/

/-- The finitely many normal-form targets on `p` edge occurrences: a parent map
pointing to strictly smaller numbers, and an orientation bit per tree edge. -/
def TargetIndex (p : ℕ) : Type :=
  {par : Fin p → Fin (p + 1) // ∀ i : Fin p, (par i).val ≤ i.val} × (Fin p → Bool)

instance : Finite (TargetIndex p) := by
  unfold TargetIndex
  infer_instance

/-- The normal-form target named by an index. -/
def indexTarget (t : TargetIndex p) : CFGraph.{0} :=
  orientedTree p t.1.1 t.1.2 t.2

/-- **The finite index of the family.**  A normal-form target, a gluing datum on
it, the stable labelling and the core identification: everything a member of the
fibre carries except its coordinate vector, which is determined. -/
def Raw (core : Core n p) (degree : ℕ) : Type :=
  Σ t : TargetIndex p, Σ data : GluingDatum (indexTarget t) degree,
    StableLengthMatrixLabelling data (Fin p) × CoreIdentification core data

instance (core : Core n p) (degree : ℕ) : Finite (Raw core degree) := by
  unfold Raw
  infer_instance

/-- A member of the fibre realizing an index. -/
def MatchesRaw {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
    (r : Raw core degree) (member : FibreMember core y degree) : Prop :=
  member.target = indexTarget r.1 ∧ HEq member.data r.2.1 ∧
    HEq member.fullDim.labelling r.2.2.1 ∧ HEq member.ident r.2.2.2

/-- **The index determines the member.**  The coordinate vector is the one place
where two members over the same datum, labelling and identification could still
differ, and `coords_unique` closes it. -/
theorem matchesRaw_unique {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
    {r : Raw core degree} {first second : FibreMember core y degree}
    (hFirst : MatchesRaw r first) (hSecond : MatchesRaw r second) : first = second := by
  obtain ⟨targetA, dataA, fdA, identA, coordsA, realizesA⟩ := first
  obtain ⟨targetB, dataB, fdB, identB, coordsB, realizesB⟩ := second
  obtain ⟨hTA, hdA, hlA, hiA⟩ := hFirst
  obtain ⟨hTB, hdB, hlB, hiB⟩ := hSecond
  have hTA' : targetA = indexTarget r.1 := hTA
  have hTB' : targetB = indexTarget r.1 := hTB
  subst hTA'
  subst hTB'
  have hdA' : HEq dataA r.2.1 := hdA
  have hdB' : HEq dataB r.2.1 := hdB
  have hdataA : dataA = r.2.1 := eq_of_heq hdA'
  subst hdataA
  have hdataB : dataB = r.2.1 := eq_of_heq hdB'
  subst hdataB
  obtain ⟨vA, cA, gA, sA, labA, dA, tA, peA⟩ := fdA
  obtain ⟨vB, cB, gB, sB, labB, dB, tB, peB⟩ := fdB
  have hlA' : HEq labA r.2.2.1 := hlA
  have hlB' : HEq labB r.2.2.1 := hlB
  have hlabA : labA = r.2.2.1 := eq_of_heq hlA'
  subst hlabA
  have hlabB : labB = r.2.2.1 := eq_of_heq hlB'
  subst hlabB
  have hiA' : HEq identA r.2.2.2 := hiA
  have hiB' : HEq identB r.2.2.2 := hiB
  have hidentA : identA = r.2.2.2 := eq_of_heq hiA'
  subst hidentA
  have hidentB : identB = r.2.2.2 := eq_of_heq hiB'
  subst hidentB
  have hcoords : coordsA = coordsB :=
    FibreMember.coords_injective
      ⟨indexTarget r.1, r.2.1, ⟨vA, cA, gA, sA, r.2.2.1, dA, tA, peA⟩, r.2.2.2,
        coordsA, realizesA⟩
      (realizesA.trans realizesB.symm)
  subst hcoords
  rfl

/-! ## 3. The finite family, and the finiteness of the fibre -/

/-- A chosen member realizing an index, or a fixed fallback when the index is
realized by no member. -/
noncomputable def family {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
    (base : FibreMember core y degree) (r : Raw core degree) :
    FibreMember core y degree :=
  @dite _ (∃ member : FibreMember core y degree, MatchesRaw r member) (Classical.dec _)
    (fun h => h.choose) (fun _ => base)

theorem matchesRaw_family {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
    (base : FibreMember core y degree) {r : Raw core degree}
    (h : ∃ member : FibreMember core y degree, MatchesRaw r member) :
    MatchesRaw r (family base r) := by
  unfold family
  by_cases hcase : ∃ member : FibreMember core y degree, MatchesRaw r member
  · rw [dif_pos hcase]
    exact hcase.choose_spec
  · exact absurd h hcase

/-- **Every member of the fibre lies over a normal-form target.**  The target of
a member is connected and of genus zero (the two standing Part-I hypotheses
carried by `FullDimensionalSourcePresentation`) and has exactly `p` occurrences
(its labelling numbers them by `Fin p`), so `exists_normalForm` applies; the
member is then carried there by `FibreMember.transport` along the normal form's
own `DatumIso`, and `cls_transport` keeps the class. -/
theorem exists_matching_normalForm {core : Core n p} {y : Fin p → ℚ} {degree : ℕ}
    (member : FibreMember core y degree) :
    ∃ (r : Raw core degree) (normal : FibreMember core y degree),
      MatchesRaw r normal ∧ normal.cls = member.cls := by
  have hcard : Multiset.card member.target.edges = p := by
    have hc := Fintype.card_congr member.fullDim.labelling.targetEdge
    rw [Fintype.card_fin, Multiset.card_coe] at hc
    exact hc.symm
  obtain ⟨nf⟩ := TargetNormalForm.exists_normalForm member.target
    member.fullDim.targetConnected member.fullDim.targetGenus p hcard
  exact ⟨⟨(⟨nf.parent, nf.parent_le⟩, nf.flip),
      (member.transport (nf.datumIso member.data)).data,
      (member.transport (nf.datumIso member.data)).fullDim.labelling,
      (member.transport (nf.datumIso member.data)).ident⟩,
    member.transport (nf.datumIso member.data), ⟨rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩,
    cls_transport member (nf.datumIso member.data)⟩

/-- **The labelled fibre is finite.**
Unconditional: the only hypotheses are the ones a `FibreMember` already
carries. -/
instance instFiniteFibre (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Finite (Fibre core y degree) := by
  by_cases hNonempty : Nonempty (FibreMember core y degree)
  · obtain ⟨base⟩ := hNonempty
    refine finite_fibre_of_meets (index := Raw core degree) (family base) ?_
    intro member
    obtain ⟨r, normal, hmatch, hcls⟩ := exists_matching_normalForm member
    refine ⟨r, ?_⟩
    have hfam : MatchesRaw r (family base r) := matchesRaw_family base ⟨normal, hmatch⟩
    have hEq : family base r = normal := matchesRaw_unique hfam hmatch
    rw [hEq]
    exact FibreMember.cls_eq_cls_iff.mp hcls
  · have hempty : IsEmpty (Fibre core y degree) := by
      constructor
      intro cls
      obtain ⟨member, -⟩ := FibreMember.cls_surjective cls
      exact hNonempty ⟨member⟩
    exact Finite.of_subsingleton

/-- The same statement as a (noncomputable, choice-built) `Fintype`, which is the
shape `oddCount_eq_card_filter` asks for. -/
noncomputable instance instFintypeFibre (core : Core n p) (y : Fin p → ℚ) (degree : ℕ) :
    Fintype (Fibre core y degree) :=
  Fintype.ofFinite _

/-! ### Non-vacuity of the index -/

/-- **Non-vacuity of `Raw`.**  The caterpillar member of
`Count.FibreCaterpillar` -- an inhabitant of the labelled fibre at every
even genus and every request -- names an index. -/
noncomputable def catRaw (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    Raw (FibreCaterpillar.catCore m) (m + 2) :=
  (exists_matching_normalForm (FibreCaterpillar.caterpillarMember m request)).choose

/-- The index it names is realized, by a member of the caterpillar's own class. -/
theorem catRaw_spec (m : ℕ) (request : Fin (6 * m + 3) → ℚ) :
    ∃ normal : FibreMember (FibreCaterpillar.catCore m) request (m + 2),
      MatchesRaw (catRaw m request) normal ∧
        normal.cls = (FibreCaterpillar.caterpillarMember m request).cls :=
  (exists_matching_normalForm (FibreCaterpillar.caterpillarMember m request)).choose_spec

end DraismaVargas.Count.FibreNormalForm
