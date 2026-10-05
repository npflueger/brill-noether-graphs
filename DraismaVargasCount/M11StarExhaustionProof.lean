module

public import DraismaVargasCount.M11StarCensusProof

@[expose] public section

/-!
# M-11 star exhaustion: the `w2M11` clause with no hypothesis

Sources: Draisma–Vargas Part I, Case `{w2-r2-nd3-M-11}` (Figure 32, Equation (6));
Vargas, Part II, the star of a codimension-one wall and the balancing condition
`prop-signed-mult`.  The generic census machinery is `DraismaVargasCount.StarCensusEngine`;
the reduction completed here is `M11StarCensusProof.exhausts_of_transports`.

## The result, in one paragraph

`DraismaVargasCount.M11StarCensusProof` reduces
`FamilyStarParity (2+2) (4*2+2) (6*2+3) .w2M11` to `M11StarExhaustion`,
and that to one `PositionTransport` per star member (`exhausts_of_transports`).  Here
every star member receives one.  A member `m` with limit isomorphism `ψ : m.limit ≅ w.limit`
gets the wall's W2 input and M-11 profile pulled back along `ψ` (§5); Part I's incoming
partition censuses, read at `m`'s own contraction, then say its normalized local
resolution has Figure 32's **split shape** or **joined shape** as relations (§6).  A joined
member goes to position `2`.  For a split member the two occurrence permutations of `ψ`
at the wall either agree on the distinguished block or differ by its transposition
(`agree_or_swap`, §8): agreeing members go to position `0` along `ψ`, the others to
position `1` along `ψ ≫ branchIso`, where the branch swap exchanges the two sheets on the
double direction only (§10).  Each transport is built from relational data by a
representative gauge (§3), and a position receiving a member is nonsingular because the
member hands it a full-dimensional presentation (§7).  Hence `m11StarExhaustion` at every
degree, core size and request, `m11StarCensus`, and `familyStarParity_w2M11` with no
hypothesis.

## What is proved

* §1 `SplitLeft`, `SplitRight`, `Discrete`, `Joined`, `SplitShape`, `JoinedShape`,
  `splitBlock_rel_iff` -- local resolutions as relations around a distinguished sheet.
* §2 `splitShape_paste`, `joinedShape_paste`, `firstSplit_shape`, `secondSplit_shape`,
  `joined_shape` -- the three pasted candidates of Equation (6) have those shapes.
* §3 `exists_gauge` (representative gauge) and **`nonempty_transportFree_of_rel`**: a
  `ResolutionExpansionFree.TransportFree` from three permutations that carry the member's
  three partitions onto the position's *as relations*, agree with the wall permutation
  modulo the merged partition, are compatible on the regrown occurrence and with every
  incident occurrence permutation.  **Family-generic**: any datum isomorphism, any
  resolutions, any placements; nothing divalent or M-11 enters.
* §4 `nonempty_transportFree_split`, `nonempty_transportFree_joined` -- the two shapes, with
  the endpoint compatibility *derived*: from `GeometricDatumIso.compatible` off the
  distinguished block and from coherence (one permutation `E` for every incident
  occurrence) on it.  Generic in the datum: only the shapes are M-11's.
* §5 `input_pullback`, `nonempty_profile_pullback` (with `blockPre`, `localRamification_blockPre`,
  `nonDanglingValency_blockPre`, `blockCard_blockPre`, `incidentEquivOf`): the W2 input and
  the M-11 profile pull back along an arbitrary `GeometricDatumIso`, to the pulled-back star
  (`M11WallExhaustion.pullbackTwoStar`, i.e. the member's `inheritedStar`).
* §6 `incomingResolution_splitShape`, `incomingResolution_joinedShape`: Part I's incoming
  partition matching (`M11IncomingSplitMatching`, `M11IncomingJoinedMatching.original_sameBlocks`)
  in shape form, for the split and joined placements (the placements with the other
  valency pattern are ruled out).
* §7 `nonsingular_of_fullDim`.  §8 `agree_or_swap`, `eq_edge_of_incident`, `block_eq_or`.
* §9 `member_splitShape`, `member_joinedShape`: at an arbitrary star member.
* §10 `transport_zero` (coherent split), `transport_one` (incoherent split, through the
  branch swap), `transport_two` (joined): the three `PositionTransport`s.
* §11 `fdOfTransport`, `exists_receipt`, `exhausts`.  §12 **`m11StarExhaustion`**,
  **`m11StarCensus`**, **`familyStarParity_w2M11`**.

## Scope

* Nothing is assumed: the three headlines have no hypothesis beyond their binders.
  `exhausts` does not even use the `w2M11` classification tag: it holds at every regrowth
  carrying a W2 input and an M-11 profile with a two-sheet block.
* The genus-six clause is about the family at `(4, 10, 15)`.  Nothing here constructs a
  genus-six `w2M11` wall.
* No other family is treated here.  §3 is reusable verbatim; §4's shapes are the divalent
  M-11 ones, and a trivalent family needs its own shapes and its own coherence statement.
* The transports produced are decoupled `ResolutionExpansionFree.TransportFree`s, which is
  what `exhausts_of_transports` consumes; the strict, wall-permutation transport
  `ResolutionExpansion.Transport` of `M11WallExhaustion` is not produced.

## Remarks

* The profile transport along a general limit isomorphism (§5) is a field-by-field
  transcription of `W2SourceTransport` with a target dictionary; the only new invariant
  is `localRamification_blockPre`.
* Whether a split member goes to position `0` or `1` is decided by the two occurrence
  permutations of `ψ` restricted to the member's distinguished block (`agree_or_swap`,
  pure combinatorics), and it only matters for split members.  The proof does not
  identify the member with a position of its own family (`exists_matching`) and carry
  that identification to the wall: it uses only Part I's *partition censuses*, in
  relational form, and builds the transport directly.  Joined members go to position `2`
  whatever the coherence: the joined shape has no block finer than the merged partition,
  so endpoint compatibility is automatic.
* By `m11StarCensus`, the star of an M-11 wall has at most three classes: no member
  outside the three positions exists.

## Endpoint compatibility

`TransportFree.endpoint_compatible` is **not** derivable from the isomorphism alone, and
§4 says exactly what else is needed: the member's endpoint partition as a *relation*
(Part I's census at the member) and, on each block where that partition is strictly finer
than the merged one, coherence of the incident occurrence permutations there.  Off such
blocks `GeometricDatumIso.compatible` already gives it.  At M-11 the only finer block is
the distinguished one at the trivalent endpoint of a split; incoherence there is exactly
what the branch swap repairs.

## Consumers

`StarSupplyAssembly` takes the `w2M11` clause `familyStarParity_w2M11`, one of the ten
wall types of the trivalent wall step of `DraismaVargasCount.Assembly`.  The
family-generic builder of §3 (`nonempty_transportFree_of_rel`, with `wall_rel_iff_of_agree`
and `sourceEndpoint_of_rel`) is reused by the star exhaustion proofs of other wall types
and by `ValencyTwoResolutionMatch`, `ValencyThreeResolutionMatch` and
`ValencyFourRigidity`; the pull-back of §5 and `nonsingular_of_fullDim` are reused as well.
-/

namespace DraismaVargas.Count.M11StarExhaustionProof

open DraismaVargas.Infrastructure DraismaVargas.LocalCases
open GluingContraction GraphContraction TargetExpansion
open W4StableSource FullDimensionalSource StableGraphIncidence
open WallStar (Regrowth Nondegenerate)
open Utilities.Certificate.ExplicitPotential (Core)
open W4WallExhaustion (mergeVertex)
open M11SourceCandidates
open ResolutionM11 (LocalResolution)

/-! ## 1.  Shapes of local resolutions, as relations -/

section Shapes

variable {d : ℕ}

/-- The leaf endpoint of Figure 32's split: joined on the distinguished block, discrete
on every other wall block. -/
def SplitLeft (W : SheetPartition d) (b : Fin d) (L : SheetPartition d) : Prop :=
  ∀ x y, L.Rel x y ↔ W.Rel x y ∧ (W.Rel b x ∨ x = y)

/-- The trivalent endpoint of Figure 32's split: discrete on the distinguished block,
joined on every other wall block. -/
def SplitRight (W : SheetPartition d) (b : Fin d) (R : SheetPartition d) : Prop :=
  ∀ x y, R.Rel x y ↔ W.Rel x y ∧ (¬ W.Rel b x ∨ x = y)

/-- A discrete partition. -/
def Discrete (N : SheetPartition d) : Prop := ∀ x y, N.Rel x y ↔ x = y

/-- A partition with the wall's blocks. -/
def Joined (W X : SheetPartition d) : Prop := ∀ x y, X.Rel x y ↔ W.Rel x y

/-- The split shape of a whole local resolution. -/
structure SplitShape (W : SheetPartition d) (b : Fin d) (r : LocalResolution d) : Prop where
  left : SplitLeft W b r.left
  right : SplitRight W b r.right
  newEdge : Discrete r.newEdge

/-- The joined shape of a whole local resolution. -/
structure JoinedShape (W : SheetPartition d) (r : LocalResolution d) : Prop where
  left : Joined W r.left
  right : Joined W r.right
  newEdge : Joined W r.newEdge

theorem SplitShape.congr_wall {W W' : SheetPartition d} {b : Fin d} {r : LocalResolution d}
    (h : SplitShape W b r) (hW : W = W') : SplitShape W' b r := hW ▸ h

theorem splitBlock_rel_iff (W : SheetPartition d) (a x y : Fin d) :
    (W.splitBlock a).Rel x y ↔ W.Rel x y ∧ (¬ W.Rel a x ∨ x = y) := by
  by_cases hx : W.Rel a x
  · rw [W.splitBlock_rel_of_rel_anchor_iff a x hx y]
    constructor
    · rintro rfl
      exact ⟨rfl, Or.inr rfl⟩
    · rintro ⟨-, h | h⟩
      · exact (h hx).elim
      · exact h
  · have hNot : ∀ z, W.Rel x z → ¬ W.Rel a z := fun z hz hz' ↦ hx (hz'.trans hz.symm)
    constructor
    · intro h
      have hW : W.Rel x y := (W.splitBlock_refines a).rel h
      exact ⟨hW, Or.inl hx⟩
    · rintro ⟨hW, -⟩
      change (W.splitBlock a).repr x = (W.splitBlock a).repr y
      rw [W.splitBlock_repr_of_not_rel a x hx, W.splitBlock_repr_of_not_rel a y (hNot y hW)]
      exact hW

end Shapes

/-! ## 2.  The candidates' shapes -/

section CandidateShapes

variable {d : ℕ}

/-- The pasted split resolution of Figure 32 (selected split, background reverse split). -/
theorem splitShape_paste (W : SheetPartition d) (sel : Fin d)
    (hC : ∀ anchor, (LocalResolution.onBlock W sel (ResolutionM11.splitResolutionAt W sel)
      (backgroundResolution W) anchor).ContractsTo W) :
    SplitShape W sel (LocalResolution.paste W (LocalResolution.onBlock W sel
      (ResolutionM11.splitResolutionAt W sel) (backgroundResolution W)) hC) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    change (LocalResolution.pasteLeft W _ hC).Rel x y ↔ _
    unfold LocalResolution.pasteLeft
    rw [SheetPartition.paste_rel_iff]
    by_cases hx : W.Rel sel x
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ (hx.trans (W.rel_repr_right x))]
      exact ⟨fun h ↦ ⟨h, Or.inl hx⟩, fun h ↦ h.1⟩
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _
        (fun h ↦ hx (h.trans (W.rel_repr_left x)))]
      change (W.splitBlock (W.repr x)).Rel x y ↔ _
      rw [splitBlock_rel_iff]
      constructor
      · rintro ⟨hW, h | h⟩
        · exact (h (W.rel_repr_left x)).elim
        · exact ⟨hW, Or.inr h⟩
      · rintro ⟨hW, h | h⟩
        · exact (hx h).elim
        · exact ⟨hW, Or.inr h⟩
  · intro x y
    change (LocalResolution.pasteRight W _ hC).Rel x y ↔ _
    unfold LocalResolution.pasteRight
    rw [SheetPartition.paste_rel_iff]
    by_cases hx : W.Rel sel x
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ (hx.trans (W.rel_repr_right x))]
      change (W.splitBlock sel).Rel x y ↔ _
      exact splitBlock_rel_iff W sel x y
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _
        (fun h ↦ hx (h.trans (W.rel_repr_left x)))]
      exact ⟨fun h ↦ ⟨h, Or.inl hx⟩, fun h ↦ h.1⟩
  · intro x y
    change (LocalResolution.pasteNewEdge W _ hC).Rel x y ↔ _
    unfold LocalResolution.pasteNewEdge
    rw [SheetPartition.paste_rel_iff]
    by_cases hx : W.Rel sel x
    · rw [LocalResolution.onBlock_of_rel _ _ _ _ _ (hx.trans (W.rel_repr_right x))]
      change (W.splitBlock sel).Rel x y ↔ _
      rw [W.splitBlock_rel_of_rel_anchor_iff sel x hx]
    · rw [LocalResolution.onBlock_of_not_rel _ _ _ _ _
        (fun h ↦ hx (h.trans (W.rel_repr_left x)))]
      change (W.splitBlock (W.repr x)).Rel x y ↔ _
      rw [W.splitBlock_rel_of_rel_anchor_iff _ x (W.rel_repr_left x)]

/-- The pasted joined resolution. -/
theorem joinedShape_paste (W : SheetPartition d) (sel : Fin d)
    (hC : ∀ anchor, (LocalResolution.onBlock W sel (ResolutionM11.joinedResolutionAt W)
      (fun _ ↦ ResolutionM11.joinedResolutionAt W) anchor).ContractsTo W) :
    JoinedShape W (LocalResolution.paste W (LocalResolution.onBlock W sel
      (ResolutionM11.joinedResolutionAt W) (fun _ ↦ ResolutionM11.joinedResolutionAt W)) hC) := by
  have hOn : ∀ a, LocalResolution.onBlock W sel (ResolutionM11.joinedResolutionAt W)
      (fun _ ↦ ResolutionM11.joinedResolutionAt W) a = ResolutionM11.joinedResolutionAt W := by
    intro a
    unfold LocalResolution.onBlock
    split_ifs <;> rfl
  refine ⟨fun x y ↦ ?_, fun x y ↦ ?_, fun x y ↦ ?_⟩
  · change (LocalResolution.pasteLeft W _ hC).Rel x y ↔ _
    unfold LocalResolution.pasteLeft
    rw [SheetPartition.paste_rel_iff, hOn]
    rfl
  · change (LocalResolution.pasteRight W _ hC).Rel x y ↔ _
    unfold LocalResolution.pasteRight
    rw [SheetPartition.paste_rel_iff, hOn]
    rfl
  · change (LocalResolution.pasteNewEdge W _ hC).Rel x y ↔ _
    unfold LocalResolution.pasteNewEdge
    rw [SheetPartition.paste_rel_iff, hOn]
    rfl

variable {target : CFGraph} {degree : ℕ} {wall : target.V}
  {data : GluingDatum target degree} {star : W2R1Target.TwoStar target wall}

theorem firstSplit_shape (input : SecondEquation.W2SourceInput data star)
    {block : W4Assembly.WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    SplitShape (data.vertexPartition wall) block.1
      (M11StarCensusProof.pasted (firstSplitPattern input profile hCard).candidate) :=
  splitShape_paste _ _ _

theorem secondSplit_shape (input : SecondEquation.W2SourceInput data star)
    {block : W4Assembly.WallBlock data wall}
    (profile : W2R2SourceProfile.SourceProfile data star block)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    SplitShape (data.vertexPartition wall) block.1
      (M11StarCensusProof.pasted
        (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate) := by
  have h : SplitShape ((M11RemoteCandidates.swappedDatum profile hCard).vertexPartition wall)
      block.1 (M11StarCensusProof.pasted
        (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate) :=
    splitShape_paste _ _ _
  exact h.congr_wall (M11RemoteCandidates.swappedDatum_vertexPartition profile hCard)

theorem joined_shape (block : W4Assembly.WallBlock data wall)
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) :
    JoinedShape (data.vertexPartition wall)
      (M11StarCensusProof.pasted (joinedPattern data star block hCard).candidate) :=
  joinedShape_paste _ _ _

end CandidateShapes

/-! ## 3.  Representative gauge, and a decoupled transport from relational data -/

section Gauge

variable {d : ℕ}

theorem relabel_rel_iff' (P : SheetPartition d) (τ : Equiv.Perm (Fin d)) (x y : Fin d) :
    (P.relabel τ).Rel x y ↔ P.Rel (τ.symm x) (τ.symm y) := by
  have h := P.relabel_rel_iff τ (τ.symm x) (τ.symm y)
  rwa [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h

/-- **Representative gauge.**  A permutation carrying one partition's relation onto
another's can be corrected, inside the blocks of the target, into one carrying the
stored representatives as well. -/
theorem exists_gauge (P Q : SheetPartition d) (τ : Equiv.Perm (Fin d))
    (h : ∀ a b, P.Rel a b ↔ Q.Rel (τ a) (τ b)) :
    ∃ σ : Equiv.Perm (Fin d), Q = P.relabel σ ∧ ∀ s, Q.Rel (σ s) (τ s) := by
  have hSame : (P.relabel τ).SameBlocks Q := by
    intro x y
    rw [relabel_rel_iff', h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  refine ⟨τ.trans (PartitionNormalization.permutation _ _ hSame), ?_, fun s ↦ ?_⟩
  · rw [← SheetPartition.relabel_relabel, PartitionNormalization.relabel_eq]
  · exact (hSame _ _).mp (PartitionNormalization.permutation_rel _ _ hSame (τ s))

end Gauge

section Builder

open ResolutionExpansionFree

variable {target otherTarget : CFGraph} {degree : ℕ}
  {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}

/-- **A decoupled transport from relational data.**  Three permutations `τO`, `τF`,
`τN` that carry the three partitions of the member's resolution onto the candidate's
*as relations*, agree with the wall permutation modulo the merged partition, are
mutually compatible on the regrown occurrence, and are compatible with every incident
occurrence permutation, are gauged into a `TransportFree`. -/
theorem nonempty_transportFree_of_rel (iso : GeometricDatumIso first second)
    (wall : target.V) (otherWall : otherTarget.V)
    (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
    (res res' : LocalResolution degree)
    (hWall : iso.targetVertex wall = otherWall)
    (hSide : ∀ edge, otherRight (iso.targetEdge edge) = right edge)
    (hLref : res.left.Refines (first.vertexPartition wall))
    (hRref : res.right.Refines (first.vertexPartition wall))
    (τO τF τN : Equiv.Perm (Fin degree))
    (hOm : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (τO s)) s)
    (hFm : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (τF s)) s)
    (hL : ∀ a b, res.left.Rel a b ↔ res'.left.Rel (τO a) (τO b))
    (hR : ∀ a b, res.right.Rel a b ↔ res'.right.Rel (τF a) (τF b))
    (hN : ∀ a b, res.newEdge.Rel a b ↔ res'.newEdge.Rel (τN a) (τN b))
    (hNO : ∀ s, res.left.Rel (τO.symm (τN s)) s)
    (hNF : ∀ s, res.right.Rel (τF.symm (τN s)) s)
    (hEnd : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨ (edge : target.V × target.V).2 = wall) →
      ∀ s, (if right edge then res.right else res.left).Rel
        ((if right edge then τF else τO).symm (iso.edgePerm edge s)) s) :
    Nonempty (TransportFree iso wall otherWall right otherRight res res') := by
  obtain ⟨σO, hσO, hσOr⟩ := exists_gauge res.left res'.left τO hL
  obtain ⟨σF, hσF, hσFr⟩ := exists_gauge res.right res'.right τF hR
  obtain ⟨σN, hσN, hσNr⟩ := exists_gauge res.newEdge res'.newEdge τN hN
  -- the gauged permutation still reads, through `τ`, inside the member's block
  have back : ∀ (P Q : SheetPartition degree) (τ σ : Equiv.Perm (Fin degree)),
      (∀ a b, P.Rel a b ↔ Q.Rel (τ a) (τ b)) → (∀ s, Q.Rel (σ s) (τ s)) →
        ∀ u v, Q.Rel (σ u) v → P.Rel u (τ.symm v) := by
    intro P Q τ σ hPQ hσ u v huv
    rw [hPQ, Equiv.apply_symm_apply]
    exact (hσ u).symm.trans huv
  refine ⟨⟨σO, σF, σN, hWall, hSide, ?_, ?_, hσO, hσF, hσN, ?_, ?_, ?_⟩⟩
  · intro s
    have h1 : res.left.Rel (τO.symm (σO s)) s :=
      (back res.left res'.left τO σO hL hσOr s (σO s) rfl).symm
    have h2 := hOm (τO.symm (σO s))
    rw [Equiv.apply_symm_apply] at h2
    exact h2.trans (hLref.rel h1)
  · intro s
    have h1 : res.right.Rel (τF.symm (σF s)) s :=
      (back res.right res'.right τF σF hR hσFr s (σF s) rfl).symm
    have h2 := hFm (τF.symm (σF s))
    rw [Equiv.apply_symm_apply] at h2
    exact h2.trans (hRref.rel h1)
  · intro s
    have hNL : res'.left.Rel (σN s) (τN s) := res'.edge_refines_left.rel (hσNr s)
    have h1 := back res.left res'.left τO σO hL hσOr (σO.symm (σN s)) (τN s)
      (by rw [Equiv.apply_symm_apply]; exact hNL)
    exact h1.trans (hNO s)
  · intro s
    have hNR : res'.right.Rel (σN s) (τN s) := res'.edge_refines_right.rel (hσNr s)
    have h1 := back res.right res'.right τF σF hR hσFr (σF.symm (σN s)) (τN s)
      (by rw [Equiv.apply_symm_apply]; exact hNR)
    exact h1.trans (hNF s)
  · intro edge hInc s
    have hE := hEnd edge hInc s
    by_cases hr : right edge = true
    · simp only [hr, ite_true] at hE ⊢
      have h1 := back res.right res'.right τF σF hR hσFr (σF.symm (iso.edgePerm edge s))
        (iso.edgePerm edge s) (by rw [Equiv.apply_symm_apply]; rfl)
      exact h1.trans hE
    · simp only [hr, ite_false, Bool.false_eq_true] at hE ⊢
      have h1 := back res.left res'.left τO σO hL hσOr (σO.symm (iso.edgePerm edge s))
        (iso.edgePerm edge s) (by rw [Equiv.apply_symm_apply]; rfl)
      exact h1.trans hE

end Builder

/-! ## 4.  Split and joined transports from shapes -/

section ShapeTransport

open ResolutionExpansionFree

variable {target otherTarget : CFGraph} {degree : ℕ}
  {first : GluingDatum target degree} {second : GluingDatum otherTarget degree}

theorem wall_rel_iff (iso : GeometricDatumIso first second) {wall : target.V}
    {otherWall : otherTarget.V} (hWall : iso.targetVertex wall = otherWall) (x y : Fin degree) :
    (second.vertexPartition otherWall).Rel x y ↔
      (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm x)
        ((iso.vertexPerm wall).symm y) := by
  subst hWall
  rw [iso.vertexPartition wall, relabel_rel_iff']

/-- A permutation agreeing with the wall permutation modulo the merged partition carries
the merged relation. -/
theorem wall_rel_iff_of_agree (iso : GeometricDatumIso first second) {wall : target.V}
    {otherWall : otherTarget.V} (hWall : iso.targetVertex wall = otherWall)
    (E : Equiv.Perm (Fin degree))
    (hE : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (E s)) s)
    (x y : Fin degree) :
    (first.vertexPartition wall).Rel x y ↔ (second.vertexPartition otherWall).Rel (E x) (E y) := by
  rw [wall_rel_iff iso hWall]
  constructor
  · intro h
    exact (hE x).trans (h.trans (hE y).symm)
  · intro h
    exact (hE x).symm.trans (h.trans (hE y))

theorem splitShape_refines_left {d : ℕ} {W : SheetPartition d} {b : Fin d}
    {r : LocalResolution d} (h : SplitShape W b r) : r.left.Refines W :=
  fun x y hxy ↦ ((h.left x y).mp hxy).1

theorem splitShape_refines_right {d : ℕ} {W : SheetPartition d} {b : Fin d}
    {r : LocalResolution d} (h : SplitShape W b r) : r.right.Refines W :=
  fun x y hxy ↦ ((h.right x y).mp hxy).1

/-- **Split to split.**  Along a limit isomorphism whose occurrence permutations at the
wall agree with one permutation `E` on the distinguished block (coherence), the member's
split resolution is carried onto the candidate's by a decoupled transport. -/
theorem nonempty_transportFree_split (iso : GeometricDatumIso first second)
    (wall : target.V) (otherWall : otherTarget.V)
    (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
    (res res' : LocalResolution degree) (b b' : Fin degree)
    (hWall : iso.targetVertex wall = otherWall)
    (hSide : ∀ edge, otherRight (iso.targetEdge edge) = right edge)
    (hS : SplitShape (first.vertexPartition wall) b res)
    (hS' : SplitShape (second.vertexPartition otherWall) b' res')
    (hb : (second.vertexPartition otherWall).Rel b' (iso.vertexPerm wall b))
    (E : Equiv.Perm (Fin degree))
    (hE : ∀ s, (first.vertexPartition wall).Rel ((iso.vertexPerm wall).symm (E s)) s)
    (hRight : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨ (edge : target.V × target.V).2 = wall) →
      right edge = true)
    (hCoh : ∀ edge : target.edges,
      ((edge : target.V × target.V).1 = wall ∨ (edge : target.V × target.V).2 = wall) →
      ∀ s, (first.vertexPartition wall).Rel b s → iso.edgePerm edge s = E s) :
    Nonempty (TransportFree iso wall otherWall right otherRight res res') := by
  set W := first.vertexPartition wall
  set W' := second.vertexPartition otherWall
  have hWE := wall_rel_iff_of_agree iso hWall E hE
  have hBE : ∀ x, W.Rel b x ↔ W'.Rel b' (E x) := by
    intro x
    rw [hWE]
    constructor
    · intro h
      exact hb.trans (((wall_rel_iff iso hWall _ _).mpr (by
        rw [Equiv.symm_apply_apply]; exact (hE b).symm)).trans h)
    · intro h
      have h1 : W'.Rel (iso.vertexPerm wall b) (E b) :=
        (wall_rel_iff iso hWall _ _).mpr (by rw [Equiv.symm_apply_apply]; exact (hE b).symm)
      exact h1.symm.trans (hb.symm.trans h)
  have hEinj : ∀ x y, E x = E y ↔ x = y := fun x y ↦ E.injective.eq_iff
  refine nonempty_transportFree_of_rel iso wall otherWall right otherRight res res' hWall hSide
    (splitShape_refines_left hS) (splitShape_refines_right hS) E E E hE hE ?_ ?_ ?_ ?_ ?_ ?_
  · intro x y
    rw [hS.left, hS'.left, hWE, hBE, hEinj]
  · intro x y
    rw [hS.right, hS'.right, hWE, hBE, hEinj]
  · intro x y
    rw [hS.newEdge, hS'.newEdge, hEinj]
  · intro s
    rw [Equiv.symm_apply_apply]
    exact (hS.left s s).mpr ⟨rfl, Or.inr rfl⟩
  · intro s
    rw [Equiv.symm_apply_apply]
    exact (hS.right s s).mpr ⟨rfl, Or.inr rfl⟩
  · intro edge hInc s
    rw [ite_eq_left (hRight edge hInc), ite_eq_left (hRight edge hInc)]
    have hCompat := iso.compatible edge wall hInc s
    have hWs : W.Rel (E.symm (iso.edgePerm edge s)) s := by
      rw [hWE, Equiv.apply_symm_apply]
      have h1 : W'.Rel (iso.edgePerm edge s) (iso.vertexPerm wall s) :=
        (wall_rel_iff iso hWall _ _).mpr (by rw [Equiv.symm_apply_apply]; exact hCompat)
      have h2 : W'.Rel (E s) (iso.vertexPerm wall s) :=
        (wall_rel_iff iso hWall _ _).mpr (by rw [Equiv.symm_apply_apply]; exact hE s)
      exact h1.trans h2.symm
    refine (hS.right _ _).mpr ⟨hWs, ?_⟩
    by_cases hs : W.Rel b s
    · right
      rw [hCoh edge hInc s hs, Equiv.symm_apply_apply]
    · left
      exact fun h ↦ hs (h.trans hWs)

/-- **Joined to joined.**  No coherence is needed: every partition involved is the
merged one. -/
theorem nonempty_transportFree_joined (iso : GeometricDatumIso first second)
    (wall : target.V) (otherWall : otherTarget.V)
    (right : target.edges → Bool) (otherRight : otherTarget.edges → Bool)
    (res res' : LocalResolution degree)
    (hWall : iso.targetVertex wall = otherWall)
    (hSide : ∀ edge, otherRight (iso.targetEdge edge) = right edge)
    (hS : JoinedShape (first.vertexPartition wall) res)
    (hS' : JoinedShape (second.vertexPartition otherWall) res') :
    Nonempty (TransportFree iso wall otherWall right otherRight res res') := by
  set V := iso.vertexPerm wall
  have hV : ∀ s, (first.vertexPartition wall).Rel (V.symm (V s)) s := by
    intro s; rw [Equiv.symm_apply_apply]; rfl
  have hWV := wall_rel_iff_of_agree iso hWall V hV
  refine nonempty_transportFree_of_rel iso wall otherWall right otherRight res res' hWall hSide
    (fun x y h ↦ (hS.left x y).mp h) (fun x y h ↦ (hS.right x y).mp h) V V V hV hV
    ?_ ?_ ?_ ?_ ?_ ?_
  · intro x y; rw [hS.left, hS'.left, hWV]
  · intro x y; rw [hS.right, hS'.right, hWV]
  · intro x y; rw [hS.newEdge, hS'.newEdge, hWV]
  · intro s; rw [Equiv.symm_apply_apply]; exact (hS.left s s).mpr rfl
  · intro s; rw [Equiv.symm_apply_apply]; exact (hS.right s s).mpr rfl
  · intro edge hInc s
    have hCompat := iso.compatible edge wall hInc s
    by_cases hr : right edge = true
    · rw [ite_eq_left hr, ite_eq_left hr]; exact (hS.right _ _).mpr hCompat
    · rw [ite_eq_right hr, ite_eq_right hr]; exact (hS.left _ _).mpr hCompat

end ShapeTransport

/-! ## 5.  The W2 input and the M-11 profile, pulled back along a limit isomorphism

`LocalCases.W2SourceTransport` moves them along a sheet relabelling of one datum.  A
limit isomorphism also renames target vertices and occurrences; the transport is the
same field by field. -/

section InputTransport

open W4Assembly W2R2SourceProfile SecondEquation W2R1Target

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

theorem sourceEndpoint_of_rel {T : CFGraph} (data : GluingDatum T degree) (v : T.V)
    {s t : Fin degree} (h : (data.vertexPartition v).Rel s t) :
    data.sourceEndpoint v s = data.sourceEndpoint v t :=
  Subtype.ext (Prod.ext rfl h)

/-- The member-side block over a wall-side sheet. -/
def blockPre (iso : GeometricDatumIso first second) (wall : target₁.V) (sheet : Fin degree) :
    WallBlock first wall :=
  WallBlock.ofSheet first wall ((iso.vertexPerm wall).symm sheet)

theorem blockPre_rel (iso : GeometricDatumIso first second) (wall : target₁.V)
    (sheet : Fin degree) :
    (first.vertexPartition wall).Rel (blockPre iso wall sheet).1 ((iso.vertexPerm wall).symm sheet) :=
  (first.vertexPartition wall).rel_repr_left _

theorem sourceVertexEquiv_sourceEndpoint (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    (s : Fin degree) :
    iso.sourceVertexEquiv (first.sourceEndpoint wall s) =
      second.sourceEndpoint wall' (iso.vertexPerm wall s) := by
  subst hWall
  exact (ResolutionExpansion.sourceEndpoint_vertexPerm iso wall s).symm

theorem sourceVertexEquiv_blockPre (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    (block' : WallBlock second wall') :
    iso.sourceVertexEquiv (WallBlock.sourceVertex first wall (blockPre iso wall block'.1)) =
      WallBlock.sourceVertex second wall' block' := by
  unfold WallBlock.sourceVertex
  rw [sourceEndpoint_of_rel first wall (blockPre_rel iso wall block'.1),
    sourceVertexEquiv_sourceEndpoint iso hWall, Equiv.apply_symm_apply]

theorem sourceVertexEquiv_block (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    (block : WallBlock first wall) :
    iso.sourceVertexEquiv (WallBlock.sourceVertex first wall block) =
      WallBlock.sourceVertex second wall'
        (WallBlock.ofSheet second wall' (iso.vertexPerm wall block.1)) := by
  unfold WallBlock.sourceVertex
  rw [sourceVertexEquiv_sourceEndpoint iso hWall]
  exact sourceEndpoint_of_rel second wall' ((second.vertexPartition wall').rel_repr_right _)

theorem blockCard_blockPre (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    (sheet : Fin degree) :
    (first.vertexPartition wall).blockCard (blockPre iso wall sheet).1 =
      (second.vertexPartition wall').blockCard sheet := by
  subst hWall
  unfold SheetPartition.blockCard
  rw [(first.vertexPartition wall).block_eq_of_rel (blockPre_rel iso wall sheet),
    iso.vertexPartition wall]
  have h := (first.vertexPartition wall).relabel_blockCard (iso.vertexPerm wall)
    ((iso.vertexPerm wall).symm sheet)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem localRamification_blockPre (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    (block' : WallBlock second wall') :
    first.localRamification wall (blockPre iso wall block'.1) =
      second.localRamification wall' block' := by
  classical
  have hCardB := blockCard_blockPre iso hWall block'.1
  subst hWall
  unfold GluingDatum.localRamification
  have hSum : (∑ edge ∈ GluingDatum.incidentEdges (iso.targetVertex wall),
      ((second.edgePartition edge).blockCountWithin
        (second.vertexPartition (iso.targetVertex wall)) block'.1 : ℤ)) =
      ∑ edge ∈ GluingDatum.incidentEdges wall,
        ((first.edgePartition edge).blockCountWithin
          (first.vertexPartition wall) (blockPre iso wall block'.1).1 : ℤ) := by
    refine (Finset.sum_bij (fun edge _ ↦ iso.targetEdge edge) ?_ ?_ ?_ ?_).symm
    · exact fun edge hEdge ↦ (iso.mem_incidentEdges_map wall edge).mpr hEdge
    · exact fun _ _ _ _ h ↦ iso.targetEdge.injective h
    · intro edge hEdge
      refine ⟨iso.targetEdge.symm edge, ?_, iso.targetEdge.apply_symm_apply edge⟩
      refine (iso.mem_incidentEdges_map wall _).mp ?_
      rwa [Equiv.apply_symm_apply]
    · intro edge hEdge
      have h := iso.blockCountWithin_map wall edge hEdge ((iso.vertexPerm wall).symm block'.1)
      rw [Equiv.apply_symm_apply] at h
      unfold SheetPartition.blockCountWithin at h ⊢
      rw [(first.vertexPartition wall).block_eq_of_rel (blockPre_rel iso wall block'.1), ← h]
  rw [hSum, iso.incidentEdges_card_map wall, hCardB]

theorem nonDanglingValency_blockPre (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    (block' : WallBlock second wall') :
    nonDanglingValency first (WallBlock.sourceVertex first wall (blockPre iso wall block'.1)) =
      nonDanglingValency second (WallBlock.sourceVertex second wall' block') := by
  rw [← sourceVertexEquiv_blockPre iso hWall block', iso.nonDanglingValency_map hConnected]

/-- **The W2 input pulls back along a limit isomorphism**, with the pulled-back star. -/
theorem input_pullback (iso : GeometricDatumIso first second)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : TwoStar target₂ wall'} (input : W2SourceInput second star') :
    W2SourceInput first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star') := by
  have hConnected : first.Connected := iso.symm.connected input.valid.1
  refine { valid := iso.symm.valid_map input.valid
           stablePath_card := ?_
           dangling_no_glue := iso.symm.danglingEdgeNoGlue_map input.valid.1 input.dangling_no_glue
           nonDangling_valency := ?_
           equation_c := ?_ }
  · rw [Fintype.card_congr (iso.stablePathEquiv hConnected), input.stablePath_card]
    congr 1
    exact iso.targetEdgeCard_map
  · intro block
    have h := input.nonDangling_valency (WallBlock.ofSheet second wall' (iso.vertexPerm wall block.1))
    rwa [← sourceVertexEquiv_block iso hWall block, iso.nonDanglingValency_map hConnected] at h
  · rw [← MergePinning.targetExcess_map iso wall, hWall]
    exact input.equation_c

end InputTransport

section ProfileTransport

open W4Assembly W2R2SourceProfile SecondEquation W2R1Target

variable {target₁ target₂ : CFGraph} {degree : ℕ}
  {first : GluingDatum target₁ degree} {second : GluingDatum target₂ degree}

/-- Incident occurrences at corresponding source vertices correspond. -/
def incidentEquivOf (iso : GeometricDatumIso first second) {v : first.SourceVertex}
    {v' : second.SourceVertex} (h : iso.sourceVertexEquiv v = v') :
    IncidentSourceEdge first v ≃ IncidentSourceEdge second v' :=
  iso.sourceEdgeEquiv.subtypeEquiv fun edge ↦ by
    rw [← h]; exact (iso.incident_map_iff edge v).symm

theorem incidentEquivOf_val (iso : GeometricDatumIso first second) {v : first.SourceVertex}
    {v' : second.SourceVertex} (h : iso.sourceVertexEquiv v = v')
    (edge : IncidentSourceEdge first v) :
    (incidentEquivOf iso h edge).1 = iso.sourceEdgeEquiv edge.1 := rfl

theorem incidentEquivOf_target (iso : GeometricDatumIso first second) {v : first.SourceVertex}
    {v' : second.SourceVertex} (h : iso.sourceVertexEquiv v = v')
    (edge : IncidentSourceEdge first v) :
    (incidentEquivOf iso h edge).1.1.1 = iso.targetEdge edge.1.1.1 := rfl

/-- **The M-11 profile pulls back along a limit isomorphism**, to the pulled-back star
and the pulled-back block. -/
theorem nonempty_profile_pullback (iso : GeometricDatumIso first second)
    (hConnected : first.Connected)
    {wall : target₁.V} {wall' : target₂.V} (hWall : iso.targetVertex wall = wall')
    {star' : TwoStar target₂ wall'} {block' : WallBlock second wall'}
    (profile : SourceProfile second star' block') :
    Nonempty (SourceProfile first (M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star')
      (blockPre iso wall block'.1)) := by
  classical
  set star := M11WallExhaustion.pullbackTwoStar iso wall wall' hWall star'
  have hStar : ∀ label, iso.targetEdge (star.edge label) = star'.edge label :=
    M11WallExhaustion.pullbackTwoStar_edge iso wall wall' hWall star'
  set IE := incidentEquivOf iso (sourceVertexEquiv_blockPre iso hWall block')
  have hTarget : ∀ (e : IncidentSourceEdge first
      (WallBlock.sourceVertex first wall (blockPre iso wall block'.1))) (label : Fin 2),
      e.1.1.1 = star.edge label ↔ (IE e).1.1.1 = star'.edge label := by
    intro e label
    rw [incidentEquivOf_target, ← hStar label]
    exact iso.targetEdge.injective.eq_iff.symm
  have hDang : ∀ (e : IncidentSourceEdge first
      (WallBlock.sourceVertex first wall (blockPre iso wall block'.1))),
      IsDangling second (IE e).1 ↔ IsDangling first e.1 :=
    fun e ↦ iso.isDangling_map_iff hConnected e.1
  have hIndex : ∀ (e : IncidentSourceEdge first
      (WallBlock.sourceVertex first wall (blockPre iso wall block'.1))),
      second.sourceEdgeIndex (IE e).1 = first.sourceEdgeIndex e.1 :=
    fun e ↦ iso.sourceEdgeIndex_map e.1
  have hFibre : ∀ label (e : IncidentSourceEdge first
      (WallBlock.sourceVertex first wall (blockPre iso wall block'.1))),
      e ∈ survivingFibre first star (blockPre iso wall block'.1) label ↔
        IE e ∈ survivingFibre second star' block' label := by
    intro label e
    rw [survivingFibre.mem, survivingFibre.mem, hTarget, hDang]
  have hCard := blockCard_blockPre iso hWall block'.1
  let deleted : DeletedOccurrence first (blockPre iso wall block'.1) :=
    { edge := IE.symm profile.deleted.edge
      dangling := by
        rw [← hDang, Equiv.apply_symm_apply]; exact profile.deleted.dangling
      index_one := by
        rw [← hIndex, Equiv.apply_symm_apply]; exact profile.deleted.index_one
      unique := by
        intro other
        rw [← hDang, profile.deleted.unique, Equiv.eq_symm_apply] }
  refine ⟨⟨?_, ?_, profile.doubleLabel, profile.singleLabel, profile.labels_ne,
    IE.symm profile.first, IE.symm profile.second, IE.symm profile.third, deleted,
    fun h ↦ profile.first_ne_second (IE.symm.injective h), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩⟩
  · rw [localRamification_blockPre iso hWall block']; exact profile.ramification
  · rw [nonDanglingValency_blockPre iso hConnected hWall block']; exact profile.valency
  · rw [hTarget, Equiv.apply_symm_apply]; exact profile.first_target
  · rw [hTarget, Equiv.apply_symm_apply]; exact profile.second_target
  · rw [hTarget, Equiv.apply_symm_apply]; exact profile.third_target
  · rw [← hDang, Equiv.apply_symm_apply]; exact profile.first_survives
  · rw [← hDang, Equiv.apply_symm_apply]; exact profile.second_survives
  · rw [← hDang, Equiv.apply_symm_apply]; exact profile.third_survives
  · ext e
    rw [hFibre, profile.double_fibre]
    simp only [Finset.mem_insert, Finset.mem_singleton, Equiv.eq_symm_apply]
  · ext e
    rw [hFibre, profile.single_fibre]
    simp only [Finset.mem_singleton, Equiv.eq_symm_apply]
  · intro e
    rcases profile.exhaustive (IE e) with h | h | h | h
    · exact Or.inl (IE.eq_symm_apply.mpr h)
    · exact Or.inr (Or.inl (IE.eq_symm_apply.mpr h))
    · exact Or.inr (Or.inr (Or.inl (IE.eq_symm_apply.mpr h)))
    · exact Or.inr (Or.inr (Or.inr (IE.eq_symm_apply.mpr h)))
  · have h1 := hIndex (IE.symm profile.first)
    have h2 := hIndex (IE.symm profile.second)
    have h3 := hIndex (IE.symm profile.third)
    rw [Equiv.apply_symm_apply] at h1 h2 h3
    have hd : (deleted.edge.1.1.1 = star.edge profile.singleLabel ↔
          profile.deleted.edge.1.1.1 = star'.edge profile.singleLabel) ∧
        (deleted.edge.1.1.1 = star.edge profile.doubleLabel ↔
          profile.deleted.edge.1.1.1 = star'.edge profile.doubleLabel) := by
      constructor <;>
      · change (IE.symm profile.deleted.edge).1.1.1 = _ ↔ _
        rw [hTarget, Equiv.apply_symm_apply]
    change (deleted.edge.1.1.1 = star.edge profile.singleLabel ∧
        first.sourceEdgeIndex (IE.symm profile.first).1 +
          first.sourceEdgeIndex (IE.symm profile.second).1 =
          (first.vertexPartition wall).blockCard (blockPre iso wall block'.1).1 ∧
        first.sourceEdgeIndex (IE.symm profile.third).1 + 1 =
          (first.vertexPartition wall).blockCard (blockPre iso wall block'.1).1) ∨
      (deleted.edge.1.1.1 = star.edge profile.doubleLabel ∧
        first.sourceEdgeIndex (IE.symm profile.first).1 +
          first.sourceEdgeIndex (IE.symm profile.second).1 + 1 =
          (first.vertexPartition wall).blockCard (blockPre iso wall block'.1).1 ∧
        first.sourceEdgeIndex (IE.symm profile.third).1 =
          (first.vertexPartition wall).blockCard (blockPre iso wall block'.1).1)
    rw [hd.1, hd.2, ← h1, ← h2, ← h3, hCard]
    exact profile.cases

end ProfileTransport

/-! ## 6.  The member's own resolution has the split or the joined shape

Part I's incoming identification (`M11IncomingSplitMatching`,
`M11IncomingJoinedMatching`), read at the member's own contraction and its pulled-back
input and profile, through the candidate shapes of §2. -/

section MemberShape

open W4Assembly W2R1Target SecondEquation ContractionRamification
open M11IncomingTargetNormalization M11IncomingOuterPartitions

variable {d : ℕ}

theorem SplitShape.of_sameBlocks {W : SheetPartition d} {b : Fin d}
    {r r' : LocalResolution d} (h : SplitShape W b r')
    (hl : r.left.SameBlocks r'.left) (hr : r.right.SameBlocks r'.right)
    (hn : r.newEdge.SameBlocks r'.newEdge) : SplitShape W b r :=
  ⟨fun x y ↦ (hl x y).trans (h.left x y), fun x y ↦ (hr x y).trans (h.right x y),
    fun x y ↦ (hn x y).trans (h.newEdge x y)⟩

theorem JoinedShape.of_sameBlocks {W : SheetPartition d} {r : LocalResolution d}
    (hl : r.left.SameBlocks W) (hr : r.right.SameBlocks W) (hn : r.newEdge.SameBlocks W) :
    JoinedShape W r := ⟨hl, hr, hn⟩

variable {target : CFGraph} {degree : ℕ} {a b : target.V} {contracted : target.edges}
  {coordinate : Type*} [Fintype coordinate] [DecidableEq coordinate]
  (incoming : GluingDatum target degree)
  (hc : (contracted : target.V × target.V) = (a, b)) (hab : a ≠ b)
  (hOne : num_edges target a b = 1)
  (fullDim : FullDimensionalSourcePresentation incoming coordinate)
  (hForest : ContractionForest incoming a b contracted)
  {star : TwoStar (contract target hab hOne) ⟨a, hab⟩}
  (input : W2SourceInput (contractDatum incoming hc hab hOne) star)
  {block : WallBlock (contractDatum incoming hc hab hOne) ⟨a, hab⟩}
  (profile : W2R2SourceProfile.SourceProfile (contractDatum incoming hc hab hOne) star block)
  (hCard : ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩).blockCard block.1 = 2)

/-- In the joined valency pattern the two star occurrences lie on different sides. -/
theorem joined_sides_ne (hLeft : (GluingDatum.incidentEdges a).card = 2)
    (hRight : (GluingDatum.incidentEdges b).card = 2) :
    IncomingTargetExpansion.right hc hab hOne (star.edge 0) ≠
      IncomingTargetExpansion.right hc hab hOne (star.edge 1) := by
  classical
  obtain ⟨label, hPred⟩ :=
    IncomingW2TargetPlacement.right_eq_singleton_of_divalent hc hab hOne star hLeft hRight
  have hNe : star.edge 0 ≠ star.edge 1 := star.edge_injective.ne (by decide)
  rw [hPred]
  fin_cases label <;> simp [hNe, Ne.symm hNe]

include fullDim hForest input profile hCard in
/-- **A member normalized onto the split placement has the split shape.** -/
theorem incomingResolution_splitShape
    (second : (contract target hab hOne).edges → Bool)
    (hP : (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))
    (hSecond : second = fun _ ↦ true) :
    SplitShape ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩) block.1
      (M11WallExhaustion.incomingResolution incoming hc hab hOne second hP) := by
  subst hSecond
  have hShape := firstSplit_shape input profile hCard
  rcases valencySplit_of_twoStar incoming hc hab hOne fullDim.valid fullDim.changeMinimal star
    with hJ | hL | hR
  · exfalso
    have hNe := joined_sides_ne hc hab hOne (star := star) hJ.1 hJ.2.1
    rcases hP with h | h
    · exact hNe ((h _ (star.edge_mem_incidentEdges 0)).trans
        (h _ (star.edge_mem_incidentEdges 1)).symm)
    · exact hNe ((h _ (star.edge_mem_incidentEdges 0)).trans
        (h _ (star.edge_mem_incidentEdges 1)).symm)
  · have hV := M11IncomingSplitMatching.vertexPartitions_sameBlocks_of_left_leaf incoming hc hab
      hOne fullDim hForest input profile hCard hL.1
    have hE := M11IncomingSplitMatching.edgePartitions_sameBlocks_of_left_leaf incoming hc hab
      hOne fullDim hForest input profile hCard hL.1
    refine hShape.of_sameBlocks ?_ ?_ ?_
    · have h := hV (oldVertex (contract target hab hOne) ⟨a, hab⟩)
      have h2 := M11StarCensusProof.candidate_oldWall (firstSplitPattern input profile hCard).candidate
      exact fun x y ↦ (h x y).trans (by rw [h2])
    · have h := hV (freshVertex (contract target hab hOne))
      have h2 := M11StarCensusProof.candidate_fresh (firstSplitPattern input profile hCard).candidate
      exact fun x y ↦ (h x y).trans (by rw [h2])
    · have h := hE (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (fun _ ↦ true) none)
      have h2 := GlobalResolution.datum_edgePartition_new (contractDatum incoming hc hab hOne)
        ⟨a, hab⟩ (firstSplitPattern input profile hCard).candidate.right
        (M11StarCensusProof.pasted (firstSplitPattern input profile hCard).candidate)
        (GlobalAssembly.blockwiseCompatible _ _ _ _ _
          (firstSplitPattern input profile hCard).candidate.exterior)
      exact fun x y ↦ (h x y).trans (by rw [← h2]; rfl)
  · have hV := M11IncomingSplitMatching.vertexPartitions_sameBlocks_of_right_leaf incoming hc hab
      hOne fullDim hForest input profile hCard hR.2.1
    have hE := M11IncomingSplitMatching.edgePartitions_sameBlocks_of_right_leaf incoming hc hab
      hOne fullDim hForest input profile hCard hR.2.1
    refine hShape.of_sameBlocks ?_ ?_ ?_
    · have h := hV (oldVertex (contract target hab hOne) ⟨a, hab⟩)
      have h2 := M11StarCensusProof.candidate_oldWall (firstSplitPattern input profile hCard).candidate
      exact fun x y ↦ (h x y).trans (by rw [h2])
    · have h := hV (freshVertex (contract target hab hOne))
      have h2 := M11StarCensusProof.candidate_fresh (firstSplitPattern input profile hCard).candidate
      exact fun x y ↦ (h x y).trans (by rw [h2])
    · have h := hE (occurrenceEquiv (contract target hab hOne) ⟨a, hab⟩ (fun _ ↦ true) none)
      have h2 := GlobalResolution.datum_edgePartition_new (contractDatum incoming hc hab hOne)
        ⟨a, hab⟩ (firstSplitPattern input profile hCard).candidate.right
        (M11StarCensusProof.pasted (firstSplitPattern input profile hCard).candidate)
        (GlobalAssembly.blockwiseCompatible _ _ _ _ _
          (firstSplitPattern input profile hCard).candidate.exterior)
      exact fun x y ↦ (h x y).trans (by rw [← h2]; rfl)

include fullDim hForest input profile hCard in
/-- **A member normalized onto the joined placement has the joined shape.** -/
theorem incomingResolution_joinedShape
    (second : (contract target hab hOne).edges → Bool)
    (hP : (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = second edge) ∨
      (∀ edge ∈ GluingDatum.incidentEdges (target := contract target hab hOne) ⟨a, hab⟩,
        IncomingTargetExpansion.right hc hab hOne edge = !(second edge)))
    (hSecond : second = star.right) :
    JoinedShape ((contractDatum incoming hc hab hOne).vertexPartition ⟨a, hab⟩)
      (M11WallExhaustion.incomingResolution incoming hc hab hOne second hP) := by
  subst hSecond
  rcases valencySplit_of_twoStar incoming hc hab hOne fullDim.valid fullDim.changeMinimal star
    with hJ | hL | hR
  · have hSame := M11IncomingJoinedMatching.original_sameBlocks incoming hc hab hOne fullDim
      hForest input profile hCard hJ.1 hJ.2.1
    rw [contractDatum_vertexPartition_merge]
    have hPair := transported_endpointPartitions incoming hc hab hOne star.right hP
    have hNew := transported_edgePartition_new incoming hc hab hOne star.right hP
      fullDim.targetConnected fullDim.targetGenus
    have hSame' : ∀ {P Q : SheetPartition degree}, P = Q → Q.SameBlocks (mergedPartition incoming a b) →
        P.SameBlocks (mergedPartition incoming a b) := by
      intro P Q h hQ; rw [h]; exact hQ
    split_ifs at hPair
    · exact JoinedShape.of_sameBlocks (hSame' (congrArg Prod.fst hPair) hSame.1)
        (hSame' (congrArg Prod.snd hPair) hSame.2.2) (hSame' hNew hSame.2.1)
    · exact JoinedShape.of_sameBlocks (hSame' (congrArg Prod.fst hPair) hSame.2.2)
        (hSame' (congrArg Prod.snd hPair) hSame.1) (hSame' hNew hSame.2.1)
  · exfalso
    have h0 := IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hL.1 0
    have h1 := IncomingW2TargetPlacement.right_star_of_leaf_left hc hab hOne star hL.1 1
    rcases hP with h | h
    · have := h _ (star.edge_mem_incidentEdges 0)
      rw [h0] at this
      exact Bool.noConfusion (this.trans star.right_edge_zero)
    · have := h _ (star.edge_mem_incidentEdges 1)
      rw [h1] at this
      exact Bool.noConfusion (this.trans (congrArg (!·) star.right_edge_one))
  · exfalso
    have h0 := IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hR.2.1 0
    have h1 := IncomingW2TargetPlacement.right_star_of_leaf_right hc hab hOne star hR.2.1 1
    rcases hP with h | h
    · have := h _ (star.edge_mem_incidentEdges 1)
      rw [h1] at this
      exact Bool.noConfusion (this.trans star.right_edge_one)
    · have := h _ (star.edge_mem_incidentEdges 0)
      rw [h0] at this
      exact Bool.noConfusion (this.trans (congrArg (!·) star.right_edge_zero))

end MemberShape

/-! ## 7.  A position that receives a member is nonsingular -/

section Nonsingular

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  {w : Regrowth core y degree}
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p))

/-- **Any full-dimensional presentation of a position's datum makes the position
nonsingular**: Equation (6)'s labelling differs from the presentation's by a row and a
column permutation. -/
theorem nonsingular_of_fullDim (q : Fin 3)
    (fd : FullDimensionalSourcePresentation
      (M11RemoteCandidates.candidates input profile hCard q).datum (Fin p)) :
    M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q := by
  classical
  unfold M11StarParityFree.Nonsingular
  rw [DraismaVargas.Count.matrix_labelling_submatrix
    (M11StarParityFree.lab input profile hCard incoming incomingFD q) fd.labelling]
  intro h
  have hAbs := Matrix.abs_det_submatrix_equiv_equiv
    ((M11StarParityFree.lab input profile hCard incoming incomingFD q).row.symm.trans
      fd.labelling.row)
    ((M11StarParityFree.lab input profile hCard incoming incomingFD q).targetEdge.trans
      fd.labelling.targetEdge.symm)
    (GluingDatum.LengthMatrixPresentation.matrix fd.labelling.presentation)
  rw [h, abs_zero] at hAbs
  exact fd.det_ne_zero (abs_eq_zero.mp hAbs.symm)

end Nonsingular

/-! ## 8.  The coherence dichotomy -/

section Dichotomy

/-- **Two injections into a two-element set agree, or differ by its transposition,
uniformly** on any domain. -/
theorem agree_or_swap {α β : Type*} [DecidableEq α] (u v : α) (huv : u ≠ v)
    (T : β → Prop) (f g : β → α) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfT : ∀ s, T s → f s = u ∨ f s = v) (hgT : ∀ s, T s → g s = u ∨ g s = v) :
    (∀ s, T s → f s = g s) ∨ (∀ s, T s → f s = Equiv.swap u v (g s)) := by
  by_cases h : ∀ s, T s → f s = g s
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨s₀, hs₀, hne⟩ := h
    intro t ht
    by_cases hft : f t = g t
    · exfalso
      have hts : t ≠ s₀ := fun h ↦ hne (h ▸ hft)
      have h1 : f t ≠ f s₀ := hf.ne hts
      have h2 : g t ≠ g s₀ := hg.ne hts
      rcases hfT t ht with a | a <;> rcases hfT s₀ hs₀ with b | b <;>
        rcases hgT t ht with c | c <;> rcases hgT s₀ hs₀ with e | e <;>
        simp_all
    · rcases hfT t ht with a | a <;> rcases hgT t ht with c | c
      · exact (hft (a.trans c.symm)).elim
      · rw [a, c, Equiv.swap_apply_right]
      · rw [a, c, Equiv.swap_apply_left]
      · exact (hft (a.trans c.symm)).elim

variable {T : CFGraph} {wall : T.V}

/-- The two labelled occurrences are all the occurrences at a divalent vertex. -/
theorem eq_edge_of_incident (star : W2R1Target.TwoStar T wall) (edge : T.edges)
    (h : (edge : T.V × T.V).1 = wall ∨ (edge : T.V × T.V).2 = wall) :
    edge = star.edge 0 ∨ edge = star.edge 1 := by
  have hMem : edge ∈ GluingDatum.incidentEdges wall := by
    simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using h
  obtain ⟨label, hLabel⟩ := star.label.surjective ⟨edge, hMem⟩
  have hEdge : star.edge label = edge := congrArg Subtype.val hLabel
  fin_cases label
  · exact Or.inl hEdge.symm
  · exact Or.inr hEdge.symm

theorem incident_of_edge (star : W2R1Target.TwoStar T wall) (label : Fin 2) :
    ((star.edge label : T.edges) : T.V × T.V).1 = wall ∨
      ((star.edge label : T.edges) : T.V × T.V).2 = wall := by
  have h := star.edge_mem_incidentEdges label
  simpa only [GluingDatum.incidentEdges, Finset.mem_filter, Finset.mem_univ, true_and] using h

/-- The distinguished block of an M-11 wall consists of its two named sheets. -/
theorem block_eq_or {degree : ℕ} {data : GluingDatum T degree} {block : W4Assembly.WallBlock data wall}
    (hCard : (data.vertexPartition wall).blockCard block.1 = 2) (u : Fin degree)
    (hu : (data.vertexPartition wall).Rel block.1 u) :
    u = block.1 ∨ u = M11RemoteCandidates.otherSheet block hCard := by
  classical
  obtain ⟨hRel, hNe⟩ := M11RemoteCandidates.otherSheet_spec block hCard
  have hMem : ∀ x, (data.vertexPartition wall).Rel block.1 x →
      x ∈ (data.vertexPartition wall).block block.1 :=
    fun x hx ↦ ((data.vertexPartition wall).mem_block_iff _ _).mpr hx
  have hSub : ({block.1, M11RemoteCandidates.otherSheet block hCard} : Finset (Fin degree)) ⊆
      (data.vertexPartition wall).block block.1 := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hMem _ rfl
    · exact hMem _ hRel
  have hEq := Finset.eq_of_subset_of_card_le hSub (by
    rw [Finset.card_pair hNe]; exact hCard.le)
  have := hMem u hu
  rw [← hEq, Finset.mem_insert, Finset.mem_singleton] at this
  exact this

end Dichotomy

/-! ## 9.  An arbitrary star member, read through its limit isomorphism -/

section Member

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

include profile hCard in
/-- **A split member has Figure 32's split shape on its own limit**, around the pulled-back
block. -/
theorem member_splitShape
    (hSide : M11WallExhaustion.memberSide (M11StarCensusProof.pinned w hy input) star other ψ = false) :
    SplitShape (other.limit.vertexPartition (mergeVertex other)) (blockPre ψ.datum (mergeVertex other) block.1).1
      (M11WallExhaustion.memberResolution (M11StarCensusProof.pinned w hy input) star other ψ) := by
  have hW := M11StarCensusProof.pinned w hy input other ψ
  obtain ⟨profile'⟩ := nonempty_profile_pullback ψ.datum (InheritedLimitRows.limit_connected other)
    hW profile
  have input' := input_pullback ψ.datum hW input
  have hCard' := (blockCard_blockPre ψ.datum hW block.1).trans hCard
  exact incomingResolution_splitShape other.frame.data rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) other.frame.fullDim (InheritedLimitRows.forest other hy)
    input' profile' hCard'
    (M11WallExhaustion.memberPlacement (M11StarCensusProof.pinned w hy input) star other ψ)
    (M11WallExhaustion.memberPlacement_spec (M11StarCensusProof.pinned w hy input) star other ψ) (by
      unfold M11WallExhaustion.memberPlacement
      rw [hSide]
      exact M11WallExhaustion.divalentPlacement_false _ _ _)

include profile hCard in
/-- **A joined member has the joined shape on its own limit.** -/
theorem member_joinedShape
    (hSide : M11WallExhaustion.memberSide (M11StarCensusProof.pinned w hy input) star other ψ = true) :
    JoinedShape (other.limit.vertexPartition (mergeVertex other))
      (M11WallExhaustion.memberResolution (M11StarCensusProof.pinned w hy input) star other ψ) := by
  have hW := M11StarCensusProof.pinned w hy input other ψ
  obtain ⟨profile'⟩ := nonempty_profile_pullback ψ.datum (InheritedLimitRows.limit_connected other)
    hW profile
  have input' := input_pullback ψ.datum hW input
  have hCard' := (blockCard_blockPre ψ.datum hW block.1).trans hCard
  exact incomingResolution_joinedShape other.frame.data rfl (fst_ne_snd (other.frame.edgeOf other.column))
    (other.frame.numEdges_edgeOf other.column) other.frame.fullDim (InheritedLimitRows.forest other hy)
    input' profile' hCard'
    (M11WallExhaustion.memberPlacement (M11StarCensusProof.pinned w hy input) star other ψ)
    (M11WallExhaustion.memberPlacement_spec (M11StarCensusProof.pinned w hy input) star other ψ) (by
      unfold M11WallExhaustion.memberPlacement
      rw [hSide]
      exact M11WallExhaustion.divalentPlacement_true _ _ _)

end Member

/-! ## 10.  The three position transports -/

section Receipts

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
  (other : Regrowth core y degree) (ψ : GeometricStar.LimitIso hy other w)

/-- The member's pulled-back block is the pull-back of the wall's. -/
theorem wall_rel_blockPre {second : GluingDatum (w.frame.limitTarget w.column) degree}
    (iso : GeometricDatumIso other.limit second)
    (hWall : iso.targetVertex (mergeVertex other) = mergeVertex w)
    (hV : iso.vertexPerm (mergeVertex other) = ψ.datum.vertexPerm (mergeVertex other)) :
    (second.vertexPartition (mergeVertex w)).Rel block.1
      (iso.vertexPerm (mergeVertex other) (blockPre ψ.datum (mergeVertex other) block.1).1) := by
  rw [wall_rel_iff iso hWall, Equiv.symm_apply_apply, hV]
  exact (blockPre_rel ψ.datum (mergeVertex other) block.1).symm

include profile hCard in
/-- **Position `0` receives a coherent split member.** -/
theorem transport_zero
    (hSide : M11WallExhaustion.memberSide (M11StarCensusProof.pinned w hy input) star other ψ = false)
    (hCoh : ∀ s, (other.limit.vertexPartition (mergeVertex other)).Rel
        (blockPre ψ.datum (mergeVertex other) block.1).1 s →
      ψ.datum.edgePerm ((M11WallExhaustion.inheritedStar (M11StarCensusProof.pinned w hy input)
          star other ψ).edge 0) s =
        ψ.datum.edgePerm ((M11WallExhaustion.inheritedStar (M11StarCensusProof.pinned w hy input)
          star other ψ).edge 1) s) :
    Nonempty (M11StarCensusProof.PositionTransport w hy input profile hCard other ψ ⟨0, by decide⟩) := by
  set hPin := M11StarCensusProof.pinned w hy input
  set inh := M11WallExhaustion.inheritedStar hPin star other ψ
  have hPlace : ∀ e, M11WallExhaustion.memberPlacement hPin star other ψ e = true := by
    intro e
    unfold M11WallExhaustion.memberPlacement
    rw [hSide]
    exact congrFun (M11WallExhaustion.divalentPlacement_false _ _ _) e
  have hW : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetVertex (mergeVertex other) =
      mergeVertex w := hPin other ψ
  refine nonempty_transportFree_split (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm)
    (mergeVertex other) (mergeVertex w) _ _ _ _ _ block.1 hW
    (fun e ↦ (hPlace e).symm) (member_splitShape w hy input profile hCard other ψ hSide)
    (firstSplit_shape input profile hCard)
    (wall_rel_blockPre w hy other ψ _ hW rfl)
    ((ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).edgePerm (inh.edge 0))
    (fun s ↦ (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).compatible (inh.edge 0)
      (mergeVertex other) (incident_of_edge inh 0) s)
    (fun e _ ↦ hPlace e) ?_
  intro e hInc s hs
  rcases eq_edge_of_incident inh e hInc with rfl | rfl
  · rfl
  · exact (hCoh s hs).symm

include profile hCard in
/-- **Position `2` receives every joined member**, with no coherence condition. -/
theorem transport_two
    (hSide : M11WallExhaustion.memberSide (M11StarCensusProof.pinned w hy input) star other ψ = true) :
    Nonempty (M11StarCensusProof.PositionTransport w hy input profile hCard other ψ ⟨2, by decide⟩) := by
  set hPin := M11StarCensusProof.pinned w hy input
  set inh := M11WallExhaustion.inheritedStar hPin star other ψ
  have hPlace : ∀ e, M11WallExhaustion.memberPlacement hPin star other ψ e = inh.right e := by
    intro e
    unfold M11WallExhaustion.memberPlacement
    rw [hSide]
    exact congrFun (M11WallExhaustion.divalentPlacement_true _ _ _) e
  have hW : (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm).targetVertex (mergeVertex other) =
      mergeVertex w := hPin other ψ
  refine nonempty_transportFree_joined (ψ.datum.trans (GeometricDatumIso.refl w.limit).symm)
    (mergeVertex other) (mergeVertex w) _ _ _ _ hW ?_
    (member_joinedShape w hy input profile hCard other ψ hSide) (joined_shape block hCard)
  intro e
  rw [hPlace e]
  change star.right (ψ.datum.targetEdge e) = inh.right e
  unfold W2R1Target.TwoStar.right
  rw [← M11WallExhaustion.inheritedStar_edge hPin star other ψ 1]
  exact decide_eq_decide.mpr ψ.datum.targetEdge.injective.eq_iff

/-- The remote position's isomorphism fixes the wall permutation. -/
theorem remote_vertexPerm
    (hW : ψ.datum.targetVertex (mergeVertex other) = mergeVertex w) :
    (ψ.datum.trans (M11StarParityFree.branchIso profile hCard).symm.symm).vertexPerm
        (mergeVertex other) = ψ.datum.vertexPerm (mergeVertex other) := by
  change (ψ.datum.vertexPerm (mergeVertex other)).trans
    ((M11RemotePruning.branchRelabeling profile hCard).vertexPermutation
      (ψ.datum.targetVertex (mergeVertex other))).symm.symm = _
  rw [hW, M11RemotePruning.branchRelabeling_vertex_wall]
  rfl

include hCard in
/-- **Position `1` receives an incoherent split member**: the branch swap exchanges the
two sheets of the distinguished block on the double direction only. -/
theorem transport_one
    (hSide : M11WallExhaustion.memberSide (M11StarCensusProof.pinned w hy input) star other ψ = false)
    (hSwap : ∀ s, (other.limit.vertexPartition (mergeVertex other)).Rel
        (blockPre ψ.datum (mergeVertex other) block.1).1 s →
      ψ.datum.edgePerm ((M11WallExhaustion.inheritedStar (M11StarCensusProof.pinned w hy input)
          star other ψ).edge 0) s =
        Equiv.swap block.1 (M11RemoteCandidates.otherSheet block hCard)
          (ψ.datum.edgePerm ((M11WallExhaustion.inheritedStar
            (M11StarCensusProof.pinned w hy input) star other ψ).edge 1) s)) :
    Nonempty (M11StarCensusProof.PositionTransport w hy input profile hCard other ψ ⟨1, by decide⟩) := by
  set hPin := M11StarCensusProof.pinned w hy input
  set inh := M11WallExhaustion.inheritedStar hPin star other ψ
  set iso := ψ.datum.trans (M11StarParityFree.branchIso profile hCard).symm.symm
  have hPlace : ∀ e, M11WallExhaustion.memberPlacement hPin star other ψ e = true := by
    intro e
    unfold M11WallExhaustion.memberPlacement
    rw [hSide]
    exact congrFun (M11WallExhaustion.divalentPlacement_false _ _ _) e
  have hW : iso.targetVertex (mergeVertex other) = mergeVertex w := hPin other ψ
  have hEdge : ∀ (label : Fin 2) s, iso.edgePerm (inh.edge label) s =
      (M11RemotePruning.branchRelabeling profile hCard).edgePermutation (star.edge label)
        (ψ.datum.edgePerm (inh.edge label) s) := by
    intro label s
    change (M11RemotePruning.branchRelabeling profile hCard).edgePermutation
      (ψ.datum.targetEdge (inh.edge label)) (ψ.datum.edgePerm (inh.edge label) s) = _
    rw [M11WallExhaustion.inheritedStar_edge hPin star other ψ label]
  have hDouble := M11BranchSeparation.branchRelabeling_edge_double profile hCard
  have hSingle := M11BranchSeparation.branchRelabeling_edge_single
    (W4StarParity.limitTarget_connected w) (W4StarParity.limitTarget_genus w) profile hCard
  have hCoh : ∀ s, (other.limit.vertexPartition (mergeVertex other)).Rel
      (blockPre ψ.datum (mergeVertex other) block.1).1 s →
      iso.edgePerm (inh.edge 0) s = iso.edgePerm (inh.edge 1) s := by
    intro s hs
    rw [hEdge 0 s, hEdge 1 s, hSwap s hs]
    have hLabels := profile.labels_ne
    rcases Fin.exists_fin_two.mp ⟨profile.doubleLabel, rfl⟩ with hd | hd <;>
      rcases Fin.exists_fin_two.mp ⟨profile.singleLabel, rfl⟩ with hs' | hs'
    · exact (hLabels (hd.trans hs'.symm)).elim
    · rw [← hd, hDouble, ← hs', hSingle, Equiv.swap_apply_self]; rfl
    · rw [← hs', hSingle, ← hd, hDouble]; rfl
    · exact (hLabels (hd.trans hs'.symm)).elim
  refine nonempty_transportFree_split iso (mergeVertex other) (mergeVertex w) _ _ _ _ _ block.1 hW
    (fun e ↦ (hPlace e).symm) (member_splitShape w hy input profile hCard other ψ hSide)
    ((secondSplit_shape input profile hCard).congr_wall
      (M11RemoteCandidates.swappedDatum_vertexPartition profile hCard).symm)
    (wall_rel_blockPre w hy other ψ iso hW (remote_vertexPerm w hy profile hCard other ψ hW))
    (iso.edgePerm (inh.edge 0))
    (fun s ↦ iso.compatible (inh.edge 0) (mergeVertex other) (incident_of_edge inh 0) s)
    (fun e _ ↦ hPlace e) ?_
  intro e hInc s hs
  rcases eq_edge_of_incident inh e hInc with rfl | rfl
  · rfl
  · exact (hCoh s hs).symm

end Receipts

/-! ## 11.  Exhaustion -/

section Exhaustion

variable {n p degree : ℕ} {core : Core n p} {y : Fin p → ℚ}
  (w : Regrowth core y degree) (hy : Nondegenerate y)
  {star : W2R1Target.TwoStar (w.frame.limitTarget w.column) (mergeVertex w)}
  (input : SecondEquation.W2SourceInput w.limit star)
  {block : W4Assembly.WallBlock w.limit (mergeVertex w)}
  (profile : W2R2SourceProfile.SourceProfile w.limit star block)
  (hCard : (w.limit.vertexPartition (mergeVertex w)).blockCard block.1 = 2)
  {incoming : Fin 3}
  (incomingFD : FullDimensionalSourcePresentation
    (M11RemoteCandidates.candidates input profile hCard incoming).datum (Fin p))

/-- A received member hands its full-dimensional presentation to the position. -/
noncomputable def fdOfTransport (other : Regrowth core y degree)
    (ψ : GeometricStar.LimitIso hy other w)
    {T : CFGraph} {second : GluingDatum T degree} (iso : GeometricDatumIso other.limit second)
    {otherWall : T.V} {R : T.edges → Bool} {res' : LocalResolution degree}
    (hOther : GlobalResolution.OldCompatible second otherWall R res')
    (t : ResolutionExpansionFree.TransportFree iso (mergeVertex other) otherWall
      (M11WallExhaustion.memberPlacement (M11StarCensusProof.pinned w hy input) star other ψ) R
      (M11WallExhaustion.memberResolution (M11StarCensusProof.pinned w hy input) star other ψ)
      res') :
    FullDimensionalSourcePresentation (GlobalResolution.datum second otherWall R res' hOther)
      (Fin p) :=
  GeometricMultiplicity.transportFullDim
    ((M11WallExhaustion.normIso (M11StarCensusProof.pinned w hy input) star other ψ).trans
      (ResolutionExpansionFree.liftFree iso (mergeVertex other) otherWall _ R _ res'
        (M11WallExhaustion.memberCompatible (M11StarCensusProof.pinned w hy input) star other ψ)
        hOther t))
    other.frame.fullDim

/-- **Every star member is received, by a position transport, at a nonsingular
position.** -/
theorem exists_receipt (member : GeometricStar.StarMember hy w) :
    ∃ ψ : GeometricStar.LimitIso hy member.member w, ∃ q : Fin 3,
      ∃ _ : M11StarParityFree.Nonsingular input profile hCard incoming incomingFD q,
        Nonempty (M11StarCensusProof.PositionTransport w hy input profile hCard member.member ψ q) := by
  classical
  obtain ⟨ψ⟩ := member.specializes
  set other := member.member
  set hPin := M11StarCensusProof.pinned w hy input
  set inh := M11WallExhaustion.inheritedStar hPin star other ψ
  cases hSide : M11WallExhaustion.memberSide hPin star other ψ with
  | true =>
    obtain ⟨t⟩ := transport_two w hy input profile hCard other ψ hSide
    exact ⟨ψ, ⟨2, by decide⟩, nonsingular_of_fullDim input profile hCard incomingFD 2
      (fdOfTransport w hy input other ψ _ (GlobalAssembly.blockwiseCompatible _ _ _ _ _
        (joinedPattern w.limit star block hCard).candidate.exterior) t), ⟨t⟩⟩
  | false =>
    have hW := hPin other ψ
    set W' := w.limit.vertexPartition (mergeVertex w)
    have hInB : ∀ (label : Fin 2) s, (other.limit.vertexPartition (mergeVertex other)).Rel
        (blockPre ψ.datum (mergeVertex other) block.1).1 s →
        W'.Rel block.1 (ψ.datum.edgePerm (inh.edge label) s) := by
      intro label s hs
      have h1 : W'.Rel block.1 (ψ.datum.vertexPerm (mergeVertex other)
          (blockPre ψ.datum (mergeVertex other) block.1).1) :=
        wall_rel_blockPre w hy other ψ ψ.datum hW rfl
      have h2 : W'.Rel (ψ.datum.vertexPerm (mergeVertex other)
          (blockPre ψ.datum (mergeVertex other) block.1).1)
          (ψ.datum.vertexPerm (mergeVertex other) s) := by
        rw [wall_rel_iff ψ.datum hW, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact hs
      have h3 : W'.Rel (ψ.datum.vertexPerm (mergeVertex other) s)
          (ψ.datum.edgePerm (inh.edge label) s) := by
        rw [wall_rel_iff ψ.datum hW, Equiv.symm_apply_apply]
        exact (ψ.datum.compatible (inh.edge label) (mergeVertex other)
          (incident_of_edge inh label) s).symm
      exact h1.trans (h2.trans h3)
    rcases agree_or_swap block.1 (M11RemoteCandidates.otherSheet block hCard)
        (M11RemoteCandidates.otherSheet_spec block hCard).2
        (fun s ↦ (other.limit.vertexPartition (mergeVertex other)).Rel
          (blockPre ψ.datum (mergeVertex other) block.1).1 s)
        (ψ.datum.edgePerm (inh.edge 0)) (ψ.datum.edgePerm (inh.edge 1))
        (Equiv.injective _) (Equiv.injective _)
        (fun s hs ↦ block_eq_or hCard _ (hInB 0 s hs))
        (fun s hs ↦ block_eq_or hCard _ (hInB 1 s hs)) with hAgree | hSwap
    · obtain ⟨t⟩ := transport_zero w hy input profile hCard other ψ hSide hAgree
      exact ⟨ψ, ⟨0, by decide⟩, nonsingular_of_fullDim input profile hCard incomingFD 0
        (fdOfTransport w hy input other ψ _ (GlobalAssembly.blockwiseCompatible _ _ _ _ _
          (firstSplitPattern input profile hCard).candidate.exterior) t), ⟨t⟩⟩
    · obtain ⟨t⟩ := transport_one w hy input profile hCard other ψ hSide hSwap
      exact ⟨ψ, ⟨1, by decide⟩, nonsingular_of_fullDim input profile hCard incomingFD 1
        (fdOfTransport w hy input other ψ _ (GlobalAssembly.blockwiseCompatible _ _ _ _ _
          (M11RemoteCandidates.secondSplitPattern input profile hCard).candidate.exterior) t),
        ⟨t⟩⟩

/-- **Stage 2 at one wall: the positions exhaust the star.** -/
theorem exhausts : M11StarCensusProof.Exhausts w hy input profile hCard incomingFD :=
  M11StarCensusProof.exhausts_of_transports w hy input profile hCard incomingFD
    (exists_receipt w hy input profile hCard incomingFD)

end Exhaustion

/-! ## 12.  The family clause -/

/-- **The M-11 star exhaustion, at every core, degree and request.** -/
theorem m11StarExhaustion (degree n p : ℕ) : M11StarCensusProof.M11StarExhaustion degree n p :=
  fun _ _ hy w _ _ _ input _ profile hCard _ incomingFD ↦ exhausts w hy input profile hCard incomingFD

/-- **The M-11 star census**, unconditionally. -/
theorem m11StarCensus (degree n p : ℕ) : M11StarParityFree.M11StarCensus degree n p :=
  M11StarCensusProof.m11StarCensus_of_exhaustion (m11StarExhaustion degree n p)

/-- **The `w2M11` clause of `FamilyStarParity` at genus six and degree four, with no
hypothesis.** -/
theorem familyStarParity_w2M11 :
    RegrowthWallInput.FamilyStarParity (2 + 2) (4 * 2 + 2) (6 * 2 + 3) .w2M11 :=
  M11StarCensusProof.familyStarParity_w2M11_of_exhaustion (m11StarExhaustion _ _ _)

end DraismaVargas.Count.M11StarExhaustionProof
