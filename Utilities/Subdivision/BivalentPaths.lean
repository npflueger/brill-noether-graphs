module

public import Utilities.Subdivision.StrongSeparator
public import Utilities.Subdivision.CoreExpansion

@[expose] public section

/-!
# Bivalent paths and strong-separator cells

A **bivalent path** in a graph `G` (`BivalentPath`) is a walk `vtx 0, …, vtx len` whose
consecutive vertices are adjacent, whose interior vertices are adjacent only to their two path
neighbours (by single edges when those neighbours differ), and whose vertices are distinct
except possibly for the two ends. A slot of a subdivision specification is one (`slotPath`).

These paths certify rank-determining sets through the strong-separator criterion
(`Utilities.Certificate.StrongSeparator`, Luo's criterion that the closure of every
complementary component is contractible). Given a set `R` of vertices, a maximal interval of a
bivalent path that misses `R` and has distinct ends in `R` is a strong-separator cell
(`BivalentPath.Gap.cell`), and `BivalentPath.exists_cell` finds one around every vertex of the
path outside `R`, as soon as both ends are in `R` and, when they coincide, some interior vertex
is in `R` too.
-/

namespace Utilities.Subdivision.BivalentPaths

open Utilities Utilities.Certificate Utilities.Certificate.SubdivisionGraph
open Utilities.Certificate.StrongSeparator
open Utilities.Subdivision.CoreExpansion

/-! ## 1.  Bivalent paths and their gaps -/

/-- **A bivalent path** in `G`: vertices `vtx 0, …, vtx len`, consecutive ones adjacent, every
interior vertex adjacent to its two path neighbours only, by single edges when those neighbours
differ, and the vertices distinct except possibly for the two ends. -/
structure BivalentPath (G : CFGraph) where
  len : ℕ
  vtx : ℕ → G.V
  adj : ∀ t, t < len → 0 < num_edges G (vtx t) (vtx (t + 1))
  nbr : ∀ t, 0 < t → t < len → ∀ y, 0 < num_edges G (vtx t) y →
    y = vtx (t - 1) ∨ y = vtx (t + 1)
  mult : ∀ t, 0 < t → t < len → vtx (t - 1) ≠ vtx (t + 1) → ∀ y, num_edges G (vtx t) y ≤ 1
  inj : ∀ s t, s ≤ len → t ≤ len → vtx s = vtx t →
    s = t ∨ (s = 0 ∧ t = len) ∨ (s = len ∧ t = 0)

namespace BivalentPath

variable {G : CFGraph} (P : BivalentPath G)

/-- **A gap of `R` along `P`**: an open interval `(lo, hi)` of positions, nonempty, whose ends are
in `R`, distinct, and whose interior misses `R`. -/
structure Gap (R : Finset G.V) where
  lo : ℕ
  hi : ℕ
  c : ℕ
  lo_lt : lo < c
  lt_hi : c < hi
  hi_le : hi ≤ P.len
  lo_mem : P.vtx lo ∈ R
  hi_mem : P.vtx hi ∈ R
  gap : ∀ t, lo < t → t < hi → P.vtx t ∉ R
  ends_ne : P.vtx lo ≠ P.vtx hi

namespace Gap

variable {P} {R : Finset G.V} (g : P.Gap R)

/-- The vertices strictly inside the gap. -/
def carrier : Finset G.V := (Finset.Ioo g.lo g.hi).image P.vtx

theorem mem_carrier {x : G.V} : x ∈ g.carrier ↔ ∃ t, g.lo < t ∧ t < g.hi ∧ P.vtx t = x := by
  simp only [carrier, Finset.mem_image, Finset.mem_Ioo]
  constructor
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    exact ⟨t, h1, h2, rfl⟩
  · rintro ⟨t, h1, h2, rfl⟩
    exact ⟨t, ⟨h1, h2⟩, rfl⟩

theorem vtx_mem_carrier {t : ℕ} (h1 : g.lo < t) (h2 : t < g.hi) : P.vtx t ∈ g.carrier :=
  g.mem_carrier.mpr ⟨t, h1, h2, rfl⟩

/-- A vertex of `R` adjacent to a carrier vertex is an end of the gap, next to the first or the
last carrier vertex. -/
theorem neighbor_classification {t : ℕ} (h1 : g.lo < t) (h2 : t < g.hi) {y : G.V}
    (hy : y ∈ R) (hyx : 0 < num_edges G (P.vtx t) y) :
    (t = g.lo + 1 ∧ y = P.vtx g.lo) ∨ (t = g.hi - 1 ∧ y = P.vtx g.hi) := by
  have hL := g.hi_le
  rcases P.nbr t (by omega) (by omega) y hyx with h | h
  · left
    by_cases hlo : g.lo < t - 1
    · exact absurd (by rw [← h]; exact hy) (g.gap (t - 1) hlo (by omega))
    · refine ⟨by omega, ?_⟩
      rw [h, show t - 1 = g.lo by omega]
  · right
    by_cases hhi : t + 1 < g.hi
    · exact absurd (by rw [← h]; exact hy) (g.gap (t + 1) (by omega) hhi)
    · refine ⟨by omega, ?_⟩
      rw [h, show t + 1 = g.hi by omega]

/-- Inside a gap the two path neighbours of a vertex differ. -/
theorem neighbor_ne {t : ℕ} (h1 : g.lo < t) (h2 : t < g.hi) :
    P.vtx (t - 1) ≠ P.vtx (t + 1) := by
  intro h
  have hL := g.hi_le
  rcases P.inj (t - 1) (t + 1) (by omega) (by omega) h with h' | ⟨h0, hL'⟩ | ⟨h0, hL'⟩
  · omega
  · apply g.ends_ne
    rw [show g.lo = t - 1 by omega, show g.hi = t + 1 by omega]
    exact h
  · omega

theorem num_edges_le_one {t : ℕ} (h1 : g.lo < t) (h2 : t < g.hi) (y : G.V) :
    num_edges G (P.vtx t) y ≤ 1 :=
  P.mult t (by omega) (by have := g.hi_le; omega) (g.neighbor_ne h1 h2) y

theorem closed {x y : G.V} (hx : x ∈ g.carrier) (hy : y ∉ g.carrier)
    (hxy : 0 < num_edges G x y) : y ∈ R := by
  obtain ⟨t, h1, h2, rfl⟩ := g.mem_carrier.mp hx
  have hL := g.hi_le
  rcases P.nbr t (by omega) (by omega) y hxy with h | h
  · by_cases hlo : g.lo < t - 1
    · exact absurd (by rw [h]; exact g.vtx_mem_carrier hlo (by omega)) hy
    · rw [h, show t - 1 = g.lo by omega]
      exact g.lo_mem
  · by_cases hhi : t + 1 < g.hi
    · exact absurd (by rw [h]; exact g.vtx_mem_carrier (by omega) hhi) hy
    · rw [h, show t + 1 = g.hi by omega]
      exact g.hi_mem

theorem oneEdge {y : G.V} (hy : y ∈ R) : intoMultiplicity G g.carrier y ≤ 1 := by
  unfold intoMultiplicity
  by_cases hEx : ∃ x ∈ g.carrier, 0 < num_edges G y x
  · obtain ⟨x₀, hx₀, hpos₀⟩ := hEx
    have hUnique : ∀ x ∈ g.carrier, 0 < num_edges G y x → x = x₀ := by
      intro x hx hpos
      obtain ⟨t, h1, h2, rfl⟩ := g.mem_carrier.mp hx
      obtain ⟨t₀, h1₀, h2₀, rfl⟩ := g.mem_carrier.mp hx₀
      rw [num_edges_symmetric] at hpos hpos₀
      rcases g.neighbor_classification h1 h2 hy hpos with ⟨ht, hyt⟩ | ⟨ht, hyt⟩ <;>
        rcases g.neighbor_classification h1₀ h2₀ hy hpos₀ with ⟨ht₀, hyt₀⟩ | ⟨ht₀, hyt₀⟩
      · rw [ht, ht₀]
      · exact absurd (hyt.symm.trans hyt₀) g.ends_ne
      · exact absurd (hyt₀.symm.trans hyt) g.ends_ne
      · rw [ht, ht₀]
    calc (∑ x ∈ g.carrier, (num_edges G y x : ℤ)) = (num_edges G y x₀ : ℤ) := by
          apply Finset.sum_eq_single x₀
          · intro x hx hne
            have hz : ¬ 0 < num_edges G y x := fun h ↦ hne (hUnique x hx h)
            simp [Nat.eq_zero_of_not_pos hz]
          · intro h
            exact absurd hx₀ h
      _ ≤ 1 := by
          obtain ⟨t₀, h1₀, h2₀, rfl⟩ := g.mem_carrier.mp hx₀
          rw [num_edges_symmetric]
          exact_mod_cast g.num_edges_le_one h1₀ h2₀ y
  · have hz : ∀ x ∈ g.carrier, (num_edges G y x : ℤ) = 0 := by
      intro x hx
      have : ¬ 0 < num_edges G y x := fun h ↦ hEx ⟨x, hx, h⟩
      simp [Nat.eq_zero_of_not_pos this]
    rw [Finset.sum_eq_zero hz]
    norm_num

theorem pathCut {t : G.V} (htR : t ∈ R) (htB : IsBoundary G g.carrier t) (A : Finset G.V)
    (hA : P.vtx g.lo ∈ A) (htA : t ∉ A) :
    (∃ x ∈ g.carrier, x ∉ A ∧ ∃ y ∈ A, 0 < num_edges G x y) ∨
    (∃ x ∈ g.carrier, x ∈ A ∧ ∃ y, y ∉ A ∧ 0 < num_edges G x y) := by
  classical
  have hL := g.hi_le
  have hlc := g.lo_lt
  have hch := g.lt_hi
  obtain ⟨x, hx, hpos⟩ := htB
  obtain ⟨u, h1, h2, rfl⟩ := g.mem_carrier.mp hx
  rw [num_edges_symmetric] at hpos
  have hhi : t = P.vtx g.hi := by
    rcases g.neighbor_classification h1 h2 htR hpos with ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd (by rw [h]; exact hA) htA
    · exact h
  -- the last position of `[lo, hi)` whose vertex lies in `A`
  set s := Nat.findGreatest (fun s ↦ g.lo ≤ s ∧ P.vtx s ∈ A) (g.hi - 1) with hs
  have hsP : g.lo ≤ s ∧ P.vtx s ∈ A :=
    Nat.findGreatest_spec (P := fun s ↦ g.lo ≤ s ∧ P.vtx s ∈ A) (m := g.lo) (by omega)
      ⟨le_rfl, hA⟩
  have hsle : s ≤ g.hi - 1 := Nat.findGreatest_le _
  have hNext : P.vtx (s + 1) ∉ A := by
    by_cases hlast : s + 1 = g.hi
    · rw [hlast, ← hhi]
      exact htA
    · intro hA'
      exact Nat.findGreatest_is_greatest (P := fun s ↦ g.lo ≤ s ∧ P.vtx s ∈ A)
        (show s < s + 1 by omega) (by omega) ⟨by omega, hA'⟩
  have hEdge := P.adj s (by omega)
  by_cases hlast : s + 1 = g.hi
  · right
    exact ⟨P.vtx s, g.vtx_mem_carrier (by omega) (by omega), hsP.2, P.vtx (s + 1), hNext, hEdge⟩
  · left
    refine ⟨P.vtx (s + 1), g.vtx_mem_carrier (by omega) (by omega), hNext, P.vtx s, hsP.2, ?_⟩
    rw [num_edges_symmetric]
    exact hEdge

/-- **A gap is a strong-separator cell.** -/
def cell : ExpansionCell G R where
  carrier := g.carrier
  nonempty := ⟨_, g.vtx_mem_carrier g.lo_lt g.lt_hi⟩
  disjoint := Finset.disjoint_left.mpr fun x hx hxR ↦ by
    obtain ⟨t, h1, h2, rfl⟩ := g.mem_carrier.mp hx
    exact g.gap t h1 h2 hxR
  anchor := P.vtx g.lo
  anchor_mem := g.lo_mem
  anchor_boundary := by
    have := g.lo_lt
    have := g.lt_hi
    have := g.hi_le
    exact ⟨P.vtx (g.lo + 1), g.vtx_mem_carrier (by omega) (by omega), P.adj g.lo (by omega)⟩
  closed := fun hx hy hxy ↦ g.closed hx hy hxy
  oneEdge := fun hy ↦ g.oneEdge hy
  pathCut := fun ht hB A hA htA ↦ g.pathCut ht hB A hA htA

end Gap

/-- **Every vertex of a path missing `R` lies in a gap**, provided the ends are in `R` and, if
they coincide, some interior vertex is in `R`. -/
theorem exists_gap (R : Finset G.V) {c : ℕ} (hcL : c < P.len)
    (hc : P.vtx c ∉ R) (h0 : P.vtx 0 ∈ R) (hL : P.vtx P.len ∈ R)
    (hEnds : P.vtx 0 ≠ P.vtx P.len ∨ ∃ r, 0 < r ∧ r < P.len ∧ P.vtx r ∈ R) :
    Nonempty (P.Gap R) := by
  classical
  set lo := Nat.findGreatest (fun s ↦ P.vtx s ∈ R) c with hlo
  have hloR : P.vtx lo ∈ R :=
    Nat.findGreatest_spec (P := fun s ↦ P.vtx s ∈ R) (m := 0) (Nat.zero_le c) h0
  have hloc : lo ≤ c := Nat.findGreatest_le c
  have hloc' : lo < c := lt_of_le_of_ne hloc fun h ↦ hc (h ▸ hloR)
  have hloMax : ∀ t, lo < t → t ≤ c → P.vtx t ∉ R := fun t h1 h2 ↦
    Nat.findGreatest_is_greatest (P := fun s ↦ P.vtx s ∈ R) h1 h2
  have hExHi : ∃ i, P.vtx (c + 1 + i) ∈ R :=
    ⟨P.len - (c + 1), by rw [show c + 1 + (P.len - (c + 1)) = P.len by omega]; exact hL⟩
  have hiR : P.vtx (c + 1 + Nat.find hExHi) ∈ R := Nat.find_spec hExHi
  have hiLe : Nat.find hExHi ≤ P.len - (c + 1) :=
    Nat.find_min' hExHi (by rw [show c + 1 + (P.len - (c + 1)) = P.len by omega]; exact hL)
  have hGap : ∀ t, lo < t → t < c + 1 + Nat.find hExHi → P.vtx t ∉ R := by
    intro t h1 h2
    by_cases htc : t ≤ c
    · exact hloMax t h1 htc
    · have h := Nat.find_min hExHi (show t - (c + 1) < Nat.find hExHi by omega)
      rwa [show c + 1 + (t - (c + 1)) = t by omega] at h
  refine ⟨⟨lo, c + 1 + Nat.find hExHi, c, hloc', (by omega), (by omega), hloR, hiR, hGap, ?_⟩⟩
  intro hEq
  rcases P.inj lo (c + 1 + Nat.find hExHi) (by omega) (by omega) hEq with h | ⟨hl, hh⟩ | ⟨hl, hh⟩
  · omega
  · rcases hEnds with hne | ⟨r, hr0, hrL, hrR⟩
    · apply hne
      rw [← hl, ← hh]
      exact hEq
    · exact hGap r (by omega) (by omega) hrR
  · omega

theorem exists_cell (R : Finset G.V) {c : ℕ} (hcL : c < P.len)
    (hc : P.vtx c ∉ R) (h0 : P.vtx 0 ∈ R) (hL : P.vtx P.len ∈ R)
    (hEnds : P.vtx 0 ≠ P.vtx P.len ∨ ∃ r, 0 < r ∧ r < P.len ∧ P.vtx r ∈ R) :
    Nonempty (ExpansionCell G R) :=
  let ⟨g⟩ := P.exists_gap R hcL hc h0 hL hEnds
  ⟨g.cell⟩

end BivalentPath

/-! ## 2.  Slots and marker chains of a subdivision are bivalent paths -/

section SpecPaths

variable {n p : ℕ} (T : Spec n p)

/-- The vertex at position `t` along slot `j` (clamped). -/
def slotVtx (j : Fin p) (t : ℕ) : T.Vertex :=
  T.pathVertex j ⟨min t (T.length j), by omega⟩

theorem slotVtx_of_le (j : Fin p) {t : ℕ} (ht : t ≤ T.length j) :
    slotVtx T j t = T.pathVertex j ⟨t, by omega⟩ :=
  PathHelpers.pathVertex_congr T j _ _ (by simp [Nat.min_eq_left ht])

theorem slotVtx_zero (j : Fin p) : slotVtx T j 0 = T.coreVertex (T.core.tail j) := by
  rw [slotVtx_of_le T j (Nat.zero_le _)]
  exact PathHelpers.pathVertex_of_zero T j _ rfl

theorem slotVtx_length (j : Fin p) :
    slotVtx T j (T.length j) = T.coreVertex (T.core.head j) := by
  rw [slotVtx_of_le T j le_rfl]
  exact PathHelpers.pathVertex_of_last T j _ (T.length_pos j).ne' rfl

theorem slotVtx_interior (j : Fin p) {t : ℕ} (h0 : 0 < t) (hL : t < T.length j) :
    slotVtx T j t = T.interiorVertex j ⟨t - 1, by omega⟩ := by
  rw [slotVtx_of_le T j hL.le]
  exact PathHelpers.pathVertex_of_interior T j _ h0.ne' hL.ne

theorem slot_adj (j : Fin p) {t : ℕ} (ht : t < T.length j) :
    0 < num_edges T.graph (slotVtx T j t) (slotVtx T j (t + 1)) := by
  rw [slotVtx_of_le T j ht.le, slotVtx_of_le T j ht]
  exact T.consecutive_num_edges_pos j ⟨t, ht⟩

theorem slot_nbr (j : Fin p) {t : ℕ} (h0 : 0 < t) (hL : t < T.length j) (y : T.Vertex)
    (h : 0 < num_edges T.graph (slotVtx T j t) y) :
    y = slotVtx T j (t - 1) ∨ y = slotVtx T j (t + 1) := by
  have hI : T.IsInteriorPosition j ⟨t, by omega⟩ := ⟨h0, hL⟩
  rw [slotVtx_of_le T j hL.le] at h
  rcases (T.pathVertex_num_edges_pos_iff j _ hI y).mp h with h' | h'
  · left
    rw [h', slotVtx_of_le T j (by omega)]
    rfl
  · right
    rw [h', slotVtx_of_le T j (by omega)]
    rfl

theorem slot_mult (j : Fin p) {t : ℕ} (h0 : 0 < t) (hL : t < T.length j) (y : T.Vertex) :
    num_edges T.graph (slotVtx T j t) y ≤ 1 := by
  rw [slotVtx_interior T j h0 hL]
  exact T.num_edges_interior_le_one j _ y

theorem slot_inj (j : Fin p) {s t : ℕ} (hs : s ≤ T.length j) (ht : t ≤ T.length j)
    (h : slotVtx T j s = slotVtx T j t) : s = t := by
  rw [slotVtx_of_le T j hs, slotVtx_of_le T j ht] at h
  exact congrArg Fin.val (T.pathVertex_injective j h)

/-- **A slot is a bivalent path.** -/
def slotPath (j : Fin p) : BivalentPath T.graph where
  len := T.length j
  vtx := slotVtx T j
  adj := fun _ ht ↦ slot_adj T j ht
  nbr := fun _ h0 hL y h ↦ slot_nbr T j h0 hL y h
  mult := fun _ h0 hL _ y ↦ slot_mult T j h0 hL y
  inj := fun _ _ hs ht h ↦ Or.inl (slot_inj T j hs ht h)

end SpecPaths

end Utilities.Subdivision.BivalentPaths
