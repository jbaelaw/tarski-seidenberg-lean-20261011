import TS.PseudoDiv

/-!
# Closure of a finite family of polynomials

Over a domain `A`, every finite family `F ⊆ A[X]` is contained in a finite family closed under
derivatives, erasing the leading term, and pseudo-remainders `prem g h` for `deg h ≤ deg g`
(`closure`).  The construction proceeds by degree levels from the maximal degree downwards: the
members of degree `e` are those of `F`, the derivatives, truncations and pseudo-remainders of
members of larger degree that have degree `e`, together with `0`.
-/

namespace TS

open Polynomial
open scoped Classical

variable {A : Type*} [CommRing A] [IsDomain A]

/-- Closure under the three operations (pseudo-remainders only for `deg h ≤ deg g`). -/
structure IsClosedFam (F : Finset A[X]) : Prop where
  deriv : ∀ g ∈ F, derivative g ∈ F
  erase : ∀ g ∈ F, g.eraseLead ∈ F
  rem : ∀ g ∈ F, ∀ h ∈ F, h.natDegree ≤ g.natDegree → prem g h ∈ F

/-- The new members of degree `e` generated from the family `U` of members of larger degree. -/
noncomputable def newLevel (F U : Finset A[X]) (e : ℕ) : Finset A[X] :=
  (F.filter fun g => g.natDegree = e) ∪
    ((U.image derivative).filter fun g => g.natDegree = e) ∪
    ((U.image eraseLead).filter fun g => g.natDegree = e) ∪
    (((U ×ˢ U).image fun p => prem p.1 p.2).filter fun g => g.natDegree = e)

/-- `levels F D k`: the members of degree `> D - k` (levels `D, D-1, …, D-k+1`). -/
noncomputable def levels (F : Finset A[X]) (D : ℕ) : ℕ → Finset A[X]
  | 0 => ∅
  | k + 1 => levels F D k ∪ newLevel F (levels F D k) (D - k)

/-- The closure: all levels together with `0`. -/
noncomputable def closure (F : Finset A[X]) : Finset A[X] :=
  insert 0 (levels F (F.sup natDegree) (F.sup natDegree + 1))

theorem levels_mono (F : Finset A[X]) (D : ℕ) {j k : ℕ} (h : j ≤ k) :
    levels F D j ⊆ levels F D k := by
  induction k with
  | zero =>
    rw [Nat.le_zero.mp h]
  | succ k ih =>
    rcases Nat.of_le_succ h with h | rfl
    · refine (ih h).trans ?_
      simp only [levels]
      exact Finset.subset_union_left
    · exact subset_rfl

theorem mem_levels_degree (F : Finset A[X]) (D : ℕ) :
    ∀ k, ∀ g ∈ levels F D k, D + 1 - k ≤ g.natDegree ∧ g.natDegree ≤ D := by
  intro k
  induction k with
  | zero => intro g hg; simp [levels] at hg
  | succ k ih =>
    intro g hg
    simp only [levels, Finset.mem_union] at hg
    rcases hg with hg | hg
    · have := ih g hg
      omega
    · have hdeg : g.natDegree = D - k := by
        simp only [newLevel, Finset.mem_union, Finset.mem_filter] at hg
        rcases hg with ((hg | hg) | hg) | hg <;> exact hg.2
      omega

/-- Elements of `F` with degree `e ≤ D` are in the level of degree `e`. -/
theorem mem_levels_of_mem (F : Finset A[X]) (D : ℕ) {g : A[X]} (hg : g ∈ F)
    (hD : g.natDegree ≤ D) : g ∈ levels F D (D - g.natDegree + 1) := by
  simp only [levels, Finset.mem_union]
  right
  simp only [newLevel, Finset.mem_union, Finset.mem_filter]
  left; left; left
  refine ⟨hg, ?_⟩
  omega

/-- Every member lies in the level of its own degree. -/
theorem mem_levels_self (F : Finset A[X]) (D : ℕ) :
    ∀ k, k ≤ D + 1 → ∀ g ∈ levels F D k, g ∈ levels F D (D - g.natDegree + 1) := by
  intro k
  induction k with
  | zero => intro _ g hg; simp [levels] at hg
  | succ k ih =>
    intro hk g hg
    simp only [levels, Finset.mem_union] at hg
    rcases hg with hg | hg
    · exact ih (by omega) g hg
    · have hdeg : g.natDegree = D - k := by
        simp only [newLevel, Finset.mem_union, Finset.mem_filter] at hg
        rcases hg with ((hg | hg) | hg) | hg <;> exact hg.2
      have : D - g.natDegree + 1 = k + 1 := by omega
      rw [this]
      simp only [levels, Finset.mem_union]
      exact Or.inr hg

/-- Derivatives of members of smaller degree lie in the level of their degree. -/
theorem derivative_mem_levels (F : Finset A[X]) (D : ℕ) {g : A[X]} {k : ℕ} (hk : k ≤ D + 1)
    (hg : g ∈ levels F D k) (hlt : (derivative g).natDegree < g.natDegree) :
    derivative g ∈ levels F D (D - (derivative g).natDegree + 1) := by
  have hdeg := mem_levels_degree F D k g hg
  have hself := mem_levels_self F D k hk g hg
  simp only [levels, Finset.mem_union]
  right
  simp only [newLevel, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  left; left; right
  refine ⟨⟨g, ?_, rfl⟩, ?_⟩
  · exact levels_mono F D (by omega) hself
  · omega

theorem eraseLead_mem_levels (F : Finset A[X]) (D : ℕ) {g : A[X]} {k : ℕ} (hk : k ≤ D + 1)
    (hg : g ∈ levels F D k) (hlt : g.eraseLead.natDegree < g.natDegree) :
    g.eraseLead ∈ levels F D (D - g.eraseLead.natDegree + 1) := by
  have hdeg := mem_levels_degree F D k g hg
  have hself := mem_levels_self F D k hk g hg
  simp only [levels, Finset.mem_union]
  right
  simp only [newLevel, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  left; right
  refine ⟨⟨g, ?_, rfl⟩, ?_⟩
  · exact levels_mono F D (by omega) hself
  · omega

theorem prem_mem_levels (F : Finset A[X]) (D : ℕ) {g h : A[X]} {k₁ k₂ : ℕ} (hk₁ : k₁ ≤ D + 1)
    (hk₂ : k₂ ≤ D + 1) (hg : g ∈ levels F D k₁) (hh : h ∈ levels F D k₂)
    (hlt : (prem g h).natDegree < h.natDegree) (hgh : h.natDegree ≤ g.natDegree) :
    prem g h ∈ levels F D (D - (prem g h).natDegree + 1) := by
  have hdeg₁ := mem_levels_degree F D k₁ g hg
  have hdeg₂ := mem_levels_degree F D k₂ h hh
  have hself₁ := mem_levels_self F D k₁ hk₁ g hg
  have hself₂ := mem_levels_self F D k₂ hk₂ h hh
  simp only [levels, Finset.mem_union]
  right
  simp only [newLevel, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_product]
  right
  refine ⟨⟨(g, h), ⟨?_, ?_⟩, rfl⟩, ?_⟩
  · exact levels_mono F D (by omega) hself₁
  · exact levels_mono F D (by omega) hself₂
  · omega

theorem subset_closure (F : Finset A[X]) : F ⊆ closure F := by
  intro g hg
  have hD : g.natDegree ≤ F.sup natDegree := Finset.le_sup hg
  unfold closure
  apply Finset.mem_insert_of_mem
  exact levels_mono F _ (by omega) (mem_levels_of_mem F _ hg hD)

theorem zero_mem_closure (F : Finset A[X]) : (0 : A[X]) ∈ closure F := by
  unfold closure
  exact Finset.mem_insert_self _ _

theorem natDegree_le_of_mem_closure (F : Finset A[X]) {g : A[X]} (hg : g ∈ closure F) :
    g.natDegree ≤ F.sup natDegree := by
  unfold closure at hg
  rcases Finset.mem_insert.mp hg with rfl | hg
  · simp
  · exact (mem_levels_degree F _ _ g hg).2

/-- Pseudo-remainder of `0` is `0`. -/
theorem prem_zero_left (h : A[X]) : prem 0 h = 0 := by
  by_cases hh : h = 0
  · simp [prem, hh]
  obtain ⟨q, hq, hr⟩ := prem_spec 0 h hh
  rw [mul_zero] at hq
  have hqh : q * h = -prem 0 h := by linear_combination -hq
  by_cases hq0 : q = 0
  · rw [hq0, zero_mul] at hqh
    exact neg_eq_zero.mp hqh.symm
  · exfalso
    have h2 : h.degree ≤ (q * h).degree := by
      rw [degree_mul]
      exact le_add_of_nonneg_left (zero_le_degree_iff.mpr hq0)
    rw [hqh, degree_neg] at h2
    exact absurd (lt_of_le_of_lt h2 hr) (lt_irrefl _)

theorem prem_zero_right (g : A[X]) : prem g 0 = 0 := by simp [prem]

/-- **The closure is closed.** -/
theorem isClosedFam_closure (F : Finset A[X]) : IsClosedFam (closure F) := by
  set D := F.sup natDegree with hD
  have hmem : ∀ g, g ∈ closure F ↔ g = 0 ∨ g ∈ levels F D (D + 1) := fun g => by
    unfold closure
    rw [Finset.mem_insert]
  have hup : ∀ g, g ∈ levels F D (D - g.natDegree + 1) → g.natDegree ≤ D → g ∈ closure F := by
    intro g hg hgD
    rw [hmem]
    right
    exact levels_mono F D (by omega) hg
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases (hmem g).mp hg with rfl | hg
    · rw [derivative_zero]
      exact zero_mem_closure F
    · by_cases h0 : g.natDegree = 0
      · rw [eq_C_of_natDegree_eq_zero h0, derivative_C]
        exact zero_mem_closure F
      · have hlt : (derivative g).natDegree < g.natDegree := natDegree_derivative_lt h0
        have hdeg := mem_levels_degree F D _ g hg
        exact hup _ (derivative_mem_levels F D le_rfl hg hlt) (by omega)
  · intro g hg
    rcases (hmem g).mp hg with rfl | hg
    · rw [eraseLead_zero]
      exact zero_mem_closure F
    · rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero g with hlt | h0
      · have hdeg := mem_levels_degree F D _ g hg
        exact hup _ (eraseLead_mem_levels F D le_rfl hg hlt) (by omega)
      · rw [h0]
        exact zero_mem_closure F
  · intro g hg h hh hgh
    by_cases hh0 : h = 0
    · rw [hh0, prem_zero_right]
      exact zero_mem_closure F
    by_cases hg0 : g = 0
    · rw [hg0, prem_zero_left]
      exact zero_mem_closure F
    replace hh : h ∈ levels F D (D + 1) := by
      rcases (hmem h).mp hh with h' | h'
      · exact absurd h' hh0
      · exact h'
    replace hg : g ∈ levels F D (D + 1) := by
      rcases (hmem g).mp hg with h' | h'
      · exact absurd h' hg0
      · exact h'
    by_cases hh1 : h.natDegree = 0
    · obtain ⟨-, -, hr⟩ := prem_spec g h hh0
      rw [degree_eq_natDegree hh0, hh1, Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hr
      rw [hr]
      exact zero_mem_closure F
    · have hlt : (prem g h).natDegree < h.natDegree :=
        natDegree_prem_lt g h hh0 (Nat.pos_of_ne_zero hh1)
      have hdeg := mem_levels_degree F D _ h hh
      exact hup _ (prem_mem_levels F D le_rfl le_rfl hg hh hlt hgh) (by omega)

end TS
