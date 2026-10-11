import TS.RealPoly

/-!
# Sign vectors of a finite family and their cells

For a finite family `P : G → ℝ[X]` and a subfamily `S : Finset G`, `sgn S P t` is the sign vector
at `t` (zero outside `S`).  `Occ S P ε` says the vector `ε` occurs, `Before S P ε₁ ε₂` that `ε₁`
occurs somewhere to the left of `ε₂`.

The key fact (Rolle + minimal degree) is that for a family closed under derivatives the level
sets of `sgn` are intervals: if the sign vectors at `a` and `b` agree, they agree on `[a, b]`.
Consequently the occurring vectors are linearly ordered by `Before`, and `Before ε ε` holds exactly
for the "interval cells" (level sets with more than one point).
-/

namespace TS

open Polynomial Set

variable {G : Type*} [DecidableEq G]

/-- The sign vector of the subfamily `S` at `t` (zero outside `S`). -/
noncomputable def sgn (S : Finset G) (P : G → ℝ[X]) (t : ℝ) : G → SignType :=
  fun g => if g ∈ S then SignType.sign (eval t (P g)) else 0

/-- `ε` occurs as a sign vector. -/
def Occ (S : Finset G) (P : G → ℝ[X]) (ε : G → SignType) : Prop := ∃ t, sgn S P t = ε

/-- `ε₁` occurs somewhere to the left of `ε₂`. -/
def Before (S : Finset G) (P : G → ℝ[X]) (ε₁ ε₂ : G → SignType) : Prop :=
  ∃ t₁ t₂, t₁ < t₂ ∧ sgn S P t₁ = ε₁ ∧ sgn S P t₂ = ε₂

/-- Closure under derivatives: the derivative of a member of positive degree is a member. -/
def DerivClosed (S : Finset G) (P : G → ℝ[X]) : Prop :=
  ∀ g ∈ S, 0 < (P g).natDegree → ∃ g' ∈ S, P g' = derivative (P g)

variable {S : Finset G} {P : G → ℝ[X]}

theorem sgn_apply_of_mem {t : ℝ} {g : G} (hg : g ∈ S) :
    sgn S P t g = SignType.sign (eval t (P g)) := by simp [sgn, hg]

theorem sgn_apply_of_not_mem {t : ℝ} {g : G} (hg : g ∉ S) : sgn S P t g = 0 := by simp [sgn, hg]

/-- A derivative-closed family loses nothing by removing a member of maximal degree. -/
theorem DerivClosed.erase (hS : DerivClosed S P) {f : G}
    (hf : ∀ g ∈ S, (P g).natDegree ≤ (P f).natDegree) : DerivClosed (S.erase f) P := by
  intro g hg hdeg
  have hgS : g ∈ S := Finset.mem_of_mem_erase hg
  obtain ⟨g', hg'S, hg'⟩ := hS g hgS hdeg
  refine ⟨g', Finset.mem_erase.mpr ⟨?_, hg'S⟩, hg'⟩
  rintro rfl
  have h1 : (P g').natDegree < (P g).natDegree := by
    rw [hg']
    exact natDegree_derivative_lt hdeg.ne'
  exact absurd (hf g hgS) (not_le.mpr h1)

/-- **Convexity of level sets**: for a derivative-closed family, equal sign vectors at `a` and `b`
force the same sign vector on `[a, b]`. -/
theorem sgn_eq_of_between (hS : DerivClosed S P) {a b c : ℝ} (hab : sgn S P a = sgn S P b)
    (hac : a ≤ c) (hcb : c ≤ b) : sgn S P c = sgn S P a := by
  rcases eq_or_lt_of_le hac with rfl | hac'
  · rfl
  rcases eq_or_lt_of_le hcb with rfl | hcb'
  · exact hab.symm
  have hab' : a < b := hac'.trans hcb'
  -- no nonzero member has a root in `[a, b]`
  have key : ∀ g ∈ S, P g ≠ 0 → ∀ t ∈ Icc a b, eval t (P g) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hgS, hg0, t, ht, hgt⟩ := hcon
    classical
    set T := S.filter (fun g => P g ≠ 0 ∧ ∃ t ∈ Icc a b, eval t (P g) = 0) with hT
    have hTne : T.Nonempty := ⟨g, by
      rw [hT, Finset.mem_filter]
      exact ⟨hgS, hg0, t, ht, hgt⟩⟩
    obtain ⟨m, hmT, hmin⟩ := T.exists_min_image (fun g => (P g).natDegree) hTne
    rw [hT, Finset.mem_filter] at hmT
    obtain ⟨hmS, hm0, s, hs, hms⟩ := hmT
    have hdeg : 0 < (P m).natDegree := by
      by_contra h0
      rw [not_lt, Nat.le_zero] at h0
      have hC := eq_C_of_natDegree_eq_zero h0
      rw [hC, eval_C] at hms
      apply hm0
      rw [hC, hms, C_0]
    obtain ⟨m', hm'S, hm'⟩ := hS m hmS hdeg
    have hm'0 : P m' ≠ 0 := by
      rw [hm']
      exact derivative_ne_zero_of_natDegree_pos hdeg
    have hm'deg : (P m').natDegree < (P m).natDegree := by
      rw [hm']
      exact natDegree_derivative_lt hdeg.ne'
    have hm'root : ∀ t ∈ Icc a b, eval t (P m') ≠ 0 := by
      intro t ht h
      have hm'T : m' ∈ T := by
        rw [hT, Finset.mem_filter]
        exact ⟨hm'S, hm'0, t, ht, h⟩
      exact absurd (hmin m' hm'T) (not_le.mpr hm'deg)
    have hmono := injOn_eval_of_deriv_ne_zero (p := P m) hab' fun t ht => by
      rw [← hm']
      exact hm'root t (Ioo_subset_Icc_self ht)
    have hsame : SignType.sign (eval a (P m)) = SignType.sign (eval b (P m)) := by
      have := congrFun hab m
      rwa [sgn_apply_of_mem hmS, sgn_apply_of_mem hmS] at this
    have haI : a ∈ Icc a b := left_mem_Icc.mpr hab'.le
    have hbI : b ∈ Icc a b := right_mem_Icc.mpr hab'.le
    rcases hmono with hmono | hmono
    · have h1 : eval a (P m) < eval b (P m) := hmono haI hbI hab'
      have h2 : eval a (P m) ≤ 0 := by
        have := hmono.monotoneOn haI hs hs.1
        simpa [hms] using this
      have h3 : 0 ≤ eval b (P m) := by
        have := hmono.monotoneOn hs hbI hs.2
        simpa [hms] using this
      rcases h2.lt_or_eq with h2 | h2
      · rcases h3.lt_or_eq with h3 | h3
        · rw [sign_neg h2, sign_pos h3] at hsame
          exact absurd hsame (by decide)
        · rw [sign_neg h2, ← h3, sign_zero] at hsame
          exact absurd hsame (by decide)
      · have h3' : 0 < eval b (P m) := by rw [← h2]; exact h1
        rw [h2, sign_zero, sign_pos h3'] at hsame
        exact absurd hsame (by decide)
    · have h1 : eval b (P m) < eval a (P m) := hmono haI hbI hab'
      have h2 : 0 ≤ eval a (P m) := by
        have := hmono.antitoneOn haI hs hs.1
        simpa [hms] using this
      have h3 : eval b (P m) ≤ 0 := by
        have := hmono.antitoneOn hs hbI hs.2
        simpa [hms] using this
      rcases h2.lt_or_eq with h2 | h2
      · rcases h3.lt_or_eq with h3 | h3
        · rw [sign_pos h2, sign_neg h3] at hsame
          exact absurd hsame (by decide)
        · rw [sign_pos h2, h3, sign_zero] at hsame
          exact absurd hsame (by decide)
      · have h3' : eval b (P m) < 0 := by rw [h2]; exact h1
        rw [← h2, sign_zero, sign_neg h3'] at hsame
        exact absurd hsame (by decide)
  -- constant sign on `[a, b]`
  funext g
  by_cases hgS : g ∈ S
  · rw [sgn_apply_of_mem hgS, sgn_apply_of_mem hgS]
    by_cases hg0 : P g = 0
    · simp [hg0]
    · exact sign_eq_of_no_root isPreconnected_Icc (key g hgS hg0) ⟨hac, hcb⟩
        (left_mem_Icc.mpr hab'.le)
  · rw [sgn_apply_of_not_mem hgS, sgn_apply_of_not_mem hgS]

/-! ### The order of the cells -/

theorem Before.occ_left {ε₁ ε₂ : G → SignType} (h : Before S P ε₁ ε₂) : Occ S P ε₁ :=
  let ⟨t₁, _, _, h₁, _⟩ := h
  ⟨t₁, h₁⟩

theorem Before.occ_right {ε₁ ε₂ : G → SignType} (h : Before S P ε₁ ε₂) : Occ S P ε₂ :=
  let ⟨_, t₂, _, _, h₂⟩ := h
  ⟨t₂, h₂⟩

/-- Two occurring vectors are comparable. -/
theorem before_or_before {ε₁ ε₂ : G → SignType} (h₁ : Occ S P ε₁) (h₂ : Occ S P ε₂)
    (hne : ε₁ ≠ ε₂) : Before S P ε₁ ε₂ ∨ Before S P ε₂ ε₁ := by
  obtain ⟨t₁, h₁⟩ := h₁
  obtain ⟨t₂, h₂⟩ := h₂
  rcases lt_trichotomy t₁ t₂ with h | rfl | h
  · exact Or.inl ⟨t₁, t₂, h, h₁, h₂⟩
  · exact absurd (h₁.symm.trans h₂) hne
  · exact Or.inr ⟨t₂, t₁, h, h₂, h₁⟩

/-- Antisymmetry of `Before` (convexity of level sets). -/
theorem Before.antisymm (hS : DerivClosed S P) {ε₁ ε₂ : G → SignType} (h₁ : Before S P ε₁ ε₂)
    (h₂ : Before S P ε₂ ε₁) : ε₁ = ε₂ := by
  obtain ⟨t₁, t₂, ht, h₁₁, h₁₂⟩ := h₁
  obtain ⟨s₁, s₂, hs, h₂₁, h₂₂⟩ := h₂
  -- `sgn t₁ = ε₁ = sgn s₂`, `sgn t₂ = ε₂ = sgn s₁`
  rcases le_or_gt t₁ s₁ with h | h
  · -- t₁ ≤ s₁ < s₂, same value at t₁ and s₂
    have := sgn_eq_of_between hS (h₁₁.trans h₂₂.symm) h hs.le
    rw [h₂₁, h₁₁] at this
    exact this.symm
  · -- s₁ < t₁ < t₂, same value at s₁ and t₂
    have := sgn_eq_of_between hS (h₂₁.trans h₁₂.symm) h.le ht.le
    rw [h₁₁, h₂₁] at this
    exact this

/-- Distinct cells are separated: every point of the left cell lies left of every point of the
right cell. -/
theorem lt_of_before (hS : DerivClosed S P) {ε₁ ε₂ : G → SignType} (h : Before S P ε₁ ε₂)
    (hne : ε₁ ≠ ε₂) {t₁ t₂ : ℝ} (h₁ : sgn S P t₁ = ε₁) (h₂ : sgn S P t₂ = ε₂) : t₁ < t₂ := by
  by_contra hle
  rw [not_lt] at hle
  rcases hle.lt_or_eq with hlt | heq
  · exact hne (h.antisymm hS ⟨t₂, t₁, hlt, h₂, h₁⟩)
  · exact hne (h₁.symm.trans (heq ▸ h₂))

/-- Transitivity of `Before` across distinct cells. -/
theorem Before.trans (hS : DerivClosed S P) {ε₁ ε₂ ε₃ : G → SignType} (h₁ : Before S P ε₁ ε₂)
    (h₂ : Before S P ε₂ ε₃) (hne : ε₁ ≠ ε₂) : Before S P ε₁ ε₃ := by
  obtain ⟨t₁, t₂, ht, h₁₁, h₁₂⟩ := h₁
  obtain ⟨s₂, s₃, hs, h₂₂, h₂₃⟩ := h₂
  have : t₁ < s₃ := by
    have h1 : t₁ < s₂ := lt_of_before hS ⟨t₁, t₂, ht, h₁₁, h₁₂⟩ hne h₁₁ h₂₂
    exact h1.trans hs
  exact ⟨t₁, s₃, this, h₁₁, h₂₃⟩

/-- A cell is a point cell exactly when `Before ε ε` fails. -/
theorem not_before_self_iff {ε : G → SignType} :
    ¬ Before S P ε ε ↔ ∀ t₁ t₂, sgn S P t₁ = ε → sgn S P t₂ = ε → t₁ = t₂ := by
  constructor
  · intro h t₁ t₂ h₁ h₂
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h ⟨t₁, t₂, hlt, h₁, h₂⟩
    · exact h ⟨t₂, t₁, hlt, h₂, h₁⟩
  · rintro h ⟨t₁, t₂, hlt, h₁, h₂⟩
    exact hlt.ne (h t₁ t₂ h₁ h₂)

/-- On an interval cell the level set is an interval containing two distinct points. -/
theorem Before.self_iff {ε : G → SignType} :
    Before S P ε ε ↔ ∃ t₁ t₂, t₁ < t₂ ∧ sgn S P t₁ = ε ∧ sgn S P t₂ = ε := Iff.rfl

end TS
