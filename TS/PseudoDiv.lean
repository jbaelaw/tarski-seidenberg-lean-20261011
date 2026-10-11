import Mathlib

/-!
# Pseudo-division of polynomials over a domain

For `f g : A[X]` with `g ≠ 0` over a domain `A`, some power of the leading coefficient of `g`
times `f` is `q * g + r` with `deg r < deg g`.  Only existence (with some exponent) is needed:
at a root `ξ` of `g` this gives `lc(g)^n f(ξ) = r(ξ)`, which determines the sign of `f(ξ)` from
the sign of `r(ξ)` and of `lc g`.
-/

namespace TS

open Polynomial

variable {A : Type*} [CommRing A] [IsDomain A]

theorem exists_pseudoDiv_aux (g : A[X]) (hg : g ≠ 0) (d : ℕ) :
    ∀ f : A[X], f.natDegree = d →
      ∃ (n : ℕ) (q r : A[X]), C g.leadingCoeff ^ n * f = q * g + r ∧ r.degree < g.degree := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro f hfd
  by_cases hfg : f.degree < g.degree
  · exact ⟨0, 0, f, by simp, hfg⟩
  · rw [not_lt] at hfg
    have hf0 : f ≠ 0 := by
      rintro rfl
      rw [degree_zero, le_bot_iff, degree_eq_bot] at hfg
      exact hg hfg
    have ha0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg
    have hlf0 : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
    have hdeg_le : g.natDegree ≤ f.natDegree := natDegree_le_natDegree hfg
    set f₁ := C g.leadingCoeff * f - C f.leadingCoeff * X ^ (f.natDegree - g.natDegree) * g
      with hf₁
    have h1 : (C g.leadingCoeff * f).degree = f.degree := degree_C_mul ha0
    have h2 : (C f.leadingCoeff * X ^ (f.natDegree - g.natDegree) * g).degree = f.degree := by
      rw [degree_mul, degree_C_mul_X_pow _ hlf0, degree_eq_natDegree hg, degree_eq_natDegree hf0,
        ← Nat.cast_add, Nat.sub_add_cancel hdeg_le]
    have h3 : (C g.leadingCoeff * f).leadingCoeff =
        (C f.leadingCoeff * X ^ (f.natDegree - g.natDegree) * g).leadingCoeff := by
      simp only [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_pow, mul_one]
      ring
    have hCf0 : C g.leadingCoeff * f ≠ 0 := by
      intro h
      rw [h, degree_zero] at h1
      exact hf0 (degree_eq_bot.mp h1.symm)
    have hf₁deg : f₁.degree < f.degree := by
      rw [← h1]
      exact degree_sub_lt_left (h1.trans h2.symm) hCf0 h3
    by_cases hf₁0 : f₁ = 0
    · refine ⟨1, C f.leadingCoeff * X ^ (f.natDegree - g.natDegree), 0, ?_, ?_⟩
      · rw [pow_one, add_zero]
        exact sub_eq_zero.mp hf₁0
      · rw [degree_zero]
        exact bot_lt_iff_ne_bot.mpr (degree_eq_bot.not.mpr hg)
    · have hlt : f₁.natDegree < d := by
        rw [← hfd]
        exact natDegree_lt_natDegree hf₁0 hf₁deg
      obtain ⟨n₁, q₁, r₁, hq, hr⟩ := ih f₁.natDegree hlt f₁ rfl
      refine ⟨n₁ + 1, q₁ + C g.leadingCoeff ^ n₁ * (C f.leadingCoeff *
        X ^ (f.natDegree - g.natDegree)), r₁, ?_, hr⟩
      rw [hf₁] at hq
      linear_combination hq

/-- Pseudo-division: `C (lc g) ^ n * f = q * g + r` with `deg r < deg g`. -/
theorem exists_pseudoDiv (f g : A[X]) (hg : g ≠ 0) :
    ∃ (n : ℕ) (q r : A[X]), C g.leadingCoeff ^ n * f = q * g + r ∧ r.degree < g.degree :=
  exists_pseudoDiv_aux g hg f.natDegree f rfl

open Classical in
/-- The pseudo-remainder (a choice). -/
noncomputable def prem (f g : A[X]) : A[X] :=
  if hg : g = 0 then 0 else Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_pseudoDiv f g hg)))

open Classical in
/-- The exponent of the pseudo-division. -/
noncomputable def premExp (f g : A[X]) : ℕ :=
  if hg : g = 0 then 0 else Classical.choose (exists_pseudoDiv f g hg)

theorem prem_spec (f g : A[X]) (hg : g ≠ 0) :
    ∃ q : A[X], C g.leadingCoeff ^ premExp f g * f = q * g + prem f g ∧
      (prem f g).degree < g.degree := by
  unfold prem premExp
  simp only [hg, ↓reduceDIte]
  obtain ⟨hq, hr⟩ := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_pseudoDiv f g hg)))
  exact ⟨_, hq, hr⟩

theorem natDegree_prem_lt (f g : A[X]) (hg : g ≠ 0) (hg1 : 0 < g.natDegree) :
    (prem f g).natDegree < g.natDegree := by
  obtain ⟨-, -, hr⟩ := prem_spec f g hg
  by_cases h0 : prem f g = 0
  · rw [h0, natDegree_zero]
    exact hg1
  · exact natDegree_lt_natDegree h0 hr

end TS
