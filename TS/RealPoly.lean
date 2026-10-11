import Mathlib

/-!
# Elementary facts about real univariate polynomials

Sign constancy between roots (intermediate value theorem), strict monotonicity from the sign of
the derivative, Rolle's theorem, and the signs at `±∞`.
-/

namespace TS

open Polynomial Set Filter Topology

/-- A polynomial without roots on an interval has constant sign there. -/
theorem sign_eq_of_no_root {p : ℝ[X]} {I : Set ℝ} (hI : IsPreconnected I)
    (h : ∀ t ∈ I, eval t p ≠ 0) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    SignType.sign (eval s p) = SignType.sign (eval t p) := by
  have hcont : ContinuousOn (fun t => eval t p) I := p.continuous.continuousOn
  have hs0 := h s hs
  have ht0 := h t ht
  rcases lt_or_gt_of_ne hs0 with hs' | hs' <;> rcases lt_or_gt_of_ne ht0 with ht' | ht'
  · rw [sign_neg hs', sign_neg ht']
  · exfalso
    obtain ⟨c, hc, hc0⟩ := hI.intermediate_value hs ht hcont ⟨hs'.le, ht'.le⟩
    exact h c hc hc0
  · exfalso
    obtain ⟨c, hc, hc0⟩ := hI.intermediate_value ht hs hcont ⟨ht'.le, hs'.le⟩
    exact h c hc hc0
  · rw [sign_pos hs', sign_pos ht']

/-- Strict monotonicity on `[a, b]` from a positive derivative on `(a, b)`. -/
theorem strictMonoOn_eval_of_deriv_pos {p : ℝ[X]} {a b : ℝ}
    (h : ∀ t ∈ Ioo a b, 0 < eval t (derivative p)) :
    StrictMonoOn (fun t => eval t p) (Icc a b) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) p.continuous.continuousOn fun t ht => ?_
  rw [interior_Icc] at ht
  rw [Polynomial.deriv]
  exact h t ht

theorem strictAntiOn_eval_of_deriv_neg {p : ℝ[X]} {a b : ℝ}
    (h : ∀ t ∈ Ioo a b, eval t (derivative p) < 0) :
    StrictAntiOn (fun t => eval t p) (Icc a b) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc a b) p.continuous.continuousOn fun t ht => ?_
  rw [interior_Icc] at ht
  rw [Polynomial.deriv]
  exact h t ht

/-- If the derivative has no root on `(a, b)`, `p` is injective on `[a, b]`; in particular it has
at most one root there and its values at distinct points of `[a, b]` are distinct. -/
theorem injOn_eval_of_deriv_ne_zero {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : ∀ t ∈ Ioo a b, eval t (derivative p) ≠ 0) :
    StrictMonoOn (fun t => eval t p) (Icc a b) ∨ StrictAntiOn (fun t => eval t p) (Icc a b) := by
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  rcases lt_or_gt_of_ne (h _ hmid) with hneg | hpos
  · right
    refine strictAntiOn_eval_of_deriv_neg fun t ht => ?_
    have := sign_eq_of_no_root isPreconnected_Ioo h ht hmid
    rw [sign_neg hneg] at this
    exact sign_eq_neg_one_iff.mp this
  · left
    refine strictMonoOn_eval_of_deriv_pos fun t ht => ?_
    have := sign_eq_of_no_root isPreconnected_Ioo h ht hmid
    rw [sign_pos hpos] at this
    exact sign_eq_one_iff.mp this

/-- Rolle's theorem for polynomials. -/
theorem exists_root_derivative {p : ℝ[X]} {a b : ℝ} (hab : a < b) (h : eval a p = eval b p) :
    ∃ c ∈ Ioo a b, eval c (derivative p) = 0 := by
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_zero hab p.continuous.continuousOn h
  refine ⟨c, hc, ?_⟩
  rw [← Polynomial.deriv]
  exact hc'

/-- The derivative of a real polynomial of positive degree is nonzero and of smaller degree. -/
theorem derivative_ne_zero_of_natDegree_pos {p : ℝ[X]} (hp : 0 < p.natDegree) :
    derivative p ≠ 0 := by
  intro h
  have := leadingCoeff_derivative p
  rw [h, leadingCoeff_zero] at this
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hp)
  have hd : (p.natDegree : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  exact mul_ne_zero hlc hd this.symm

/-- Sign at `+∞`. -/
theorem eventually_sign_atTop (p : ℝ[X]) (hp : 0 < p.natDegree) :
    ∀ᶠ t in atTop, SignType.sign (eval t p) = SignType.sign p.leadingCoeff := by
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hp
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  rcases lt_or_gt_of_ne hlc with hneg | hpos
  · have := (tendsto_atBot_of_leadingCoeff_nonpos p hdeg hneg.le).eventually_lt_atBot 0
    filter_upwards [this] with t ht
    rw [sign_neg ht, sign_neg hneg]
  · have := (tendsto_atTop_of_leadingCoeff_nonneg p hdeg hpos.le).eventually_gt_atTop 0
    filter_upwards [this] with t ht
    rw [sign_pos ht, sign_pos hpos]

/-- Sign at `-∞`: the sign of `lc p * (-1) ^ deg p`. -/
theorem eventually_sign_atBot (p : ℝ[X]) (hp : 0 < p.natDegree) :
    ∀ᶠ t in atBot, SignType.sign (eval t p) =
      SignType.sign (p.leadingCoeff * (-1) ^ p.natDegree) := by
  set q : ℝ[X] := p.comp (-X) with hq
  have hX : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  have hqdeg : q.natDegree = p.natDegree := by
    rw [hq, natDegree_comp, hX, mul_one]
  have hqlc : q.leadingCoeff = p.leadingCoeff * (-1) ^ p.natDegree := by
    rw [hq, leadingCoeff_comp (by rw [hX]; exact one_ne_zero), leadingCoeff_neg, leadingCoeff_X]
  have hqpos : 0 < q.natDegree := by rw [hqdeg]; exact hp
  have h := eventually_sign_atTop q hqpos
  have h' : ∀ᶠ t in atBot, SignType.sign (eval (-t) q) = SignType.sign q.leadingCoeff :=
    tendsto_neg_atBot_atTop.eventually h
  filter_upwards [h'] with t ht
  rw [hq, eval_comp, eval_neg, eval_X, neg_neg] at ht
  rw [ht, hqlc]

/-- Beyond some point to the right every member of a finite family of nonzero polynomials has its
limiting sign. -/
theorem exists_forall_sign_atTop {G : Type*} (S : Finset G) (P : G → ℝ[X])
    (hS : ∀ g ∈ S, 0 < (P g).natDegree) :
    ∃ t₀, ∀ t, t₀ ≤ t → ∀ g ∈ S, SignType.sign (eval t (P g)) = SignType.sign (P g).leadingCoeff := by
  have : ∀ᶠ t in atTop, ∀ g ∈ S, SignType.sign (eval t (P g)) = SignType.sign (P g).leadingCoeff := by
    rw [Filter.eventually_all_finset]
    intro g hg
    exact eventually_sign_atTop (P g) (hS g hg)
  exact Filter.eventually_atTop.mp this

theorem exists_forall_sign_atBot {G : Type*} (S : Finset G) (P : G → ℝ[X])
    (hS : ∀ g ∈ S, 0 < (P g).natDegree) :
    ∃ t₀, ∀ t, t ≤ t₀ → ∀ g ∈ S, SignType.sign (eval t (P g)) =
      SignType.sign ((P g).leadingCoeff * (-1) ^ (P g).natDegree) := by
  have : ∀ᶠ t in atBot, ∀ g ∈ S, SignType.sign (eval t (P g)) =
      SignType.sign ((P g).leadingCoeff * (-1) ^ (P g).natDegree) := by
    rw [Filter.eventually_all_finset]
    intro g hg
    exact eventually_sign_atBot (P g) (hS g hg)
  exact Filter.eventually_atBot.mp this

/-- A nonzero polynomial vanishing on a nontrivial interval is impossible. -/
theorem ne_zero_on_Ioo {p : ℝ[X]} (hp : p ≠ 0) {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, eval t p ≠ 0 := by
  by_contra h
  push Not at h
  apply hp
  apply eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono (fun t ht => h t ht) (Set.Ioo_infinite hab)

/-- Near a point where `p` does not vanish, the sign of `p` is constant. -/
theorem eventually_sign_eq_nhds {p : ℝ[X]} {a : ℝ} (ha : eval a p ≠ 0) :
    ∀ᶠ t in 𝓝 a, SignType.sign (eval t p) = SignType.sign (eval a p) := by
  have hcont : ContinuousAt (fun t => eval t p) a := p.continuous.continuousAt
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · filter_upwards [hcont.eventually (gt_mem_nhds hneg)] with t ht
    rw [sign_neg ht, sign_neg hneg]
  · filter_upwards [hcont.eventually (lt_mem_nhds hpos)] with t ht
    rw [sign_pos ht, sign_pos hpos]

end TS
