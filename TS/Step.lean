import TS.Neighbors

/-!
# The Hörmander step: adding a polynomial of maximal degree

Let `S` be a derivative-closed family of nonzero polynomials, `f ∈ S` of maximal degree `≥ 1`,
`S' = S.erase f`.  The cells of `S` are determined by the cells of `S'` and finite data: the
derivative index `f'`, pseudo-division data of `f` by the members of `S'` (exponents and the
indices of the remainders), the signs of the leading coefficients and the degree of `f`:

* at a point cell `π` of `S'` the sign of `f` is `ptSign` (from the remainder);
* on an interval cell `ε'` of `S'`, `f` is strictly monotone and its signs are `fsigns sL sR`,
  where `sL`/`sR` are the signs of `f` at the adjacent point cells, or the limiting signs at
  `∓∞` when there is none;
* `Occ` and `Before` for `S` are expressed through `Occ`, `Before` for `S'` (`occ_iff`,
  `before_iff`).
-/

namespace TS

open Polynomial Set

variable {G : Type*} [DecidableEq G]

/-- The combinatorial data of one step. -/
structure StepData (G : Type*) where
  f : G
  f' : G
  n : G → ℕ
  rep : G → Option G
  lcs : G → SignType
  df : ℕ

/-- Hypotheses linking the data to the actual family. -/
structure StepHyp (S : Finset G) (P : G → ℝ[X]) (d : StepData G) : Prop where
  hf : d.f ∈ S
  hnz : NonzeroOn S P
  hS : DerivClosed S P
  hmax : ∀ g ∈ S, (P g).natDegree ≤ (P d.f).natDegree
  hdeg : 0 < (P d.f).natDegree
  hf' : d.f' ∈ S.erase d.f
  hf'eq : P d.f' = derivative (P d.f)
  hrem : ∀ h ∈ S.erase d.f, ∃ q : ℝ[X],
    C (P h).leadingCoeff ^ d.n h * P d.f = q * P h + (d.rep h).elim 0 P
  hrep : ∀ h ∈ S.erase d.f, ∀ r, d.rep h = some r → r ∈ S.erase d.f
  hlcs : ∀ g ∈ S, d.lcs g = SignType.sign (P g).leadingCoeff
  hdf : d.df = (P d.f).natDegree

/-- The level set (cell) of the sign vector `ε'`. -/
def cell (S' : Finset G) (P : G → ℝ[X]) (ε' : G → SignType) : Set ℝ := {t | sgn S' P t = ε'}

/-- The set of signs taken by a strictly monotone function on an open interval whose endpoint
values (or limits) have signs `sL`, `sR`. -/
def fsigns (sL sR : SignType) : Set SignType :=
  if sL = sR then {sL} else if sL = 0 then {sR} else if sR = 0 then {sL} else {sL, 0, sR}

theorem mem_fsigns_left {sL sR : SignType} (h : sL ≠ 0) : sL ∈ fsigns sL sR := by
  unfold fsigns
  split_ifs <;> simp_all

theorem mem_fsigns_right {sL sR : SignType} (h : sR ≠ 0) : sR ∈ fsigns sL sR := by
  unfold fsigns
  split_ifs <;> simp_all

open Classical in
/-- The sign of `f` at a point cell `π` of `S'`, read off from the remainder of `f` by a member
vanishing there. -/
noncomputable def ptSign (S' : Finset G) (d : StepData G) (π : G → SignType) : SignType :=
  if h : ∃ g ∈ S', π g = 0 then d.lcs h.choose ^ d.n h.choose * (d.rep h.choose).elim 0 π else 0

/-! ### Signs of a strictly monotone function on an open interval -/

section Signs

variable {φ : ℝ → ℝ}

theorem signs_Ioo_of_strictMonoOn (hφ : Continuous φ) {α β : ℝ} (hαβ : α < β)
    (hmono : StrictMonoOn φ (Icc α β)) :
    {s | ∃ t ∈ Ioo α β, SignType.sign (φ t) = s} =
      fsigns (SignType.sign (φ α)) (SignType.sign (φ β)) := by
  have hαI : α ∈ Icc α β := left_mem_Icc.mpr hαβ.le
  have hβI : β ∈ Icc α β := right_mem_Icc.mpr hαβ.le
  have hab : φ α < φ β := hmono hαI hβI hαβ
  have hmid : (α + β) / 2 ∈ Ioo α β := ⟨by linarith, by linarith⟩
  have hIVT : Ioo (φ α) (φ β) ⊆ φ '' Ioo α β := intermediate_value_Ioo hαβ.le hφ.continuousOn
  have hval : ∀ t ∈ Ioo α β, φ α < φ t ∧ φ t < φ β := fun t ht =>
    ⟨hmono hαI (Ioo_subset_Icc_self ht) ht.1, hmono (Ioo_subset_Icc_self ht) hβI ht.2⟩
  ext s
  simp only [Set.mem_ofPred_eq]
  unfold fsigns
  split_ifs with e1 e2 e3
  · -- equal (nonzero) signs at both ends
    have hne : φ α ≠ 0 := by
      intro h0
      rw [h0, sign_zero] at e1
      have : 0 < φ β := by rw [← h0]; exact hab
      rw [sign_pos this] at e1
      exact absurd e1 (by decide)
    simp only [Set.mem_singleton_iff]
    rcases lt_or_gt_of_ne hne with hneg | hpos
    · have hβneg : φ β < 0 := by
        by_contra h
        rw [not_lt] at h
        rw [sign_neg hneg] at e1
        rcases h.lt_or_eq with h | h
        · rw [sign_pos h] at e1
          exact absurd e1 (by decide)
        · rw [← h, sign_zero] at e1
          exact absurd e1 (by decide)
      constructor
      · rintro ⟨t, ht, rfl⟩
        rw [sign_neg ((hval t ht).2.trans hβneg), sign_neg hneg]
      · rintro rfl
        exact ⟨_, hmid, by rw [sign_neg ((hval _ hmid).2.trans hβneg), sign_neg hneg]⟩
    · constructor
      · rintro ⟨t, ht, rfl⟩
        rw [sign_pos (hpos.trans (hval t ht).1), sign_pos hpos]
      · rintro rfl
        exact ⟨_, hmid, by rw [sign_pos (hpos.trans (hval _ hmid).1), sign_pos hpos]⟩
  · -- `φ α = 0`
    have h0 : φ α = 0 := sign_eq_zero_iff.mp e2
    have hβpos : 0 < φ β := by rw [← h0]; exact hab
    simp only [Set.mem_singleton_iff, sign_pos hβpos]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [sign_pos (by rw [← h0]; exact (hval t ht).1)]
    · rintro rfl
      exact ⟨_, hmid, by rw [sign_pos (by rw [← h0]; exact (hval _ hmid).1)]⟩
  · -- `φ β = 0`
    have h0 : φ β = 0 := sign_eq_zero_iff.mp e3
    have hαneg : φ α < 0 := by rw [← h0]; exact hab
    simp only [Set.mem_singleton_iff, sign_neg hαneg]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [sign_neg (by rw [← h0]; exact (hval t ht).2)]
    · rintro rfl
      exact ⟨_, hmid, by rw [sign_neg (by rw [← h0]; exact (hval _ hmid).2)]⟩
  · -- `φ α < 0 < φ β`
    have hαneg : φ α < 0 := by
      rcases lt_trichotomy (φ α) 0 with h | h | h
      · exact h
      · exact absurd (by rw [h, sign_zero]) e2
      · exfalso
        have : 0 < φ β := h.trans hab
        rw [sign_pos h, sign_pos this] at e1
        exact e1 rfl
    have hβpos : 0 < φ β := by
      rcases lt_trichotomy (φ β) 0 with h | h | h
      · exfalso
        rw [sign_neg hαneg, sign_neg h] at e1
        exact e1 rfl
      · exact absurd (by rw [h, sign_zero]) e3
      · exact h
    rw [sign_neg hαneg, sign_pos hβpos]
    constructor
    · intro _
      cases s <;> simp
    · intro _
      rcases s with _ | _ | _
      · obtain ⟨t, ht, hty⟩ := hIVT ⟨hαneg, hβpos⟩
        exact ⟨t, ht, by rw [hty, sign_zero]; rfl⟩
      · obtain ⟨t, ht, hty⟩ := hIVT (show φ α / 2 ∈ Ioo (φ α) (φ β) from ⟨by linarith, by linarith⟩)
        exact ⟨t, ht, by rw [hty]; exact sign_neg (by linarith)⟩
      · obtain ⟨t, ht, hty⟩ := hIVT (show φ β / 2 ∈ Ioo (φ α) (φ β) from ⟨by linarith, by linarith⟩)
        exact ⟨t, ht, by rw [hty]; exact sign_pos (by linarith)⟩

theorem signs_Ioo_of_strictAntiOn (hφ : Continuous φ) {α β : ℝ} (hαβ : α < β)
    (hanti : StrictAntiOn φ (Icc α β)) :
    {s | ∃ t ∈ Ioo α β, SignType.sign (φ t) = s} =
      fsigns (SignType.sign (φ α)) (SignType.sign (φ β)) := by
  have hmono : StrictMonoOn (fun t => -φ t) (Icc α β) := fun a ha b hb hab =>
    neg_lt_neg (hanti ha hb hab)
  have h := signs_Ioo_of_strictMonoOn (φ := fun t => -φ t) hφ.neg hαβ hmono
  have hneg : ∀ x : ℝ, SignType.sign (-x) = -SignType.sign x := fun x => Left.sign_neg x
  simp only [hneg] at h
  -- transport along negation
  ext s
  have := congrArg (fun A : Set SignType => -s ∈ A) h
  simp only [Set.mem_ofPred_eq, eq_iff_iff] at this
  have h1 : (∃ t ∈ Ioo α β, -SignType.sign (φ t) = -s) ↔ ∃ t ∈ Ioo α β, SignType.sign (φ t) = s := by
    simp only [neg_inj]
  rw [h1] at this
  rw [Set.mem_ofPred_eq, this]
  unfold fsigns
  cases SignType.sign (φ α) <;> cases SignType.sign (φ β) <;> cases s <;> simp

/-- Combined statement for a function with nonvanishing derivative. -/
theorem signs_Ioo_of_injOn (hφ : Continuous φ) {α β : ℝ} (hαβ : α < β)
    (h : StrictMonoOn φ (Icc α β) ∨ StrictAntiOn φ (Icc α β)) :
    {s | ∃ t ∈ Ioo α β, SignType.sign (φ t) = s} =
      fsigns (SignType.sign (φ α)) (SignType.sign (φ β)) := by
  rcases h with h | h
  · exact signs_Ioo_of_strictMonoOn hφ hαβ h
  · exact signs_Ioo_of_strictAntiOn hφ hαβ h

end Signs

variable {S : Finset G} {P : G → ℝ[X]} {d : StepData G}

namespace StepHyp

variable (H : StepHyp S P d)
include H

theorem hS' : DerivClosed (S.erase d.f) P := H.hS.erase H.hmax

theorem hnz' : NonzeroOn (S.erase d.f) P := fun g hg => H.hnz g (Finset.mem_of_mem_erase hg)

theorem f_ne_zero : P d.f ≠ 0 := H.hnz d.f H.hf

/-- The sign vector of `S` is that of `S'` updated at `f`. -/
theorem sgn_eq (t : ℝ) : sgn S P t =
    Function.update (sgn (S.erase d.f) P t) d.f (SignType.sign (eval t (P d.f))) := by
  funext g
  by_cases hg : g = d.f
  · subst hg
    rw [Function.update_self, sgn_apply_of_mem H.hf]
  · rw [Function.update_of_ne hg]
    by_cases hgS : g ∈ S
    · rw [sgn_apply_of_mem hgS, sgn_apply_of_mem (Finset.mem_erase.mpr ⟨hg, hgS⟩)]
    · rw [sgn_apply_of_not_mem hgS,
        sgn_apply_of_not_mem (fun h => hgS (Finset.mem_of_mem_erase h))]

omit H in
/-- The sign vector of `S'` is that of `S` with the `f`-coordinate erased. -/
theorem sgn_erase (t : ℝ) : sgn (S.erase d.f) P t = Function.update (sgn S P t) d.f 0 := by
  funext g
  by_cases hg : g = d.f
  · subst hg
    rw [Function.update_self, sgn_apply_of_not_mem (Finset.notMem_erase _ _)]
  · rw [Function.update_of_ne hg]
    by_cases hgS : g ∈ S
    · rw [sgn_apply_of_mem hgS, sgn_apply_of_mem (Finset.mem_erase.mpr ⟨hg, hgS⟩)]
    · rw [sgn_apply_of_not_mem hgS,
        sgn_apply_of_not_mem (fun h => hgS (Finset.mem_of_mem_erase h))]

theorem sgn_f (t : ℝ) : sgn S P t d.f = SignType.sign (eval t (P d.f)) := sgn_apply_of_mem H.hf

/-- **Point cells**: the sign of `f` at a point cell of `S'` is `ptSign`. -/
theorem ptSign_eq {π : G → SignType} (hπ : IsPt (S.erase d.f) P π) {α : ℝ}
    (hα : sgn (S.erase d.f) P α = π) : SignType.sign (eval α (P d.f)) = ptSign (S.erase d.f) d π := by
  have hex : ∃ g ∈ S.erase d.f, π g = 0 := hπ.exists_zero hα
  have hpt : ptSign (S.erase d.f) d π =
      d.lcs hex.choose ^ d.n hex.choose * (d.rep hex.choose).elim 0 π := by
    unfold ptSign
    split_ifs
    rfl
  rw [hpt]
  obtain ⟨hgS, hgπ⟩ := hex.choose_spec
  generalize hgdef : hex.choose = g at hgS hgπ ⊢
  have hPg : eval α (P g) = 0 := by
    have := congrFun hα g
    rw [sgn_apply_of_mem hgS, hgπ] at this
    exact sign_eq_zero_iff.mp this
  obtain ⟨q, hq⟩ := H.hrem g hgS
  have hev := congrArg (eval α) hq
  simp only [eval_mul, eval_pow, eval_C, eval_add, hPg, mul_zero, zero_add] at hev
  have hs := congrArg SignType.sign hev
  rw [sign_mul, sign_pow] at hs
  have hR : SignType.sign (eval α ((d.rep g).elim 0 P)) = (d.rep g).elim 0 π := by
    cases hr : d.rep g with
    | none => simp
    | some r =>
      simp only [Option.elim]
      have hr' := H.hrep g hgS r hr
      rw [← hα, sgn_apply_of_mem hr']
  rw [hR] at hs
  have hlc : SignType.sign (P g).leadingCoeff ≠ 0 := by
    rw [Ne, sign_eq_zero_iff]
    exact leadingCoeff_ne_zero.mpr (H.hnz' g hgS)
  have key : ∀ s : SignType, s ≠ 0 → s * s = 1 := by decide
  have hσσ : SignType.sign (P g).leadingCoeff ^ d.n g * SignType.sign (P g).leadingCoeff ^ d.n g = 1 := by
    rw [← mul_pow, key _ hlc, one_pow]
  rw [H.hlcs g (Finset.mem_of_mem_erase hgS), ← hs, ← mul_assoc, hσσ, one_mul]

/-! ### Interval cells -/

theorem deriv_sign {ε' : G → SignType} {t : ℝ} (ht : sgn (S.erase d.f) P t = ε') :
    SignType.sign (eval t (derivative (P d.f))) = ε' d.f' := by
  rw [← H.hf'eq, ← sgn_apply_of_mem H.hf', ht]

theorem f'_ne_zero {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') : ε' d.f' ≠ 0 :=
  before_self_ne_zero H.hS' H.hnz' hε' H.hf'

/-- `f` is injective (strictly monotone or antitone) on the closed hull of two points of a cell. -/
theorem injOn_cell {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') {a b : ℝ} (hab : a < b)
    (hsub : ∀ s ∈ Ioo a b, sgn (S.erase d.f) P s = ε') :
    StrictMonoOn (fun t => eval t (P d.f)) (Icc a b) ∨
      StrictAntiOn (fun t => eval t (P d.f)) (Icc a b) := by
  refine injOn_eval_of_deriv_ne_zero hab fun s hs h0 => ?_
  have := H.deriv_sign (hsub s hs)
  rw [h0, sign_zero] at this
  exact H.f'_ne_zero hε' this.symm

/-- In the increasing case `f` is strictly monotone on the cell. -/
theorem strictMonoOn_cell {ε' : G → SignType}
    (hpos : ε' d.f' = 1) : StrictMonoOn (fun t => eval t (P d.f)) (cell (S.erase d.f) P ε') := by
  intro t₁ h₁ t₂ h₂ hlt
  have hIcc : ∀ s ∈ Icc t₁ t₂, sgn (S.erase d.f) P s = ε' := fun s hs =>
    sgn_eq_of_mem_Icc H.hS' h₁ h₂ hs
  have := strictMonoOn_eval_of_deriv_pos (p := P d.f) (a := t₁) (b := t₂) fun s hs => by
    have := H.deriv_sign (hIcc s (Ioo_subset_Icc_self hs))
    rw [hpos] at this
    exact sign_eq_one_iff.mp this
  exact this (left_mem_Icc.mpr hlt.le) (right_mem_Icc.mpr hlt.le) hlt

theorem strictAntiOn_cell {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε')
    (hneg : ε' d.f' ≠ 1) : StrictAntiOn (fun t => eval t (P d.f)) (cell (S.erase d.f) P ε') := by
  have hneg' : ε' d.f' = -1 := by
    have := H.f'_ne_zero hε'
    cases h : ε' d.f' <;> simp_all
  intro t₁ h₁ t₂ h₂ hlt
  have hIcc : ∀ s ∈ Icc t₁ t₂, sgn (S.erase d.f) P s = ε' := fun s hs =>
    sgn_eq_of_mem_Icc H.hS' h₁ h₂ hs
  have := strictAntiOn_eval_of_deriv_neg (p := P d.f) (a := t₁) (b := t₂) fun s hs => by
    have := H.deriv_sign (hIcc s (Ioo_subset_Icc_self hs))
    rw [hneg'] at this
    exact sign_eq_neg_one_iff.mp this
  exact this (left_mem_Icc.mpr hlt.le) (right_mem_Icc.mpr hlt.le) hlt

end StepHyp

open Classical in
/-- The sign of `f` at the left end of a cell `ε'`, relative to an abstract order `B`: at the
adjacent point cell, or at `-∞`. -/
noncomputable def leftSignP (B : (G → SignType) → (G → SignType) → Prop) (S' : Finset G)
    (d : StepData G) (ε' : G → SignType) : SignType :=
  if h : ∃ π, AdjP B π ε' then ptSign S' d h.choose else d.lcs d.f * (-1) ^ d.df

open Classical in
/-- The sign of `f` at the right end of a cell `ε'`, relative to an abstract order `B`. -/
noncomputable def rightSignP (B : (G → SignType) → (G → SignType) → Prop) (S' : Finset G)
    (d : StepData G) (ε' : G → SignType) : SignType :=
  if h : ∃ π, AdjRP B ε' π then ptSign S' d h.choose else d.lcs d.f

/-- The sign of `f` at the left end of the cell `ε'`. -/
noncomputable def leftSign (S' : Finset G) (P : G → ℝ[X]) (d : StepData G) (ε' : G → SignType) :
    SignType :=
  leftSignP (Before S' P) S' d ε'

/-- The sign of `f` at the right end of the cell `ε'`. -/
noncomputable def rightSign (S' : Finset G) (P : G → ℝ[X]) (d : StepData G) (ε' : G → SignType) :
    SignType :=
  rightSignP (Before S' P) S' d ε'

theorem leftSign_eq (S' : Finset G) (P : G → ℝ[X]) (d : StepData G) (ε' : G → SignType) :
    leftSign S' P d ε' = leftSignP (Before S' P) S' d ε' := rfl

theorem rightSign_eq (S' : Finset G) (P : G → ℝ[X]) (d : StepData G) (ε' : G → SignType) :
    rightSign S' P d ε' = rightSignP (Before S' P) S' d ε' := rfl

namespace StepHyp

variable (H : StepHyp S P d)
include H

theorem sign_atBot_eq : SignType.sign ((P d.f).leadingCoeff * (-1) ^ (P d.f).natDegree) =
    d.lcs d.f * (-1) ^ d.df := by
  rw [sign_mul, sign_pow, H.hlcs d.f H.hf, H.hdf]
  congr 1
  rw [show (SignType.sign (-1 : ℝ)) = -1 from sign_neg (by norm_num)]

/-- The left endpoint data of an interval cell containing `t`: either an adjacent point cell at
`α < t` with `(α, t] ⊆ cell` and `sign f(α) = leftSign`, or the cell extends to `-∞` with the
`-∞`-sign equal to `leftSign`. -/
theorem left_data {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') {t : ℝ}
    (ht : sgn (S.erase d.f) P t = ε') :
    (∃ α, α < t ∧ (∀ s, α < s → s ≤ t → sgn (S.erase d.f) P s = ε') ∧
      (∀ s, sgn (S.erase d.f) P s = ε' → α < s) ∧
      SignType.sign (eval α (P d.f)) = leftSign (S.erase d.f) P d ε') ∨
    ((∀ s, s ≤ t → sgn (S.erase d.f) P s = ε') ∧
      leftSign (S.erase d.f) P d ε' = SignType.sign ((P d.f).leadingCoeff * (-1) ^ (P d.f).natDegree)) := by
  rcases left_neighbor H.hS' H.hnz' hε' ht with hall | ⟨α, π, hαt, hα, hpt, hadj, hconst, huniq⟩
  · right
    refine ⟨hall, ?_⟩
    unfold leftSign leftSignP
    split_ifs with h
    · exact absurd h.choose_spec (not_adj_of_unbounded_below H.hS' ht hall)
    · exact H.sign_atBot_eq.symm
  · left
    refine ⟨α, hαt, hconst, fun s hs => lt_of_before H.hS' hadj.1 hadj.2.1 hα hs, ?_⟩
    unfold leftSign leftSignP
    split_ifs with h
    · have hπ : h.choose = π := Adj.unique h.choose_spec hadj
      rw [hπ]
      exact H.ptSign_eq hpt hα
    · exact absurd ⟨π, hadj⟩ h

theorem right_data {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') {t : ℝ}
    (ht : sgn (S.erase d.f) P t = ε') :
    (∃ β, t < β ∧ (∀ s, t ≤ s → s < β → sgn (S.erase d.f) P s = ε') ∧
      (∀ s, sgn (S.erase d.f) P s = ε' → s < β) ∧
      SignType.sign (eval β (P d.f)) = rightSign (S.erase d.f) P d ε') ∨
    ((∀ s, t ≤ s → sgn (S.erase d.f) P s = ε') ∧
      rightSign (S.erase d.f) P d ε' = SignType.sign (P d.f).leadingCoeff) := by
  rcases right_neighbor H.hS' H.hnz' hε' ht with hall | ⟨β, π, htβ, hβ, hpt, hadj, hconst, huniq⟩
  · right
    refine ⟨hall, ?_⟩
    unfold rightSign rightSignP
    split_ifs with h
    · exact absurd h.choose_spec (not_adjR_of_unbounded_above H.hS' ht hall)
    · exact H.hlcs d.f H.hf
  · left
    refine ⟨β, htβ, hconst, fun s hs => lt_of_before H.hS' hadj.1 hadj.2.1 hs hβ, ?_⟩
    unfold rightSign rightSignP
    split_ifs with h
    · have hπ : h.choose = π := AdjR.unique h.choose_spec hadj
      rw [hπ]
      exact H.ptSign_eq hpt hβ
    · exact absurd ⟨π, hadj⟩ h

/-- The signs of `f` on an open interval `(a, b)` inside a cell, with `a, b` not necessarily in
the cell: `fsigns (sign f a) (sign f b)`. -/
theorem signs_Ioo {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') {a b : ℝ} (hab : a < b)
    (hsub : ∀ s ∈ Ioo a b, sgn (S.erase d.f) P s = ε') :
    {s | ∃ t ∈ Ioo a b, SignType.sign (eval t (P d.f)) = s} =
      fsigns (SignType.sign (eval a (P d.f))) (SignType.sign (eval b (P d.f))) :=
  signs_Ioo_of_injOn (P d.f).continuous hab (H.injOn_cell hε' hab hsub)

/-- **Interval cells**: the signs of `f` on the cell `ε'` are exactly
`fsigns (leftSign ε') (rightSign ε')`. -/
theorem signs_cell {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') :
    {s | ∃ t ∈ cell (S.erase d.f) P ε', SignType.sign (eval t (P d.f)) = s} =
      fsigns (leftSign (S.erase d.f) P d ε') (rightSign (S.erase d.f) P d ε') := by
  obtain ⟨t, ht⟩ : Occ (S.erase d.f) P ε' := hε'.occ_left
  have hdeg := H.hdeg
  -- tails
  obtain ⟨tL, htL⟩ := Filter.eventually_atBot.mp (eventually_sign_atBot (P d.f) hdeg)
  obtain ⟨tR, htR⟩ := Filter.eventually_atTop.mp (eventually_sign_atTop (P d.f) hdeg)
  rcases H.left_data hε' ht with ⟨α, hαt, hαsub, hαlt, hαsign⟩ | ⟨hLall, hLsign⟩ <;>
    rcases H.right_data hε' ht with ⟨β, htβ, hβsub, hβlt, hβsign⟩ | ⟨hRall, hRsign⟩
  · -- bounded on both sides: cell = Ioo α β
    have hcell : cell (S.erase d.f) P ε' = Ioo α β := by
      ext s
      constructor
      · intro hs
        exact ⟨hαlt s hs, hβlt s hs⟩
      · intro hs
        rcases le_or_gt s t with h | h
        · exact hαsub s hs.1 h
        · exact hβsub s h.le hs.2
    rw [hcell, ← hαsign, ← hβsign]
    exact H.signs_Ioo hε' (hαt.trans htβ) (by rw [← hcell]; exact fun s hs => hs)
  · -- left endpoint `α`, unbounded above: cell = Ioi α
    have hcell : cell (S.erase d.f) P ε' = Ioi α := by
      ext s
      constructor
      · intro hs
        exact hαlt s hs
      · intro hs
        rcases le_or_gt s t with h | h
        · exact hαsub s hs h
        · exact hRall s h.le
    set t₁ := max (t + 1) tR with ht₁
    have ht₁R : tR ≤ t₁ := le_max_right _ _
    have ht₁t : t < t₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hαt₁ : α < t₁ := hαt.trans ht₁t
    have hsub : ∀ s ∈ Ioo α t₁, sgn (S.erase d.f) P s = ε' := fun s hs => by
      have : s ∈ cell (S.erase d.f) P ε' := by rw [hcell]; exact hs.1
      exact this
    have hIoo := H.signs_Ioo hε' hαt₁ hsub
    have hR1 : SignType.sign (eval t₁ (P d.f)) = rightSign (S.erase d.f) P d ε' := by
      rw [hRsign]
      exact htR t₁ ht₁R
    have hRne : rightSign (S.erase d.f) P d ε' ≠ 0 := by
      rw [hRsign, Ne, sign_eq_zero_iff]
      exact leadingCoeff_ne_zero.mpr H.f_ne_zero
    rw [hcell]
    ext s
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases lt_or_ge u t₁ with hlt | hge
      · have : SignType.sign (eval u (P d.f)) ∈ fsigns (SignType.sign (eval α (P d.f)))
            (SignType.sign (eval t₁ (P d.f))) := by
          rw [← hIoo]
          exact ⟨u, ⟨hu, hlt⟩, rfl⟩
        rwa [hαsign, hR1] at this
      · rw [htR u (ht₁R.trans hge), ← hRsign]
        exact mem_fsigns_right hRne
    · intro hs
      rw [← hαsign, ← hR1, ← hIoo] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      exact ⟨u, hu.1, rfl⟩
  · -- unbounded below, right endpoint `β`: cell = Iio β
    have hcell : cell (S.erase d.f) P ε' = Iio β := by
      ext s
      constructor
      · intro hs
        exact hβlt s hs
      · intro hs
        rcases le_or_gt s t with h | h
        · exact hLall s h
        · exact hβsub s h.le hs
    set t₀ := min (t - 1) tL with ht₀
    have ht₀L : t₀ ≤ tL := min_le_right _ _
    have ht₀t : t₀ < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht₀β : t₀ < β := ht₀t.trans htβ
    have hsub : ∀ s ∈ Ioo t₀ β, sgn (S.erase d.f) P s = ε' := fun s hs => by
      have : s ∈ cell (S.erase d.f) P ε' := by rw [hcell]; exact hs.2
      exact this
    have hIoo := H.signs_Ioo hε' ht₀β hsub
    have hL1 : SignType.sign (eval t₀ (P d.f)) = leftSign (S.erase d.f) P d ε' := by
      rw [hLsign]
      exact htL t₀ ht₀L
    have hLne : leftSign (S.erase d.f) P d ε' ≠ 0 := by
      rw [hLsign, Ne, sign_eq_zero_iff]
      refine mul_ne_zero (leadingCoeff_ne_zero.mpr H.f_ne_zero) (pow_ne_zero _ (by norm_num))
    rw [hcell]
    ext s
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases lt_or_ge t₀ u with hlt | hge
      · have : SignType.sign (eval u (P d.f)) ∈ fsigns (SignType.sign (eval t₀ (P d.f)))
            (SignType.sign (eval β (P d.f))) := by
          rw [← hIoo]
          exact ⟨u, ⟨hlt, hu⟩, rfl⟩
        rwa [hL1, hβsign] at this
      · rw [htL u (hge.trans ht₀L), ← hLsign]
        exact mem_fsigns_left hLne
    · intro hs
      rw [← hL1, ← hβsign, ← hIoo] at hs
      obtain ⟨u, hu, rfl⟩ := hs
      exact ⟨u, hu.2, rfl⟩
  · -- unbounded on both sides: cell = univ
    have hcell : cell (S.erase d.f) P ε' = univ := by
      ext s
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      rcases le_or_gt s t with h | h
      · exact hLall s h
      · exact hRall s h.le
    set t₀ := min (t - 1) tL with ht₀
    set t₁ := max (t + 1) tR with ht₁
    have ht₀L : t₀ ≤ tL := min_le_right _ _
    have ht₁R : tR ≤ t₁ := le_max_right _ _
    have ht₀t : t₀ < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht₁t : t < t₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have ht₀₁ : t₀ < t₁ := ht₀t.trans ht₁t
    have hsub : ∀ s ∈ Ioo t₀ t₁, sgn (S.erase d.f) P s = ε' := fun s _ => by
      have : s ∈ cell (S.erase d.f) P ε' := by rw [hcell]; trivial
      exact this
    have hIoo := H.signs_Ioo hε' ht₀₁ hsub
    have hL1 : SignType.sign (eval t₀ (P d.f)) = leftSign (S.erase d.f) P d ε' := by
      rw [hLsign]
      exact htL t₀ ht₀L
    have hR1 : SignType.sign (eval t₁ (P d.f)) = rightSign (S.erase d.f) P d ε' := by
      rw [hRsign]
      exact htR t₁ ht₁R
    have hLne : leftSign (S.erase d.f) P d ε' ≠ 0 := by
      rw [hLsign, Ne, sign_eq_zero_iff]
      exact mul_ne_zero (leadingCoeff_ne_zero.mpr H.f_ne_zero) (pow_ne_zero _ (by norm_num))
    have hRne : rightSign (S.erase d.f) P d ε' ≠ 0 := by
      rw [hRsign, Ne, sign_eq_zero_iff]
      exact leadingCoeff_ne_zero.mpr H.f_ne_zero
    rw [hcell]
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_univ, true_and]
    constructor
    · rintro ⟨u, rfl⟩
      rcases lt_or_ge u t₁ with hlt | hge
      · rcases lt_or_ge t₀ u with hlt' | hge'
        · have : SignType.sign (eval u (P d.f)) ∈ fsigns (SignType.sign (eval t₀ (P d.f)))
              (SignType.sign (eval t₁ (P d.f))) := by
            rw [← hIoo]
            exact ⟨u, ⟨hlt', hlt⟩, rfl⟩
          rwa [hL1, hR1] at this
        · rw [htL u (hge'.trans ht₀L), ← hLsign]
          exact mem_fsigns_left hLne
      · rw [htR u (ht₁R.trans hge), ← hRsign]
        exact mem_fsigns_right hRne
    · intro hs
      rw [← hL1, ← hR1, ← hIoo] at hs
      obtain ⟨u, -, rfl⟩ := hs
      exact ⟨u, rfl⟩

/-- Every point of a cell has a left neighborhood inside the cell. -/
theorem exists_Ioc_subset_cell {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') {t : ℝ}
    (ht : sgn (S.erase d.f) P t = ε') :
    ∃ a, a < t ∧ ∀ s, a < s → s ≤ t → sgn (S.erase d.f) P s = ε' := by
  rcases H.left_data hε' ht with ⟨α, hαt, hαsub, -, -⟩ | ⟨hLall, -⟩
  · exact ⟨α, hαt, hαsub⟩
  · exact ⟨t - 1, by linarith, fun s _ hs => hLall s hs⟩

/-- Two points of the cell with the same nonzero `f`-sign, in either order. -/
theorem exists_two_of_sign {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') {σ : SignType}
    (hσ : σ ≠ 0) (hocc : σ ∈ fsigns (leftSign (S.erase d.f) P d ε') (rightSign (S.erase d.f) P d ε')) :
    ∃ t₁ t₂, t₁ < t₂ ∧ sgn (S.erase d.f) P t₁ = ε' ∧ sgn (S.erase d.f) P t₂ = ε' ∧
      SignType.sign (eval t₁ (P d.f)) = σ ∧ SignType.sign (eval t₂ (P d.f)) = σ := by
  rw [← H.signs_cell hε'] at hocc
  obtain ⟨t, ht, hts⟩ := hocc
  have hne : eval t (P d.f) ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at hts
    exact hσ hts.symm
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_sign_eq_nhds hne)
  obtain ⟨a, hat, hasub⟩ := H.exists_Ioc_subset_cell hε' ht
  set t₁ := max a (t - δ / 2) + (t - max a (t - δ / 2)) / 2 with ht₁
  have hmax_lt : max a (t - δ / 2) < t := max_lt hat (by linarith)
  have ht₁lt : t₁ < t := by rw [ht₁]; linarith
  have ht₁gt_a : a < t₁ := by
    rw [ht₁]
    have := le_max_left a (t - δ / 2)
    linarith
  have ht₁near : dist t₁ t < δ := by
    rw [Real.dist_eq, abs_sub_lt_iff]
    have := le_max_right a (t - δ / 2)
    constructor <;> [linarith; (rw [ht₁]; linarith)]
  refine ⟨t₁, t, ht₁lt, hasub t₁ ht₁gt_a ht₁lt.le, ht, ?_, hts⟩
  rw [hball ht₁near, hts]

end StepHyp

/-! ### The determination of `Occ` and `Before` -/

namespace StepHyp

variable (H : StepHyp S P d)
include H

omit H in
/-- The `S'`-part of a sign vector of `S`. -/
abbrev res (d : StepData G) (ε : G → SignType) : G → SignType := Function.update ε d.f 0

omit H in
theorem res_sgn (t : ℝ) : res d (sgn S P t) = sgn (S.erase d.f) P t := (sgn_erase t).symm

omit H in
theorem update_res (ε : G → SignType) : Function.update (res d ε) d.f (ε d.f) = ε := by
  rw [Function.update_idem, Function.update_eq_self]

/-- **Occurrence**: `ε` occurs for `S` iff its `S'`-part occurs for `S'` and its `f`-coordinate is
the sign of `f` there (a single value on point cells, a range on interval cells). -/
theorem occ_iff (ε : G → SignType) :
    Occ S P ε ↔ Occ (S.erase d.f) P (res d ε) ∧
      ((Before (S.erase d.f) P (res d ε) (res d ε) ∧
        ε d.f ∈ fsigns (leftSign (S.erase d.f) P d (res d ε)) (rightSign (S.erase d.f) P d (res d ε))) ∨
      (¬ Before (S.erase d.f) P (res d ε) (res d ε) ∧ ε d.f = ptSign (S.erase d.f) d (res d ε))) := by
  constructor
  · rintro ⟨t, ht⟩
    have ht' : sgn (S.erase d.f) P t = res d ε := by rw [← res_sgn, ht]
    refine ⟨⟨t, ht'⟩, ?_⟩
    by_cases hb : Before (S.erase d.f) P (res d ε) (res d ε)
    · left
      refine ⟨hb, ?_⟩
      rw [← H.signs_cell hb]
      exact ⟨t, ht', by rw [← ht, H.sgn_f]⟩
    · right
      refine ⟨hb, ?_⟩
      have h1 : ε d.f = sgn S P t d.f := by rw [ht]
      rw [h1, H.sgn_f]
      exact H.ptSign_eq ⟨⟨t, ht'⟩, hb⟩ ht'
  · rintro ⟨⟨t₀, ht₀⟩, hcond⟩
    rcases hcond with ⟨hb, hmem⟩ | ⟨hb, heq⟩
    · rw [← H.signs_cell hb] at hmem
      obtain ⟨t, ht, hts⟩ := hmem
      refine ⟨t, ?_⟩
      rw [H.sgn_eq, ht, hts, update_res]
    · refine ⟨t₀, ?_⟩
      rw [H.sgn_eq, ht₀, ← heq.trans (H.ptSign_eq ⟨⟨t₀, ht₀⟩, hb⟩ ht₀).symm, update_res]

/-- Same-cell pairs: the realizable ordered pairs of `f`-signs. -/
theorem pair_iff {ε' : G → SignType} (hε' : Before (S.erase d.f) P ε' ε') (s₁ s₂ : SignType) :
    (∃ t₁ t₂, t₁ < t₂ ∧ sgn (S.erase d.f) P t₁ = ε' ∧ sgn (S.erase d.f) P t₂ = ε' ∧
        SignType.sign (eval t₁ (P d.f)) = s₁ ∧ SignType.sign (eval t₂ (P d.f)) = s₂) ↔
      (s₁ ∈ fsigns (leftSign (S.erase d.f) P d ε') (rightSign (S.erase d.f) P d ε') ∧
        s₂ ∈ fsigns (leftSign (S.erase d.f) P d ε') (rightSign (S.erase d.f) P d ε') ∧
        ¬ (s₁ = 0 ∧ s₂ = 0) ∧ (if ε' d.f' = 1 then s₁ ≤ s₂ else s₂ ≤ s₁)) := by
  have hsigns := H.signs_cell hε'
  constructor
  · rintro ⟨t₁, t₂, hlt, h₁, h₂, rfl, rfl⟩
    refine ⟨by rw [← hsigns]; exact ⟨t₁, h₁, rfl⟩, by rw [← hsigns]; exact ⟨t₂, h₂, rfl⟩, ?_, ?_⟩
    · rintro ⟨e₁, e₂⟩
      rw [sign_eq_zero_iff] at e₁ e₂
      by_cases hpos : ε' d.f' = 1
      · have := H.strictMonoOn_cell hpos h₁ h₂ hlt
        simp only at this
        rw [e₁, e₂] at this
        exact lt_irrefl _ this
      · have := H.strictAntiOn_cell hε' hpos h₁ h₂ hlt
        simp only at this
        rw [e₁, e₂] at this
        exact lt_irrefl _ this
    · by_cases hpos : ε' d.f' = 1
      · simp only [hpos, ↓reduceIte]
        have := H.strictMonoOn_cell hpos h₁ h₂ hlt
        exact SignType.sign.monotone this.le
      · simp only [hpos, ↓reduceIte]
        have := H.strictAntiOn_cell hε' hpos h₁ h₂ hlt
        exact SignType.sign.monotone this.le
  · rintro ⟨hs₁, hs₂, hnot, hord⟩
    by_cases heq : s₁ = s₂
    · subst heq
      have hs₁0 : s₁ ≠ 0 := fun h => hnot ⟨h, h⟩
      obtain ⟨t₁, t₂, hlt, h₁, h₂, e₁, e₂⟩ := H.exists_two_of_sign hε' hs₁0 hs₁
      exact ⟨t₁, t₂, hlt, h₁, h₂, e₁, e₂⟩
    · rw [← hsigns] at hs₁ hs₂
      obtain ⟨t₁, h₁, e₁⟩ := hs₁
      obtain ⟨t₂, h₂, e₂⟩ := hs₂
      by_cases hpos : ε' d.f' = 1
      · simp only [hpos, ↓reduceIte] at hord
        have hmono := H.strictMonoOn_cell hpos
        have hlt' : eval t₁ (P d.f) < eval t₂ (P d.f) := by
          have hs : SignType.sign (eval t₁ (P d.f)) < SignType.sign (eval t₂ (P d.f)) := by
            rw [e₁, e₂]
            exact lt_of_le_of_ne hord heq
          exact lt_of_not_ge fun hge => absurd (SignType.sign.monotone hge) (not_le.mpr hs)
        exact ⟨t₁, t₂, (hmono.lt_iff_lt h₁ h₂).mp hlt', h₁, h₂, e₁, e₂⟩
      · simp only [hpos, ↓reduceIte] at hord
        have hanti := H.strictAntiOn_cell hε' hpos
        have hlt' : eval t₂ (P d.f) < eval t₁ (P d.f) := by
          have hs : SignType.sign (eval t₂ (P d.f)) < SignType.sign (eval t₁ (P d.f)) := by
            rw [e₁, e₂]
            exact lt_of_le_of_ne hord (Ne.symm heq)
          exact lt_of_not_ge fun hge => absurd (SignType.sign.monotone hge) (not_le.mpr hs)
        exact ⟨t₁, t₂, (hanti.lt_iff_gt h₂ h₁).mp hlt', h₁, h₂, e₁, e₂⟩

/-- **Order**: `Before` for `S` in terms of `S'`. -/
theorem before_iff (ε₁ ε₂ : G → SignType) :
    Before S P ε₁ ε₂ ↔
      (res d ε₁ ≠ res d ε₂ ∧ Before (S.erase d.f) P (res d ε₁) (res d ε₂) ∧ Occ S P ε₁ ∧ Occ S P ε₂) ∨
      (res d ε₁ = res d ε₂ ∧ Before (S.erase d.f) P (res d ε₁) (res d ε₁) ∧
        ε₁ d.f ∈ fsigns (leftSign (S.erase d.f) P d (res d ε₁)) (rightSign (S.erase d.f) P d (res d ε₁)) ∧
        ε₂ d.f ∈ fsigns (leftSign (S.erase d.f) P d (res d ε₁)) (rightSign (S.erase d.f) P d (res d ε₁)) ∧
        ¬ (ε₁ d.f = 0 ∧ ε₂ d.f = 0) ∧
        (if res d ε₁ d.f' = 1 then ε₁ d.f ≤ ε₂ d.f else ε₂ d.f ≤ ε₁ d.f)) := by
  constructor
  · rintro ⟨t₁, t₂, hlt, h₁, h₂⟩
    have h₁' : sgn (S.erase d.f) P t₁ = res d ε₁ := by rw [← res_sgn, h₁]
    have h₂' : sgn (S.erase d.f) P t₂ = res d ε₂ := by rw [← res_sgn, h₂]
    by_cases hne : res d ε₁ = res d ε₂
    · right
      have hb : Before (S.erase d.f) P (res d ε₁) (res d ε₁) :=
        ⟨t₁, t₂, hlt, h₁', by rw [h₂', hne]⟩
      refine ⟨hne, hb, ?_⟩
      have := (H.pair_iff hb (ε₁ d.f) (ε₂ d.f)).mp
        ⟨t₁, t₂, hlt, h₁', by rw [h₂', hne], by rw [← H.sgn_f, h₁], by rw [← H.sgn_f, h₂]⟩
      exact this
    · left
      exact ⟨hne, ⟨t₁, t₂, hlt, h₁', h₂'⟩, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩
  · rintro (⟨hne, hb, ⟨t₁, h₁⟩, ⟨t₂, h₂⟩⟩ | ⟨heq, hb, hrest⟩)
    · have h₁' : sgn (S.erase d.f) P t₁ = res d ε₁ := by rw [← res_sgn, h₁]
      have h₂' : sgn (S.erase d.f) P t₂ = res d ε₂ := by rw [← res_sgn, h₂]
      exact ⟨t₁, t₂, lt_of_before H.hS' hb hne h₁' h₂', h₁, h₂⟩
    · obtain ⟨t₁, t₂, hlt, h₁, h₂, e₁, e₂⟩ := (H.pair_iff hb (ε₁ d.f) (ε₂ d.f)).mpr hrest
      refine ⟨t₁, t₂, hlt, ?_, ?_⟩
      · rw [H.sgn_eq, h₁, e₁, update_res]
      · rw [H.sgn_eq, h₂, heq, e₂, update_res]

end StepHyp

end TS
