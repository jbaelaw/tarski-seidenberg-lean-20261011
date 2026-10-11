import TS.Param

/-!
# The parametric induction and the relative Tarski–Seidenberg theorem

For a closed family `F`, the *profile* of a subfamily `S` at `x` records which sign vectors occur
and their order (`Occ`, `Before`) as Booleans; it lives in a finite type.  The Hörmander step
shows that the profile of `S` is an explicit function `Ψ` of the profile of `S.erase f` and the
step data.  By induction on `S` (down-closed subfamilies of the effective family on a piece
`lcs = lam`) all the sets `{x | lcs x = lam ∧ profile S (Px x) = p}` are semialgebraic.  Finally,
for any finite family `F₀ ⊆ A[X]`, the set of parameters `x` at which a prescribed sign condition
on `F₀` is realized by some `t ∈ ℝ` is semialgebraic (`semialg_exists_sign`).
-/

namespace TS

open Polynomial Set
open scoped Classical

variable {A : Type*} [CommRing A]
variable {X : Type*} (ev : X → A →+* ℝ) (F : Finset A[X])

/-- Sign vectors. -/
abbrev V := Idx F → SignType

/-- Profiles: which vectors occur, and their order, as Booleans. -/
abbrev Prof := (V F → Bool) × (V F → V F → Bool)

/-- The profile of the subfamily `S` of the actual family `P`. -/
noncomputable def profile (S : Finset (Idx F)) (P : Idx F → ℝ[X]) : Prof F :=
  (fun ε => decide (Occ S P ε), fun ε₁ ε₂ => decide (Before S P ε₁ ε₂))

theorem profile_fst (S : Finset (Idx F)) (P : Idx F → ℝ[X]) (ε : V F) :
    (profile F S P).1 ε = true ↔ Occ S P ε := by
  simp [profile]

theorem profile_snd (S : Finset (Idx F)) (P : Idx F → ℝ[X]) (ε₁ ε₂ : V F) :
    (profile F S P).2 ε₁ ε₂ = true ↔ Before S P ε₁ ε₂ := by
  simp [profile]

/-! ### The step as a function of profiles -/

/-- The occurrence formula of the step, in terms of a profile `p'` of `S'`. -/
def OccF (S' : Finset (Idx F)) (d : StepData (Idx F)) (p' : Prof F) (ε : V F) : Prop :=
  p'.1 (StepHyp.res d ε) = true ∧
    ((p'.2 (StepHyp.res d ε) (StepHyp.res d ε) = true ∧
      ε d.f ∈ fsigns (leftSignP (fun a b => p'.2 a b = true) S' d (StepHyp.res d ε))
        (rightSignP (fun a b => p'.2 a b = true) S' d (StepHyp.res d ε))) ∨
    (¬ p'.2 (StepHyp.res d ε) (StepHyp.res d ε) = true ∧ ε d.f = ptSign S' d (StepHyp.res d ε)))

/-- The order formula of the step. -/
def BefF (S' : Finset (Idx F)) (d : StepData (Idx F)) (p' : Prof F) (ε₁ ε₂ : V F) : Prop :=
  (StepHyp.res d ε₁ ≠ StepHyp.res d ε₂ ∧ p'.2 (StepHyp.res d ε₁) (StepHyp.res d ε₂) = true ∧
    OccF F S' d p' ε₁ ∧ OccF F S' d p' ε₂) ∨
  (StepHyp.res d ε₁ = StepHyp.res d ε₂ ∧ p'.2 (StepHyp.res d ε₁) (StepHyp.res d ε₁) = true ∧
    ε₁ d.f ∈ fsigns (leftSignP (fun a b => p'.2 a b = true) S' d (StepHyp.res d ε₁))
      (rightSignP (fun a b => p'.2 a b = true) S' d (StepHyp.res d ε₁)) ∧
    ε₂ d.f ∈ fsigns (leftSignP (fun a b => p'.2 a b = true) S' d (StepHyp.res d ε₁))
      (rightSignP (fun a b => p'.2 a b = true) S' d (StepHyp.res d ε₁)) ∧
    ¬ (ε₁ d.f = 0 ∧ ε₂ d.f = 0) ∧
    (if StepHyp.res d ε₁ d.f' = 1 then ε₁ d.f ≤ ε₂ d.f else ε₂ d.f ≤ ε₁ d.f))

/-- The profile transformation of one step. -/
noncomputable def Ψ (S' : Finset (Idx F)) (d : StepData (Idx F)) (p' : Prof F) : Prof F :=
  (fun ε => decide (OccF F S' d p' ε), fun ε₁ ε₂ => decide (BefF F S' d p' ε₁ ε₂))

theorem profile_eq_Ψ {S : Finset (Idx F)} {P : Idx F → ℝ[X]} {d : StepData (Idx F)}
    (H : StepHyp S P d) : profile F S P = Ψ F (S.erase d.f) d (profile F (S.erase d.f) P) := by
  have hB : (fun a b : V F => (profile F (S.erase d.f) P).2 a b = true) = Before (S.erase d.f) P := by
    funext a b
    exact propext (profile_snd F _ _ a b)
  have hocc : ∀ ε, Occ S P ε ↔ OccF F (S.erase d.f) d (profile F (S.erase d.f) P) ε := by
    intro ε
    rw [H.occ_iff, OccF, hB, ← leftSign_eq, ← rightSign_eq, profile_fst, profile_snd]
  refine Prod.ext (funext fun ε => ?_) (funext fun ε₁ => funext fun ε₂ => ?_)
  · show decide (Occ S P ε) = decide (OccF F (S.erase d.f) d (profile F (S.erase d.f) P) ε)
    exact decide_eq_decide.mpr (hocc ε)
  · show decide (Before S P ε₁ ε₂) =
      decide (BefF F (S.erase d.f) d (profile F (S.erase d.f) P) ε₁ ε₂)
    refine decide_eq_decide.mpr ?_
    rw [H.before_iff, BefF, hB, ← leftSign_eq, ← rightSign_eq, profile_snd, profile_snd,
      ← hocc, ← hocc]

/-! ### The degenerate cases -/

/-- The profile of the empty family. -/
noncomputable def profEmpty : Prof F :=
  (fun ε => decide (ε = 0), fun ε₁ ε₂ => decide (ε₁ = 0 ∧ ε₂ = 0))

theorem sgn_empty (P : Idx F → ℝ[X]) (t : ℝ) : sgn (∅ : Finset (Idx F)) P t = 0 := by
  funext g
  exact sgn_apply_of_not_mem (Finset.notMem_empty g)

theorem profile_empty (P : Idx F → ℝ[X]) : profile F ∅ P = profEmpty F := by
  refine Prod.ext (funext fun ε => ?_) (funext fun ε₁ => funext fun ε₂ => ?_)
  · simp only [profile, profEmpty]
    refine decide_eq_decide.mpr ⟨?_, ?_⟩
    · rintro ⟨t, ht⟩
      rw [← ht, sgn_empty]
    · rintro rfl
      exact ⟨0, sgn_empty F P 0⟩
  · simp only [profile, profEmpty]
    refine decide_eq_decide.mpr ⟨?_, ?_⟩
    · rintro ⟨t₁, t₂, -, h₁, h₂⟩
      rw [← h₁, ← h₂, sgn_empty, sgn_empty]
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨0, 1, zero_lt_one, sgn_empty F P 0, sgn_empty F P 1⟩

/-- The profile of a family with constant sign vector `v`. -/
noncomputable def profConst (v : V F) : Prof F :=
  (fun ε => decide (ε = v), fun ε₁ ε₂ => decide (ε₁ = v ∧ ε₂ = v))

theorem profile_const (S : Finset (Idx F)) (P : Idx F → ℝ[X]) (v : V F)
    (h : ∀ t, sgn S P t = v) : profile F S P = profConst F v := by
  refine Prod.ext (funext fun ε => ?_) (funext fun ε₁ => funext fun ε₂ => ?_)
  · simp only [profile, profConst]
    refine decide_eq_decide.mpr ⟨?_, ?_⟩
    · rintro ⟨t, ht⟩
      rw [← ht, h]
    · rintro rfl
      exact ⟨0, h 0⟩
  · simp only [profile, profConst]
    refine decide_eq_decide.mpr ⟨?_, ?_⟩
    · rintro ⟨t₁, t₂, -, h₁, h₂⟩
      rw [← h₁, ← h₂, h, h]
      exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨0, 1, zero_lt_one, h 0, h 1⟩

/-- On a piece, a family of constants has the constant sign vector given by `lam`. -/
theorem sgn_of_constants {x : X} {lam : V F} (hlam : lcs ev F x = lam) {S : Finset (Idx F)}
    (hconst : ∀ g ∈ S, g.1.natDegree = 0) (t : ℝ) :
    sgn S (Px ev F x) t = fun g => if g ∈ S then lam g else 0 := by
  funext g
  by_cases hg : g ∈ S
  · rw [sgn_apply_of_mem hg]
    simp only [hg, ↓reduceIte]
    rw [← hlam]
    simp only [lcs, Px]
    have hC := eq_C_of_natDegree_eq_zero (hconst g hg)
    rw [hC, Polynomial.map_C, eval_C, leadingCoeff_C]
  · rw [sgn_apply_of_not_mem hg]
    simp only [hg, ↓reduceIte]

/-- The data of the step with the representative function `ρ` and leading-coefficient signs
`lam`. -/
noncomputable def dataOf [IsDomain A] (hF : IsClosedFam F) (f : Idx F) (lam : V F) (ρ : Idx F → Option (Idx F)) :
    StepData (Idx F) where
  f := f
  f' := ⟨derivative f.1, hF.deriv _ f.2⟩
  n := fun h => premExp f.1 h.1
  rep := ρ
  lcs := lam
  df := f.1.natDegree

/-- The representative function of the step at `x`. -/
noncomputable def repFn [IsDomain A] (hF : IsClosedFam F) (x : X) (f : Idx F) : Idx F → Option (Idx F) :=
  fun h => if hd : h.1.natDegree ≤ f.1.natDegree then
    repAt ev F x ⟨prem f.1 h.1, hF.rem _ f.2 _ h.2 hd⟩ else none

theorem stepData_eq [IsDomain A] (hF : IsClosedFam F) (x : X) (f : Idx F) :
    stepData ev F hF x f = dataOf F hF f (lcs ev F x) (repFn ev F hF x f) := rfl

theorem semialg_repFn [IsDomain A] (hF : IsClosedFam F) (f : Idx F) (ρ : Idx F → Option (Idx F)) :
    Semialg (Rev ev) {x | repFn ev F hF x f = ρ} := by
  have : {x | repFn ev F hF x f = ρ} = ⋂ h : Idx F, {x | repFn ev F hF x f h = ρ h} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
  rw [this]
  refine Semialg.iInter fun h => ?_
  unfold repFn
  split_ifs with hd
  · exact semialg_repAt ev F _ _
  · exact semialg_const ev _

variable [IsDomain A] [IsAddTorsionFree A]

/-- **The parametric induction**: the profile sets of down-closed subfamilies on a piece are
semialgebraic. -/
theorem semialg_profile (hF : IsClosedFam F) (lam : V F) :
    ∀ (n : ℕ) (S : Finset (Idx F)), S.card = n → DownClosed F lam S → ∀ p : Prof F,
      Semialg (Rev ev) {x | lcs ev F x = lam ∧ profile F S (Px ev F x) = p} := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hcard hS p
  rcases S.eq_empty_or_nonempty with rfl | hne
  · -- the empty family
    have : {x | lcs ev F x = lam ∧ profile F ∅ (Px ev F x) = p} =
        {x | lcs ev F x = lam} ∩ {_x | profEmpty F = p} := by
      ext x
      simp [profile_empty]
    rw [this]
    exact (semialg_lcs ev F lam).inter (semialg_const ev _)
  obtain ⟨f, hf, hmax⟩ := S.exists_max_image (fun g => g.1.natDegree) hne
  by_cases hdeg : f.1.natDegree = 0
  · -- all members are constants
    have hconst : ∀ g ∈ S, g.1.natDegree = 0 := fun g hg => by
      have := hmax g hg
      omega
    have : {x | lcs ev F x = lam ∧ profile F S (Px ev F x) = p} =
        {x | lcs ev F x = lam} ∩ {_x | profConst F (fun g => if g ∈ S then lam g else 0) = p} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨hlam, hp⟩
        refine ⟨hlam, ?_⟩
        rw [← hp, profile_const F S _ _ (sgn_of_constants ev F hlam hconst)]
      · rintro ⟨hlam, hp⟩
        refine ⟨hlam, ?_⟩
        rw [profile_const F S _ _ (sgn_of_constants ev F hlam hconst), hp]
    rw [this]
    exact (semialg_lcs ev F lam).inter (semialg_const ev _)
  · -- the Hörmander step
    have hdeg' : 0 < f.1.natDegree := Nat.pos_of_ne_zero hdeg
    have hS' : DownClosed F lam (S.erase f) := DownClosed.erase F hS hmax
    have hcard' : (S.erase f).card < n := by
      rw [← hcard]
      exact Finset.card_erase_lt_of_mem hf
    have hstep : ∀ x, lcs ev F x = lam →
        profile F S (Px ev F x) =
          Ψ F (S.erase f) (dataOf F hF f lam (repFn ev F hF x f)) (profile F (S.erase f) (Px ev F x)) := by
      intro x hlam
      have H := stepHyp ev F hF hlam hS hf hmax hdeg'
      have := profile_eq_Ψ F H
      rw [stepData_eq, hlam] at this
      exact this
    have : {x | lcs ev F x = lam ∧ profile F S (Px ev F x) = p} =
        ⋃ p' : Prof F, ⋃ ρ : Idx F → Option (Idx F),
          ({x | lcs ev F x = lam ∧ profile F (S.erase f) (Px ev F x) = p'} ∩
            {x | repFn ev F hF x f = ρ}) ∩ {_x | Ψ F (S.erase f) (dataOf F hF f lam ρ) p' = p} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · rintro ⟨hlam, hp⟩
        refine ⟨profile F (S.erase f) (Px ev F x), repFn ev F hF x f, ⟨⟨hlam, rfl⟩, rfl⟩, ?_⟩
        rw [← hp, hstep x hlam]
      · rintro ⟨p', ρ, ⟨⟨hlam, hp'⟩, hρ⟩, hΨ⟩
        refine ⟨hlam, ?_⟩
        rw [hstep x hlam, hp', hρ, hΨ]
    rw [this]
    refine Semialg.iUnion fun p' => Semialg.iUnion fun ρ => ?_
    exact ((ih _ hcard' _ rfl hS' p').inter (semialg_repFn ev F hF f ρ)).inter (semialg_const ev _)

/-! ### The relative Tarski–Seidenberg theorem -/

/-- The sign of a member at `(x, t)` in terms of the effective family: its own coordinate when the
leading coefficient does not vanish, otherwise the coordinate of its representative. -/
noncomputable def transform (lam : V F) (ρ : Idx F → Option (Idx F)) (η : V F) : V F :=
  fun g => if lam g ≠ 0 then η g else (ρ g).elim 0 η

omit [IsAddTorsionFree A] in
theorem sign_eval_eq_transform (hF : IsClosedFam F) {x : X} {lam : V F} (hlam : lcs ev F x = lam)
    (t : ℝ) (g : Idx F) :
    SignType.sign (eval t (Px ev F x g)) =
      transform F lam (repAt ev F x) (sgn (eff F lam) (Px ev F x) t) g := by
  unfold transform
  split_ifs with h
  · rw [sgn_apply_of_mem ((mem_eff F).mpr h)]
  · rw [not_not] at h
    have hlc : ev x g.1.leadingCoeff = 0 := by
      rw [← hlam] at h
      exact sign_eq_zero_iff.mp h
    obtain ⟨hsome, hnone⟩ := repAt_spec ev F hF x g
    rcases hr : repAt ev F x g with _ | r
    · simp only [Option.elim]
      have := hnone hr
      simp only [Px] at this ⊢
      rw [this, eval_zero, sign_zero]
    · simp only [Option.elim]
      obtain ⟨hrlc, hrmap, -⟩ := hsome r hr
      have hr_eff : r ∈ eff F lam := by
        rw [mem_eff, ← hlam]
        exact (lam_ne_zero_iff ev F rfl r).mpr hrlc
      rw [sgn_apply_of_mem hr_eff]
      simp only [Px]
      rw [hrmap]

/-- **Relative Tarski–Seidenberg**: for every finite family `F₀ ⊆ A[X]` and sign condition `ε`,
the set of parameters at which some `t ∈ ℝ` realizes the condition is semialgebraic. -/
theorem semialg_exists_sign (F₀ : Finset A[X]) (ε : A[X] → SignType) :
    Semialg (Rev ev) {x | ∃ t : ℝ, ∀ g ∈ F₀, SignType.sign (eval t (g.map (ev x))) = ε g} := by
  set F := closure F₀ with hFdef
  have hF : IsClosedFam F := isClosedFam_closure F₀
  have hsub : F₀ ⊆ F := subset_closure F₀
  -- the realization condition in terms of the effective family on a piece
  have key : ∀ x, (∃ t : ℝ, ∀ g ∈ F₀, SignType.sign (eval t (g.map (ev x))) = ε g) ↔
      ∃ η : V F, Occ (eff F (lcs ev F x)) (Px ev F x) η ∧
        ∀ g (hg : g ∈ F₀), transform F (lcs ev F x) (repAt ev F x) η ⟨g, hsub hg⟩ = ε g := by
    intro x
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨sgn (eff F (lcs ev F x)) (Px ev F x) t, ⟨t, rfl⟩, fun g hg => ?_⟩
      rw [← sign_eval_eq_transform ev F hF rfl t ⟨g, hsub hg⟩]
      exact ht g hg
    · rintro ⟨η, ⟨t, ht⟩, hε⟩
      refine ⟨t, fun g hg => ?_⟩
      have := hε g hg
      rw [← ht, ← sign_eval_eq_transform ev F hF rfl t ⟨g, hsub hg⟩] at this
      exact this
  have : {x | ∃ t : ℝ, ∀ g ∈ F₀, SignType.sign (eval t (g.map (ev x))) = ε g} =
      ⋃ lam : V F, ⋃ ρ : Idx F → Option (Idx F), ⋃ p : Prof F,
        ({x | lcs ev F x = lam ∧ profile F (eff F lam) (Px ev F x) = p} ∩
          {x | ∀ g, repAt ev F x g = ρ g}) ∩
        {_x | ∃ η : V F, p.1 η = true ∧ ∀ g (hg : g ∈ F₀), transform F lam ρ η ⟨g, hsub hg⟩ = ε g} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    rw [key x]
    constructor
    · rintro ⟨η, hocc, hε⟩
      refine ⟨lcs ev F x, repAt ev F x, profile F (eff F (lcs ev F x)) (Px ev F x),
        ⟨⟨rfl, rfl⟩, fun g => rfl⟩, η, (profile_fst F _ _ η).mpr hocc, hε⟩
    · rintro ⟨lam, ρ, p, ⟨⟨hlam, hp⟩, hρ⟩, η, hocc, hε⟩
      subst hlam
      have hρ' : repAt ev F x = ρ := funext hρ
      subst hρ'
      subst hp
      exact ⟨η, (profile_fst F _ _ η).mp hocc, hε⟩
  rw [this]
  refine Semialg.iUnion fun lam => Semialg.iUnion fun ρ => Semialg.iUnion fun p => ?_
  refine ((semialg_profile ev F hF lam _ _ rfl (DownClosed.eff F lam) p).inter ?_).inter
    (semialg_const ev _)
  have : {x | ∀ g, repAt ev F x g = ρ g} = ⋂ g, {x | repAt ev F x g = ρ g} := by
    ext x
    simp
  rw [this]
  exact Semialg.iInter fun g => semialg_repAt ev F g (ρ g)

end TS
