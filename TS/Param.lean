import TS.Step
import TS.Closure
import TS.Semialg

/-!
# Parametric families: evaluation, truncation representatives and the step data

A parameter space `X` with evaluation homomorphisms `ev x : A →+* ℝ` (think `A = ℝ[x₁, …, xₙ]`,
`ev x = eval x`).  `Rev ev` is the subring of functions `x ↦ ev x a`; semialgebraic sets are
`Semialg (Rev ev)`.  For a closed finite family `F ⊆ A[X]` (`IsClosedFam`), the actual polynomials
at `x` are `Px ev F x g = g.map (ev x)`.

* `repAt ev F x g` is the first iterated truncation of `g` whose leading coefficient does not
  vanish at `x` (it has the same value at `x` as `g`), or `none` when `g` vanishes at `x`.
* The level sets of the leading-coefficient signs `lcs` and of `repAt` are semialgebraic.
* `stepHyp`: on the piece `lcs = lam`, every down-closed `S ⊆ eff lam` with a member `f` of
  maximal positive degree satisfies the hypotheses of the Hörmander step with explicit data
  `stepData`.
-/

namespace TS

open Polynomial Set
open scoped Classical

variable {A : Type*} [CommRing A]
variable {X : Type*} (ev : X → A →+* ℝ)

/-- The evaluation functions as a ring homomorphism `A →+* (X → ℝ)`. -/
def evRing : A →+* (X → ℝ) := RingHom.pi fun x => ev x

/-- The subring of evaluation functions. -/
def Rev : Subring (X → ℝ) := (evRing ev).range

theorem mem_Rev (a : A) : (fun x => ev x a) ∈ Rev ev := ⟨a, rfl⟩

theorem semialg_zero (a : A) : Semialg (Rev ev) {x | ev x a = 0} := Semialg.zero (mem_Rev ev a)

theorem semialg_ne_zero (a : A) : Semialg (Rev ev) {x | ev x a ≠ 0} :=
  Semialg.ne_zero (mem_Rev ev a)

theorem semialg_sign (a : A) (σ : SignType) : Semialg (Rev ev) {x | SignType.sign (ev x a) = σ} :=
  Semialg.sign_eq (mem_Rev ev a) σ

theorem semialg_const (p : Prop) : Semialg (Rev ev) {_x : X | p} := by
  by_cases hp : p
  · exact Semialg.univ.of_eq (by ext; simp [hp])
  · exact Semialg.empty.of_eq (by ext; simp [hp])

variable (F : Finset A[X])

/-- The index type of the family. -/
abbrev Idx := {g : A[X] // g ∈ F}

/-- The actual polynomials at `x`. -/
noncomputable def Px (x : X) : Idx F → ℝ[X] := fun g => g.1.map (ev x)

/-- The signs of the leading coefficients at `x`. -/
noncomputable def lcs (x : X) : Idx F → SignType := fun g => SignType.sign (ev x g.1.leadingCoeff)

/-- The effective family for the leading-coefficient signs `lam`. -/
def eff (lam : Idx F → SignType) : Finset (Idx F) := Finset.univ.filter fun g => lam g ≠ 0

theorem mem_eff {lam : Idx F → SignType} {g : Idx F} : g ∈ eff F lam ↔ lam g ≠ 0 := by
  simp [eff]

theorem semialg_lcs (lam : Idx F → SignType) : Semialg (Rev ev) {x | lcs ev F x = lam} := by
  have : {x | lcs ev F x = lam} = ⋂ g : Idx F, {x | SignType.sign (ev x g.1.leadingCoeff) = lam g} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, lcs, funext_iff]
  rw [this]
  exact Semialg.iInter fun g => semialg_sign ev _ _

/-! ### Basic facts about the actual polynomials -/

theorem lc_Px {x : X} {g : Idx F} (h : ev x g.1.leadingCoeff ≠ 0) :
    (Px ev F x g).leadingCoeff = ev x g.1.leadingCoeff :=
  leadingCoeff_map_of_leadingCoeff_ne_zero _ h

theorem natDegree_Px {x : X} {g : Idx F} (h : ev x g.1.leadingCoeff ≠ 0) :
    (Px ev F x g).natDegree = g.1.natDegree :=
  natDegree_map_of_leadingCoeff_ne_zero _ h

theorem Px_ne_zero {x : X} {g : Idx F} (h : ev x g.1.leadingCoeff ≠ 0) : Px ev F x g ≠ 0 := by
  intro h0
  have := lc_Px ev F h
  rw [h0, leadingCoeff_zero] at this
  exact h this.symm

theorem natDegree_Px_le (x : X) (g : Idx F) : (Px ev F x g).natDegree ≤ g.1.natDegree :=
  natDegree_map_le

theorem lc_derivative_ne_zero [IsAddTorsionFree A] {x : X} {g : A[X]} (h : ev x g.leadingCoeff ≠ 0)
    (hdeg : g.natDegree ≠ 0) : ev x (derivative g).leadingCoeff ≠ 0 := by
  rw [leadingCoeff_derivative, map_mul, map_natCast]
  exact mul_ne_zero h (by exact_mod_cast hdeg)

/-- Erasing a leading term that vanishes at `x` does not change the value at `x`. -/
theorem map_eraseLead_of_lc_eq_zero {x : X} {g : A[X]} (h : ev x g.leadingCoeff = 0) :
    g.eraseLead.map (ev x) = g.map (ev x) := by
  conv_rhs => rw [← eraseLead_add_monomial_natDegree_leadingCoeff g]
  rw [Polynomial.map_add, Polynomial.map_monomial, h, monomial_zero_right, add_zero]

/-! ### Truncation representatives -/

/-- The first iterated truncation of `g` (within `k` steps) whose leading coefficient does not
vanish at `x`, as a member of the family. -/
noncomputable def repFuel (x : X) : ℕ → A[X] → Option (Idx F)
  | 0, _ => none
  | k + 1, g => if ev x g.leadingCoeff ≠ 0 then (if hg : g ∈ F then some ⟨g, hg⟩ else none)
      else repFuel x k g.eraseLead

/-- The representative of `g` at `x`. -/
noncomputable def repAt (x : X) (g : Idx F) : Option (Idx F) :=
  repFuel ev F x (g.1.natDegree + 1) g.1

theorem repFuel_zero (x : X) : ∀ k, repFuel ev F x k 0 = none := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [repFuel, leadingCoeff_zero, map_zero, ne_eq, not_true_eq_false, ↓reduceIte,
      eraseLead_zero]
    exact ih

theorem semialg_repFuel : ∀ (k : ℕ) (g : A[X]) (o : Option (Idx F)),
    Semialg (Rev ev) {x | repFuel ev F x k g = o} := by
  intro k
  induction k with
  | zero =>
    intro g o
    exact semialg_const ev (none = o)
  | succ k ih =>
    intro g o
    have : {x | repFuel ev F x (k + 1) g = o} =
        ({x | ev x g.leadingCoeff ≠ 0} ∩ {_x | (if hg : g ∈ F then some ⟨g, hg⟩ else none) = o}) ∪
        ({x | ev x g.leadingCoeff = 0} ∩ {x | repFuel ev F x k g.eraseLead = o}) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, repFuel]
      by_cases h : ev x g.leadingCoeff ≠ 0
      · simp [h]
      · rw [not_not] at h
        simp [h]
    rw [this]
    exact ((semialg_ne_zero ev _).inter (semialg_const ev _)).union
      ((semialg_zero ev _).inter (ih _ _))

theorem semialg_repAt (g : Idx F) (o : Option (Idx F)) :
    Semialg (Rev ev) {x | repAt ev F x g = o} :=
  semialg_repFuel ev F _ _ _

/-! ### Down-closed subfamilies and the step data -/

/-- `S` is a down-closed subfamily of the effective family: it contains every effective member of
smaller degree than one of its members. -/
def DownClosed (lam : Idx F → SignType) (S : Finset (Idx F)) : Prop :=
  S ⊆ eff F lam ∧ ∀ g ∈ eff F lam, ∀ h ∈ S, g.1.natDegree < h.1.natDegree → g ∈ S

theorem DownClosed.erase {lam : Idx F → SignType} {S : Finset (Idx F)} (hS : DownClosed F lam S)
    {f : Idx F} (hmax : ∀ g ∈ S, g.1.natDegree ≤ f.1.natDegree) : DownClosed F lam (S.erase f) := by
  refine ⟨(Finset.erase_subset _ _).trans hS.1, fun g hg h hh hlt => ?_⟩
  have hhS : h ∈ S := Finset.mem_of_mem_erase hh
  refine Finset.mem_erase.mpr ⟨?_, hS.2 g hg h hhS hlt⟩
  rintro rfl
  exact absurd (hmax h hhS) (not_le.mpr hlt)

theorem DownClosed.eff (lam : Idx F → SignType) : DownClosed F lam (eff F lam) :=
  ⟨subset_rfl, fun _ hg _ _ _ => hg⟩

theorem lam_ne_zero_iff {x : X} {lam : Idx F → SignType} (hlam : lcs ev F x = lam) (g : Idx F) :
    lam g ≠ 0 ↔ ev x g.1.leadingCoeff ≠ 0 := by
  rw [← hlam, lcs, Ne, Ne, sign_eq_zero_iff]


variable [IsDomain A]

theorem repFuel_spec (hF : IsClosedFam F) (x : X) :
    ∀ k (g : A[X]), g ∈ F → g.natDegree < k →
      (∀ r, repFuel ev F x k g = some r →
        ev x r.1.leadingCoeff ≠ 0 ∧ r.1.map (ev x) = g.map (ev x) ∧ r.1.natDegree ≤ g.natDegree) ∧
      (repFuel ev F x k g = none → g.map (ev x) = 0) := by
  intro k
  induction k with
  | zero => intro g _ h; exact absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro g hgF hk
    simp only [repFuel]
    split_ifs with hlc
    · refine ⟨fun r hr => ?_, fun h => by simp_all⟩
      have hr' : (⟨g, hgF⟩ : Idx F) = r := by simpa using hr
      subst hr'
      exact ⟨hlc, rfl, le_rfl⟩
    · rw [not_not] at hlc
      have hmap := map_eraseLead_of_lc_eq_zero ev hlc
      rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero g with hlt | h0
      · have hk' : g.eraseLead.natDegree < k := by omega
        obtain ⟨h1, h2⟩ := ih g.eraseLead (hF.erase g hgF) hk'
        refine ⟨fun r hr => ?_, fun h => ?_⟩
        · obtain ⟨a, b, c⟩ := h1 r hr
          exact ⟨a, b.trans hmap, c.trans (eraseLead_natDegree_le g |>.trans (Nat.sub_le _ _))⟩
        · rw [← hmap]
          exact h2 h
      · rw [h0, repFuel_zero]
        refine ⟨fun r hr => (by cases hr), fun _ => ?_⟩
        rw [← hmap, h0, Polynomial.map_zero]

theorem repAt_spec (hF : IsClosedFam F) (x : X) (g : Idx F) :
    (∀ r, repAt ev F x g = some r →
      ev x r.1.leadingCoeff ≠ 0 ∧ r.1.map (ev x) = g.1.map (ev x) ∧ r.1.natDegree ≤ g.1.natDegree) ∧
    (repAt ev F x g = none → g.1.map (ev x) = 0) :=
  repFuel_spec ev F hF x _ g.1 g.2 (Nat.lt_succ_self _)

/-- The data of the step removing `f`. -/
noncomputable def stepData (hF : IsClosedFam F) (x : X) (f : Idx F) : StepData (Idx F) where
  f := f
  f' := ⟨derivative f.1, hF.deriv _ f.2⟩
  n := fun h => premExp f.1 h.1
  rep := fun h => if hd : h.1.natDegree ≤ f.1.natDegree then
    repAt ev F x ⟨prem f.1 h.1, hF.rem _ f.2 _ h.2 hd⟩ else none
  lcs := lcs ev F x
  df := f.1.natDegree

/-- **The step hypotheses hold on a piece.** -/
theorem stepHyp [IsAddTorsionFree A] (hF : IsClosedFam F) {x : X} {lam : Idx F → SignType} (hlam : lcs ev F x = lam)
    {S : Finset (Idx F)} (hS : DownClosed F lam S) {f : Idx F} (hf : f ∈ S)
    (hmax : ∀ g ∈ S, g.1.natDegree ≤ f.1.natDegree) (hdeg : 0 < f.1.natDegree) :
    StepHyp S (Px ev F x) (stepData ev F hF x f) := by
  have hlc : ∀ g ∈ S, ev x g.1.leadingCoeff ≠ 0 := fun g hg =>
    (lam_ne_zero_iff ev F hlam g).mp (mem_eff F |>.mp (hS.1 hg))
  have hmemS : ∀ g : Idx F, ev x g.1.leadingCoeff ≠ 0 → ∀ h ∈ S, g.1.natDegree < h.1.natDegree →
      g ∈ S := fun g hg h hh hlt =>
    hS.2 g ((mem_eff F).mpr ((lam_ne_zero_iff ev F hlam g).mpr hg)) h hh hlt
  -- the derivative of a member of `S` of positive degree is in `S`
  have hderiv : ∀ g ∈ S, g.1.natDegree ≠ 0 →
      (⟨derivative g.1, hF.deriv _ g.2⟩ : Idx F) ∈ S := fun g hg hg0 =>
    hmemS _ (lc_derivative_ne_zero ev (hlc g hg) hg0) g hg (natDegree_derivative_lt hg0)
  have hf'S : (⟨derivative f.1, hF.deriv _ f.2⟩ : Idx F) ∈ S.erase f := by
    refine Finset.mem_erase.mpr ⟨?_, hderiv f hf hdeg.ne'⟩
    intro h
    have := congrArg (fun g : Idx F => g.1.natDegree) h
    simp only at this
    have := natDegree_derivative_lt hdeg.ne'
    omega
  refine ⟨hf, fun g hg => Px_ne_zero ev F (hlc g hg), ?_, ?_, ?_, hf'S, ?_, ?_, ?_, ?_, ?_⟩
  · -- derivative-closed
    intro g hg hgdeg
    have hg0 : g.1.natDegree ≠ 0 := by
      have := natDegree_Px_le ev F x g
      omega
    exact ⟨_, hderiv g hg hg0, (derivative_map _ _).symm⟩
  · intro g hg
    show (Px ev F x g).natDegree ≤ (Px ev F x f).natDegree
    rw [natDegree_Px ev F (hlc g hg), natDegree_Px ev F (hlc f hf)]
    exact hmax g hg
  · show 0 < (Px ev F x f).natDegree
    rw [natDegree_Px ev F (hlc f hf)]
    exact hdeg
  · exact (derivative_map _ _).symm
  · -- remainders
    intro h hh
    have hhS : h ∈ S := Finset.mem_of_mem_erase hh
    have hd : h.1.natDegree ≤ f.1.natDegree := hmax h hhS
    have hh0 : h.1 ≠ 0 := by
      intro h0
      apply hlc h hhS
      rw [h0, leadingCoeff_zero, map_zero]
    obtain ⟨q, hq, -⟩ := prem_spec f.1 h.1 hh0
    refine ⟨q.map (ev x), ?_⟩
    have hmap := congrArg (Polynomial.map (ev x)) hq
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_add] at hmap
    rw [lc_Px ev F (hlc h hhS)]
    simp only [stepData, hd, ↓reduceDIte]
    obtain ⟨hsome, hnone⟩ := repAt_spec ev F hF x ⟨prem f.1 h.1, hF.rem _ f.2 _ h.2 hd⟩
    rcases hr : repAt ev F x ⟨prem f.1 h.1, hF.rem _ f.2 _ h.2 hd⟩ with _ | ρ
    · simp only [Option.elim]
      rw [hnone hr] at hmap
      exact hmap
    · simp only [Option.elim, Px]
      rw [(hsome ρ hr).2.1]
      exact hmap
  · -- representatives lie in `S'`
    intro h hh ρ hρ
    have hhS : h ∈ S := Finset.mem_of_mem_erase hh
    have hd : h.1.natDegree ≤ f.1.natDegree := hmax h hhS
    simp only [stepData, hd, ↓reduceDIte] at hρ
    have hh0 : h.1 ≠ 0 := by
      intro h0
      apply hlc h hhS
      rw [h0, leadingCoeff_zero, map_zero]
    obtain ⟨hsome, -⟩ := repAt_spec ev F hF x ⟨prem f.1 h.1, hF.rem _ f.2 _ h.2 hd⟩
    obtain ⟨hρlc, hρmap, hρdeg⟩ := hsome ρ hρ
    have hρne : ρ.1.map (ev x) ≠ 0 := by
      intro h0
      apply hρlc
      have := congrArg leadingCoeff h0
      rw [leadingCoeff_map_of_leadingCoeff_ne_zero _ hρlc, leadingCoeff_zero] at this
      exact this
    have hh1 : 0 < h.1.natDegree := by
      by_contra h0
      rw [not_lt, Nat.le_zero] at h0
      obtain ⟨-, -, hr⟩ := prem_spec f.1 h.1 hh0
      rw [degree_eq_natDegree hh0, h0, Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hr
      apply hρne
      rw [hρmap]
      simp only [hr, Polynomial.map_zero]
    have hlt : ρ.1.natDegree < h.1.natDegree :=
      lt_of_le_of_lt hρdeg (natDegree_prem_lt f.1 h.1 hh0 hh1)
    refine Finset.mem_erase.mpr ⟨?_, hmemS ρ hρlc h hhS hlt⟩
    rintro rfl
    exact absurd hd (not_le.mpr hlt)
  · intro g hg
    simp only [stepData, lcs]
    rw [lc_Px ev F (hlc g hg)]
  · show f.1.natDegree = (Px ev F x f).natDegree
    exact (natDegree_Px ev F (hlc f hf)).symm

end TS
