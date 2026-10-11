import TS.Cells

/-!
# Point cells, interval cells and neighbors

For a derivative-closed family of nonzero polynomials:

* at a point cell (a level set of `sgn` with a single point) some member vanishes, and on an
  interval cell every member is nonzero;
* for `t` in an interval cell, either no root lies below `t` (the cell extends to `-∞`) or the
  largest root `α` below `t` is the unique point of a point cell adjacent to the cell on the left,
  and the sign vector is the cell's on `(α, t]`; symmetrically on the right;
* adjacent cells are unique.
-/

namespace TS

open Polynomial Set

variable {G : Type*} [DecidableEq G] {S : Finset G} {P : G → ℝ[X]}

/-- Members are nonzero polynomials. -/
def NonzeroOn (S : Finset G) (P : G → ℝ[X]) : Prop := ∀ g ∈ S, P g ≠ 0

/-- `π` is a point cell. -/
def IsPt (S : Finset G) (P : G → ℝ[X]) (π : G → SignType) : Prop := Occ S P π ∧ ¬ Before S P π π

/-- Adjacency on the left relative to an abstract order `B`. -/
def AdjP (B : (G → SignType) → (G → SignType) → Prop) (π ε : G → SignType) : Prop :=
  B π ε ∧ π ≠ ε ∧ ∀ ρ, B π ρ → B ρ ε → ρ = π ∨ ρ = ε

/-- `π` is immediately to the left of `ε`. -/
abbrev Adj (S : Finset G) (P : G → ℝ[X]) (π ε : G → SignType) : Prop := AdjP (Before S P) π ε

/-- The (finite) set of roots of the members. -/
noncomputable def rootSet (S : Finset G) (P : G → ℝ[X]) : Finset ℝ :=
  S.biUnion fun g => (P g).roots.toFinset

omit [DecidableEq G] in
theorem mem_rootSet {z : ℝ} : z ∈ rootSet S P ↔ ∃ g ∈ S, P g ≠ 0 ∧ eval z (P g) = 0 := by
  simp only [rootSet, Finset.mem_biUnion, Multiset.mem_toFinset]
  constructor
  · rintro ⟨g, hg, hz⟩
    have hg0 : P g ≠ 0 := by
      rintro h
      rw [h] at hz
      simp at hz
    exact ⟨g, hg, hg0, (mem_roots hg0).mp hz⟩
  · rintro ⟨g, hg, hg0, hz⟩
    exact ⟨g, hg, (mem_roots hg0).mpr hz⟩

/-- Without roots of the members on a preconnected set, the sign vector is constant there. -/
theorem sgn_eq_of_no_root_mem {I : Set ℝ} (hI : IsPreconnected I)
    (h : ∀ z ∈ I, z ∉ rootSet S P) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) : sgn S P s = sgn S P t := by
  funext g
  by_cases hg : g ∈ S
  · rw [sgn_apply_of_mem hg, sgn_apply_of_mem hg]
    by_cases hg0 : P g = 0
    · simp [hg0]
    · refine sign_eq_of_no_root hI (fun z hz hz0 => h z hz ?_) hs ht
      exact mem_rootSet.mpr ⟨g, hg, hg0, hz0⟩
  · rw [sgn_apply_of_not_mem hg, sgn_apply_of_not_mem hg]

/-- The sign vector is constant on the convex hull of two points of a level set. -/
theorem sgn_eq_of_mem_Icc (hS : DerivClosed S P) {ε : G → SignType} {t₁ t₂ t : ℝ}
    (h₁ : sgn S P t₁ = ε) (h₂ : sgn S P t₂ = ε) (ht : t ∈ Icc t₁ t₂) : sgn S P t = ε := by
  have := sgn_eq_of_between hS (h₁.trans h₂.symm) ht.1 ht.2
  rw [this, h₁]

/-- At a point cell some member vanishes. -/
theorem IsPt.exists_zero {π : G → SignType} (hπ : IsPt S P π) {α : ℝ} (hα : sgn S P α = π) :
    ∃ g ∈ S, π g = 0 := by
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ t in nhds α, sgn S P t = π := by
    have : ∀ g ∈ S, ∀ᶠ t in nhds α, SignType.sign (eval t (P g)) = π g := by
      intro g hg
      have hne : eval α (P g) ≠ 0 := by
        intro h0
        apply hcon g hg
        rw [← hα, sgn_apply_of_mem hg, h0, sign_zero]
      have := eventually_sign_eq_nhds hne
      rw [← sgn_apply_of_mem (P := P) (t := α) hg, hα] at this
      exact this
    rw [← Filter.eventually_all_finset] at this
    filter_upwards [this] with t ht
    funext g
    by_cases hg : g ∈ S
    · rw [sgn_apply_of_mem hg]
      exact ht g hg
    · rw [sgn_apply_of_not_mem hg, ← hα, sgn_apply_of_not_mem hg]
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  apply hπ.2
  refine ⟨α, α + δ / 2, by linarith, hα, hball ?_⟩
  rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (by linarith)]
  linarith

/-- On an interval cell every member is nonzero. -/
theorem before_self_ne_zero (hS : DerivClosed S P) (hnz : NonzeroOn S P) {ε : G → SignType}
    (hε : Before S P ε ε) {g : G} (hg : g ∈ S) : ε g ≠ 0 := by
  obtain ⟨t₁, t₂, hlt, h₁, h₂⟩ := hε
  intro h0
  apply hnz g hg
  apply eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono ?_ (Set.Icc_infinite hlt)
  intro t ht
  have := congrFun (sgn_eq_of_mem_Icc hS h₁ h₂ ht) g
  rw [sgn_apply_of_mem hg, h0, sign_eq_zero_iff] at this
  exact this

/-- A cell containing a root is a point cell with that root as its unique point. -/
theorem isPt_of_root (hS : DerivClosed S P) (hnz : NonzeroOn S P) {α : ℝ}
    (hα : α ∈ rootSet S P) : IsPt S P (sgn S P α) ∧ ∀ s, sgn S P s = sgn S P α → s = α := by
  obtain ⟨g, hg, hg0, hz⟩ := mem_rootSet.mp hα
  have hnb : ¬ Before S P (sgn S P α) (sgn S P α) := by
    intro hb
    apply before_self_ne_zero hS hnz hb hg
    rw [sgn_apply_of_mem hg, hz, sign_zero]
  refine ⟨⟨⟨α, rfl⟩, hnb⟩, fun s hs => ?_⟩
  by_contra hne
  apply hnb
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨s, α, h, hs, rfl⟩
  · exact ⟨α, s, h, rfl, hs⟩

/-- Adjacent cells on the left are unique. -/
theorem Adj.unique {π₁ π₂ ε : G → SignType} (h₁ : Adj S P π₁ ε)
    (h₂ : Adj S P π₂ ε) : π₁ = π₂ := by
  by_contra hne
  rcases before_or_before h₁.1.occ_left h₂.1.occ_left hne with h | h
  · rcases h₁.2.2 π₂ h h₂.1 with h' | h'
    · exact hne h'.symm
    · exact h₂.2.1 h'
  · rcases h₂.2.2 π₁ h h₁.1 with h' | h'
    · exact hne h'
    · exact h₁.2.1 h'

/-- **Left neighbor.**  For `t` in an interval cell `ε`: either the cell extends to `-∞`, or there
is a point cell `π` adjacent on the left, with unique point `α < t`, and the sign vector is `ε`
on `(α, t]`. -/
theorem left_neighbor (hS : DerivClosed S P) (hnz : NonzeroOn S P) {ε : G → SignType}
    (hε : Before S P ε ε) {t : ℝ} (ht : sgn S P t = ε) :
    (∀ s, s ≤ t → sgn S P s = ε) ∨
    ∃ α π, α < t ∧ sgn S P α = π ∧ IsPt S P π ∧ Adj S P π ε ∧
      (∀ s, α < s → s ≤ t → sgn S P s = ε) ∧ (∀ s, sgn S P s = π → s = α) := by
  classical
  have ht_root : t ∉ rootSet S P := by
    intro hroot
    obtain ⟨g, hg, hg0, hz⟩ := mem_rootSet.mp hroot
    apply before_self_ne_zero hS hnz hε hg
    rw [← ht, sgn_apply_of_mem hg, hz, sign_zero]
  set Z := (rootSet S P).filter (fun z => z < t) with hZ
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · left
    intro s hs
    refine (sgn_eq_of_no_root_mem (I := Iic t) isPreconnected_Iic ?_ hs (Set.mem_Iic.mpr le_rfl)).trans ht
    intro z hz hzr
    rcases (Set.mem_Iic.mp hz).lt_or_eq with hlt | rfl
    · have : z ∈ Z := by
        rw [hZ, Finset.mem_filter]
        exact ⟨hzr, hlt⟩
      rw [hZe] at this
      exact absurd this (Finset.notMem_empty z)
    · exact ht_root hzr
  · right
    set α := Z.max' hZne with hα
    have hαZ : α ∈ Z := Z.max'_mem hZne
    have hαroot : α ∈ rootSet S P := (Finset.mem_filter.mp hαZ).1
    have hαt : α < t := (Finset.mem_filter.mp hαZ).2
    -- no roots in `(α, t]`
    have hnoroot : ∀ z ∈ Ioc α t, z ∉ rootSet S P := by
      intro z hz hzr
      rcases hz.2.lt_or_eq with hlt | rfl
      · have : z ∈ Z := by
          rw [hZ, Finset.mem_filter]
          exact ⟨hzr, hlt⟩
        exact absurd (Z.le_max' z this) (not_le.mpr hz.1)
      · exact ht_root hzr
    have hconst : ∀ s, α < s → s ≤ t → sgn S P s = ε := fun s h1 h2 =>
      (sgn_eq_of_no_root_mem isPreconnected_Ioc hnoroot ⟨h1, h2⟩ ⟨hαt, le_rfl⟩).trans ht
    obtain ⟨hpt, huniq⟩ := isPt_of_root hS hnz hαroot
    have hne : sgn S P α ≠ ε := by
      intro h
      exact hpt.2 (h ▸ hε)
    refine ⟨α, sgn S P α, hαt, rfl, hpt, ⟨⟨α, t, hαt, rfl, ht⟩, hne, ?_⟩, hconst, huniq⟩
    intro ρ hπρ hρε
    obtain ⟨s₁, s₂, hs, hs₁, hs₂⟩ := hπρ
    have hs₁α : s₁ = α := huniq s₁ hs₁
    subst hs₁α
    by_cases hρ : ρ = ε
    · exact Or.inr hρ
    · have := lt_of_before hS hρε hρ hs₂ ht
      exact Or.inr ((hconst s₂ hs this.le).symm.trans hs₂ |>.symm ▸ rfl)

/-- Adjacency on the right relative to an abstract order `B`. -/
def AdjRP (B : (G → SignType) → (G → SignType) → Prop) (ε π : G → SignType) : Prop :=
  B ε π ∧ ε ≠ π ∧ ∀ ρ, B ε ρ → B ρ π → ρ = ε ∨ ρ = π

/-- `π` is immediately to the right of `ε`. -/
abbrev AdjR (S : Finset G) (P : G → ℝ[X]) (ε π : G → SignType) : Prop := AdjRP (Before S P) ε π

theorem AdjR.unique {ε π₁ π₂ : G → SignType} (h₁ : AdjR S P ε π₁)
    (h₂ : AdjR S P ε π₂) : π₁ = π₂ := by
  by_contra hne
  rcases before_or_before h₁.1.occ_right h₂.1.occ_right hne with h | h
  · rcases h₂.2.2 π₁ h₁.1 h with h' | h'
    · exact h₁.2.1 h'.symm
    · exact hne h'
  · rcases h₁.2.2 π₂ h₂.1 h with h' | h'
    · exact h₂.2.1 h'.symm
    · exact hne h'.symm

/-- **Right neighbor.** -/
theorem right_neighbor (hS : DerivClosed S P) (hnz : NonzeroOn S P) {ε : G → SignType}
    (hε : Before S P ε ε) {t : ℝ} (ht : sgn S P t = ε) :
    (∀ s, t ≤ s → sgn S P s = ε) ∨
    ∃ β π, t < β ∧ sgn S P β = π ∧ IsPt S P π ∧ AdjR S P ε π ∧
      (∀ s, t ≤ s → s < β → sgn S P s = ε) ∧ (∀ s, sgn S P s = π → s = β) := by
  classical
  have ht_root : t ∉ rootSet S P := by
    intro hroot
    obtain ⟨g, hg, hg0, hz⟩ := mem_rootSet.mp hroot
    apply before_self_ne_zero hS hnz hε hg
    rw [← ht, sgn_apply_of_mem hg, hz, sign_zero]
  set Z := (rootSet S P).filter (fun z => t < z) with hZ
  rcases Z.eq_empty_or_nonempty with hZe | hZne
  · left
    intro s hs
    refine (sgn_eq_of_no_root_mem (I := Ici t) isPreconnected_Ici ?_ hs (Set.mem_Ici.mpr le_rfl)).trans ht
    intro z hz hzr
    rcases (Set.mem_Ici.mp hz).lt_or_eq with hlt | rfl
    · have : z ∈ Z := by
        rw [hZ, Finset.mem_filter]
        exact ⟨hzr, hlt⟩
      rw [hZe] at this
      exact absurd this (Finset.notMem_empty z)
    · exact ht_root hzr
  · right
    set β := Z.min' hZne with hβ
    have hβZ : β ∈ Z := Z.min'_mem hZne
    have hβroot : β ∈ rootSet S P := (Finset.mem_filter.mp hβZ).1
    have htβ : t < β := (Finset.mem_filter.mp hβZ).2
    have hnoroot : ∀ z ∈ Ico t β, z ∉ rootSet S P := by
      intro z hz hzr
      rcases hz.1.lt_or_eq with hlt | rfl
      · have : z ∈ Z := by
          rw [hZ, Finset.mem_filter]
          exact ⟨hzr, hlt⟩
        exact absurd (Z.min'_le z this) (not_le.mpr hz.2)
      · exact ht_root hzr
    have hconst : ∀ s, t ≤ s → s < β → sgn S P s = ε := fun s h1 h2 =>
      (sgn_eq_of_no_root_mem isPreconnected_Ico hnoroot ⟨h1, h2⟩ ⟨le_rfl, htβ⟩).trans ht
    obtain ⟨hpt, huniq⟩ := isPt_of_root hS hnz hβroot
    have hne : ε ≠ sgn S P β := by
      intro h
      exact hpt.2 (h ▸ hε)
    refine ⟨β, sgn S P β, htβ, rfl, hpt, ⟨⟨t, β, htβ, ht, rfl⟩, hne, ?_⟩, hconst, huniq⟩
    intro ρ hερ hρπ
    obtain ⟨s₁, s₂, hs, hs₁, hs₂⟩ := hρπ
    have hs₂β : s₂ = β := huniq s₂ hs₂
    subst hs₂β
    by_cases hρ : ρ = ε
    · exact Or.inl hρ
    · have := lt_of_before hS hερ (Ne.symm hρ) ht hs₁
      exact Or.inl (((hconst s₁ this.le hs).symm.trans hs₁).symm ▸ rfl)

/-- If the cell extends to `-∞`, nothing is adjacent on the left. -/
theorem not_adj_of_unbounded_below (hS : DerivClosed S P) {ε : G → SignType} {t : ℝ}
    (ht : sgn S P t = ε) (hall : ∀ s, s ≤ t → sgn S P s = ε) {π : G → SignType}
    (hπ : Adj S P π ε) : False := by
  obtain ⟨s₁, s₂, hs, h₁, h₂⟩ := hπ.1
  apply hπ.2.1
  rcases le_or_gt s₁ t with hle | hgt
  · rw [← h₁, hall s₁ hle]
  · rw [← h₁, sgn_eq_of_mem_Icc hS ht h₂ ⟨hgt.le, hs.le⟩]

/-- If the cell extends to `+∞`, nothing is adjacent on the right. -/
theorem not_adjR_of_unbounded_above (hS : DerivClosed S P) {ε : G → SignType} {t : ℝ}
    (ht : sgn S P t = ε) (hall : ∀ s, t ≤ s → sgn S P s = ε) {π : G → SignType}
    (hπ : AdjR S P ε π) : False := by
  obtain ⟨s₁, s₂, hs, h₁, h₂⟩ := hπ.1
  apply hπ.2.1
  rcases le_or_gt t s₂ with hle | hgt
  · rw [← h₂, hall s₂ hle]
  · rw [← h₂, sgn_eq_of_mem_Icc hS h₁ ht ⟨hs.le, hgt.le⟩]

end TS
