import TS

/-! Axiom audit: every statement should depend only on `propext`, `Classical.choice`, `Quot.sound`. -/

-- Pseudo-division and the closure
#print axioms TS.exists_pseudoDiv
#print axioms TS.isClosedFam_closure
#print axioms TS.subset_closure
-- Cells
#print axioms TS.sgn_eq_of_between
#print axioms TS.Before.antisymm
#print axioms TS.left_neighbor
#print axioms TS.right_neighbor
-- The Hörmander step
#print axioms TS.StepHyp.ptSign_eq
#print axioms TS.StepHyp.signs_cell
#print axioms TS.StepHyp.occ_iff
#print axioms TS.StepHyp.before_iff
-- The parametric induction
#print axioms TS.stepHyp
#print axioms TS.profile_eq_Ψ
#print axioms TS.semialg_profile
#print axioms TS.semialg_exists_sign
-- Semialgebraic sets and the Tarski–Seidenberg theorem
#print axioms TS.Semialg.exists_cells
#print axioms TS.eval_elim
#print axioms TS.IsSemialgebraic.image_proj
#print axioms TS.IsSemialgebraic.reindex
#print axioms TS.IsSemialgebraic.image_projInl
