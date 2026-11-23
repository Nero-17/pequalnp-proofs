import Mathlib

theorem PEqualNP.Outside.L_meta_683 : ∀ (F : Type) [Field F] [Fintype F] [CharP F 2],
    ∃ b : F, ∀ x : F, x ^ 2 + b * x + 1 ≠ 0 := by
  intro F _ _ _
  classical
  by_contra! all_have_roots
  let coefficient (x : F) := if x = 0 then -(1 + 1) else -(x ^ 2 + 1) / x
  have onto : Function.Surjective coefficient := by
    intro b
    obtain ⟨x, root⟩ := all_have_roots b
    have nonzero : x ≠ 0 := by
      rintro rfl
      simp at root
    refine ⟨x, ?_⟩
    simp only [coefficient, if_neg nonzero]
    apply (div_eq_iff nonzero).2
    linear_combination -root
  have same : coefficient 0 = coefficient 1 := by simp [coefficient]
  exact zero_ne_one ((Finite.injective_iff_surjective.mpr onto) same)
