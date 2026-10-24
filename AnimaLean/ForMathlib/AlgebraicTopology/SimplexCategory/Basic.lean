import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open CategoryTheory Simplicial

namespace SimplexCategory

variable {n : ℕ}

/-- A retraction of the coface `δ j`. -/
lemma exists_retraction_δ (j : Fin (n + 3)) :
    ∃ s : ⦋n + 2⦌ ⟶ ⦋n + 1⦌, δ j ≫ s = 𝟙 _ := by
  by_cases hj : j = Fin.last _
  · exact ⟨σ (Fin.last _), δ_comp_σ_succ' (by simp [hj])⟩
  · exact ⟨σ (j.castPred hj), δ_comp_σ_self' (by simp)⟩

/-- A degeneracy followed by the face `δ j`: the identity of `[n + 2]` except at `j`. -/
noncomputable def collapse (j : Fin (n + 3)) : ⦋n + 2⦌ ⟶ ⦋n + 2⦌ :=
  (exists_retraction_δ j).choose ≫ δ j

lemma collapse_apply_of_ne {j t : Fin (n + 3)} (ht : t ≠ j) : (collapse j).toOrderHom t = t := by
  obtain ⟨t', rfl⟩ := Fin.exists_succAbove_eq ht
  exact congr_arg (δ j).toOrderHom
    (congr_arg (fun f ↦ f.toOrderHom t') (exists_retraction_δ j).choose_spec)

lemma comp_collapse {p : ℕ} (d : ⦋p⦌ ⟶ ⦋n + 2⦌) {j : Fin (n + 3)} (hd : ∀ t, d.toOrderHom t ≠ j) :
    d ≫ collapse j = d := by
  ext t : 3
  exact collapse_apply_of_ne (hd t)

/-- A codimension `2` face of `[n + 2]` missing exactly `j` and `k`. -/
lemma exists_codim_two {j k : Fin (n + 3)} (hjk : j ≠ k) :
    ∃ d : ⦋n⦌ ⟶ ⦋n + 2⦌, Mono d ∧ (∀ t, d.toOrderHom t ≠ j ∧ d.toOrderHom t ≠ k) ∧
      ∀ c, c ≠ j → c ≠ k → c ∈ Set.range d.toOrderHom := by
  obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq hjk
  refine ⟨δ j' ≫ δ k, inferInstance, fun t ↦ ⟨?_, ?_⟩, ?_⟩
  · change k.succAbove (j'.succAbove t) ≠ j
    rw [← hj']
    exact fun h ↦ Fin.succAbove_ne j' t (Fin.succAbove_right_injective h)
  · exact Fin.succAbove_ne k _
  · intro c hcj hck
    obtain ⟨c', rfl⟩ := Fin.exists_succAbove_eq hck
    have : c' ≠ j' := by rintro rfl; exact hcj hj'
    obtain ⟨c'', rfl⟩ := Fin.exists_succAbove_eq this
    exact ⟨c'', rfl⟩

end SimplexCategory
