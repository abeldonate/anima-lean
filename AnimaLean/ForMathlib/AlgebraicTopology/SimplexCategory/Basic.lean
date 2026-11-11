import Mathlib.AlgebraicTopology.SimplexCategory.Basic

open CategoryTheory Simplicial

namespace SimplexCategory

variable {n : ℕ}

/-- A retraction of the coface `δ j`. -/
lemma exists_retraction_δ (j : Fin (n + 2)) : ∃ s : ⦋n + 1⦌ ⟶ ⦋n⦌, δ j ≫ s = 𝟙 _ := by
  by_cases hj : j = Fin.last _
  · exact ⟨σ (Fin.last _), δ_comp_σ_succ' (by simp [hj])⟩
  · exact ⟨σ (j.castPred hj), δ_comp_σ_self' (by simp)⟩

/-- There is an endomorphism of `[n + 2]` which avoids `j` and `k` and fixes the other vertices:
a retraction onto the face missing `j` and `k`. -/
lemma exists_collapse (j k : Fin (n + 3)) :
    ∃ g : ⦋n + 2⦌ ⟶ ⦋n + 2⦌, (∀ t, g.toOrderHom t ≠ j ∧ g.toOrderHom t ≠ k) ∧
      ∀ t, t ≠ j → t ≠ k → g.toOrderHom t = t := by
  obtain ⟨s, hs⟩ := exists_retraction_δ k
  have hs' (t) : s.toOrderHom (k.succAbove t) = t := congr_arg (fun f ↦ f.toOrderHom t) hs
  by_cases hjk : j = k
  · subst hjk
    refine ⟨s ≫ δ j, fun t ↦ ⟨Fin.succAbove_ne j _, Fin.succAbove_ne j _⟩, fun t ht _ ↦ ?_⟩
    obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq ht
    exact congr_arg j.succAbove (hs' t)
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hjk
    obtain ⟨r, hr⟩ := exists_retraction_δ j
    refine ⟨s ≫ r ≫ δ j ≫ δ k, fun t ↦ ⟨fun h ↦ ?_, Fin.succAbove_ne k _⟩, fun t htj htk ↦ ?_⟩
    · exact Fin.succAbove_ne j _ (Fin.succAbove_right_injective h)
    · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq htk
      obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq (fun h ↦ htj (h ▸ rfl) : t ≠ j)
      change k.succAbove (j.succAbove (r.toOrderHom (s.toOrderHom _))) = _
      rw [hs', show r.toOrderHom (j.succAbove t) = t from congr_arg (fun f ↦ f.toOrderHom t) hr]

/-- An endomorphism of `[n + 2]` which avoids `j` and `k` and fixes the other vertices. -/
noncomputable def collapse (j k : Fin (n + 3)) : ⦋n + 2⦌ ⟶ ⦋n + 2⦌ :=
  (exists_collapse j k).choose

lemma collapse_ne (j k t : Fin (n + 3)) :
    (collapse j k).toOrderHom t ≠ j ∧ (collapse j k).toOrderHom t ≠ k :=
  (exists_collapse j k).choose_spec.1 t

lemma collapse_apply {j k t : Fin (n + 3)} (hj : t ≠ j) (hk : t ≠ k) :
    (collapse j k).toOrderHom t = t :=
  (exists_collapse j k).choose_spec.2 t hj hk

lemma comp_collapse {p : ℕ} (d : ⦋p⦌ ⟶ ⦋n + 2⦌) {j k : Fin (n + 3)}
    (hd : ∀ t, d.toOrderHom t ≠ j ∧ d.toOrderHom t ≠ k) : d ≫ collapse j k = d := by
  ext t : 3
  exact collapse_apply (hd t).1 (hd t).2

end SimplexCategory
