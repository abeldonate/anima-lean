import Mathlib.AlgebraicTopology.SimplicialSet.Horn

open CategoryTheory Simplicial

namespace SSet

/-- An `m`-simplex of `Δ¹` lies in the horn `Λ[1, b]` iff it is constant with value `b`. -/
lemma mem_horn_one_iff.{w} (b : Fin 2) {m : SimplexCategoryᵒᵖ}
    (x : (stdSimplex.{w}.obj ⦋1⦌).obj m) :
    x ∈ (horn.{w} 1 b).obj m ↔ ∀ t, stdSimplex.asOrderHom x t = b := by
  rw [mem_horn_iff, Ne, Set.eq_univ_iff_forall]
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, not_forall, not_or, not_exists]
  exact ⟨fun ⟨c, hc, hcb⟩ t ↦ by grind, fun h ↦ ⟨b.rev, fun t ↦ by grind, by grind⟩⟩

end SSet
