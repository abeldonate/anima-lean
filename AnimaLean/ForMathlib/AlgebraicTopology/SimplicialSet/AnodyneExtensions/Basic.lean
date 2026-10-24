import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

open CategoryTheory HomotopicalAlgebra

namespace SSet.anodyneExtensions

/-- Anodyne inclusions are stable under preimage along an isomorphism. -/
lemma preimage_ι.{w} {X Y : SSet.{w}} (e : X ≅ Y) (B : Y.Subcomplex)
    (hB : anodyneExtensions B.ι) : anodyneExtensions (B.preimage e.hom).ι := by
  refine ((anodyneExtensions).arrow_mk_iso_iff (Arrow.isoMk (?_ : _ ≅ _) e.symm ?_)).1 hB
  · exact
      { hom := Subcomplex.lift (B.ι ≫ e.inv) (by
          rintro n _ ⟨b, rfl⟩
          change e.hom.app n (e.inv.app n b.1) ∈ B.obj n
          simp [← NatTrans.comp_app_apply])
        inv := B.fromPreimage e.hom
        hom_inv_id := by
          ext n ⟨b, hb⟩
          apply Subtype.ext
          change e.hom.app n (e.inv.app n b) = b
          simp
        inv_hom_id := by
          ext n ⟨x, hx⟩
          apply Subtype.ext
          change e.inv.app n (e.hom.app n x) = x
          simp }
  · rfl

/-- If `f : A ⟶ B` is anodyne and `X` is a Kan complex, every map `A ⟶ X` extends along `f`. -/
lemma exists_extension.{w} {A B X : SSet.{w}} {f : A ⟶ B}
    (hf : anodyneExtensions f) [KanComplex X] (g : A ⟶ X) : ∃ h : B ⟶ X, f ≫ h = g := by
  have := hf (Limits.terminal.from X)
    (by rw [← fibration_iff]; infer_instance)
  exact ⟨(CommSq.mk (Limits.terminal.hom_ext (g ≫ Limits.terminal.from X)
    (f ≫ Limits.terminal.from B))).lift, by simp⟩

end SSet.anodyneExtensions
