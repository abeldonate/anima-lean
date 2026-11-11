import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

open CategoryTheory HomotopicalAlgebra

namespace SSet.anodyneExtensions

/-- If `e : X ⟶ Y` and `r : Y ⟶ X` satisfy `e ≫ r = 𝟙 X` and restrict to maps between the
subcomplexes `A` and `B`, then `A.ι` is a retract of `B.ι`; so it is anodyne if `B.ι` is. -/
lemma of_retract_ι.{w} {X Y : SSet.{w}} {A : X.Subcomplex} {B : Y.Subcomplex}
    (hB : anodyneExtensions B.ι) (e : X ⟶ Y) (r : Y ⟶ X) (her : e ≫ r = 𝟙 X)
    (he : A ≤ B.preimage e) (hr : B ≤ A.preimage r) : anodyneExtensions A.ι :=
  anodyneExtensions.of_retract
    { i := Arrow.homMk' (Subcomplex.lift (A.ι ≫ e) (by rintro n _ ⟨x, rfl⟩; exact he n x.2)) e rfl
      r := Arrow.homMk' (Subcomplex.lift (B.ι ≫ r) (by rintro n _ ⟨y, rfl⟩; exact hr n y.2)) r rfl
      retract := by
        ext n x
        · exact Subtype.ext (congr_arg (fun f ↦ f.app n x.1) her)
        · exact congr_arg (fun f ↦ f.app n x) her } hB

/-- If `f : A ⟶ B` is anodyne and `X` is a Kan complex, every map `A ⟶ X` extends along `f`. -/
lemma exists_extension.{w} {A B X : SSet.{w}} {f : A ⟶ B}
    (hf : anodyneExtensions f) [KanComplex X] (g : A ⟶ X) : ∃ h : B ⟶ X, f ≫ h = g := by
  have := hf (Limits.terminal.from X)
    (by rw [← fibration_iff]; infer_instance)
  exact ⟨(CommSq.mk (Limits.terminal.hom_ext (g ≫ Limits.terminal.from X)
    (f ≫ Limits.terminal.from B))).lift, by simp⟩

end SSet.anodyneExtensions
