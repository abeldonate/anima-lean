import Mathlib.CategoryTheory.Adjunction.Basic
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialNerve.Thickening

universe u

open CategoryTheory SimplicialCategory

namespace CategoryTheory

/-- The category of small simplicial categories and simplicial functors. -/
structure SimplicialCat : Type (u + 1) where
  /-- The type of objects. -/
  α : Type u
  [category : Category.{u} α]
  [simplicialCategory : SimplicialCategory α]

namespace SimplicialCat

attribute [instance] category simplicialCategory

instance : CoeSort SimplicialCat.{u} (Type u) := ⟨α⟩

instance : Category.{u} SimplicialCat.{u} where
  Hom C D := EnrichedFunctor SSet.{u} C D
  id C := EnrichedFunctor.id SSet C
  comp F G := F.comp SSet G
  id_comp _ := enrichedFunctor_ext fun _ _ _ _ ↦ rfl
  comp_id _ := enrichedFunctor_ext fun _ _ _ _ ↦ rfl
  assoc _ _ _ := enrichedFunctor_ext fun _ _ _ _ ↦ rfl

/-- The simplicial nerve (homotopy coherent nerve), as a functor from small simplicial categories
to simplicial sets. -/
def simplicialNerve : SimplicialCat.{u} ⥤ SSet.{u} where
  obj C := SimplicialNerve C
  map F := SimplicialNerve.map F
  map_id _ := by
    ext n E
    exact enrichedFunctor_ext fun _ _ _ _ ↦ rfl
  map_comp _ _ := by
    ext n E
    exact enrichedFunctor_ext fun _ _ _ _ ↦ rfl

end SimplicialCat

end CategoryTheory

namespace SSet

open SimplicialCat

/-- The path category of a simplicial set, as a functor to small simplicial categories. -/
def thickening : SSet.{u} ⥤ SimplicialCat.{u} :=
  Adjunction.leftAdjointOfEquiv (G := simplicialNerve) (F_obj := fun S ↦ ⟨S.Thickening⟩)
    (fun S D ↦ Thickening.homEquiv S D) (fun S _ _ G F ↦
      (congr_arg (Thickening.unit S ≫ ·) (simplicialNerve.map_comp F G)).trans
        (Category.assoc _ _ _).symm)

/-- The path category functor is left adjoint to the simplicial nerve (homotopy coherent
nerve). -/
@[kerodon 00L4]
def thickeningAdjunction : thickening.{u} ⊣ simplicialNerve :=
  Adjunction.adjunctionOfEquivLeft _ _

end SSet
