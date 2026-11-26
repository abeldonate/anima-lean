import Mathlib.AlgebraicTopology.SimplicialNerve
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic

universe v u

open CategoryTheory

namespace CategoryTheory

/-- The category `Cat_Δ` of simplicial categories and simplicial functors. -/
@[kerodon 00K1]
structure SimplicialCat : Type (max (u + 1) (v + 1)) where
  /-- The type of objects. -/
  α : Type u
  /-- The underlying category. -/
  [category : Category.{v} α]
  /-- The simplicial enrichment. -/
  [simplicialCategory : SimplicialCategory α]

namespace SimplicialCat

-- This line lets Lean infer `Category C.α` and `SimplicialCategory C.α` for `C : SimplicialCat`
attribute [instance] category simplicialCategory

instance : CoeSort SimplicialCat.{v, u} (Type u) := ⟨α⟩

instance : Category.{max u v} SimplicialCat.{v, u} where
  Hom C D := EnrichedFunctor SSet.{v} C D
  id C := EnrichedFunctor.id SSet C
  comp F G := F.comp SSet G
  id_comp := EnrichedFunctor.id_comp
  comp_id := EnrichedFunctor.comp_id
  assoc := EnrichedFunctor.comp_assoc

end SimplicialCat

namespace SimplicialNerve

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
  {D : Type u} [Category.{v} D] [SimplicialCategory D]

/-- The simplicial nerve is functorial in simplicial functors: postcompose. -/
def map (F : EnrichedFunctor SSet.{v} C D) : SimplicialNerve C ⟶ SimplicialNerve D where
  app _ := TypeCat.ofHom fun E ↦ E.comp SSet F
  naturality _ _ _ := by
    ext E
    exact EnrichedFunctor.comp_assoc _ _ _

end SimplicialNerve

namespace SimplicialCat

/-- The homotopy coherent nerve `N^hc : Cat_Δ ⥤ Set_Δ`. -/
@[kerodon 00KU]
def simplicialNerve : SimplicialCat.{v, u} ⥤ SSet.{max u v} where
  obj C := SimplicialNerve C
  map F := SimplicialNerve.map F
  map_id _ := by
    ext _ E
    exact EnrichedFunctor.comp_id E
  map_comp _ _ := by
    ext _ E
    exact (EnrichedFunctor.comp_assoc E _ _).symm

end SimplicialCat

/-- The simplicial thickening of `[k]`, whose simplicial functors to `C` are the `k`-simplices of
the simplicial nerve of `C`. -/
abbrev Th (k : ℕ) := SimplicialThickening (ULift.{v} (Fin (k + 1)))

end CategoryTheory
