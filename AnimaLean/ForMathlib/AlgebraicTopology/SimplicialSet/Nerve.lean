import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

universe v u

namespace CategoryTheory

namespace Nerve

open Limits MonoidalCategory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Two maps into the nerve of a category with at most one object and at most one morphism
between any two objects are equal. -/
lemma hom_ext_of_subsingleton [Subsingleton C] [Quiver.IsThin C] {X : SSet.{max u v}}
    (f g : X ⟶ nerve C) : f = g := by
  ext n x
  exact Subsingleton.elim _ _

/-- The nerve of a category with one object and at most one morphism is a terminal SSet -/
def isTerminal [Unique C] [Quiver.IsThin C] : IsTerminal (nerve C) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ { app _ := TypeCat.ofHom fun _ ↦ (Functor.const _).obj default })
    (fun _ _ ↦ hom_ext_of_subsingleton _ _)



@[simp]
lemma nerveMap_app_obj (F : C ⥤ D)
    {n : SimplexCategoryᵒᵖ} (x : (nerve C).obj n) (t : Fin (n.unop.len + 1)) :
    ((nerveMap F).app n x).obj t = F.obj (x.obj t) :=
  rfl

variable {α β : Type u} [Preorder α] [Preorder β]

/-- An order isomorphism induces an isomorphism of nerves. -/
@[simps]
def isoOfOrderIso (e : α ≃o β) : nerve α ≅ nerve β where
  hom := nerveMap e.monotone.functor
  inv := nerveMap e.symm.monotone.functor
  hom_inv_id := by
    ext n x
    exact e.symm_apply_apply _
  inv_hom_id := by
    ext n x
    exact e.apply_symm_apply _

@[simp]
lemma isoOfOrderIso_hom_app_obj (e : α ≃o β) {n : SimplexCategoryᵒᵖ} (x : (nerve α).obj n)
    (t : Fin (n.unop.len + 1)) : ((isoOfOrderIso e).hom.app n x).obj t = e (x.obj t) :=
  rfl

end Nerve

end CategoryTheory
