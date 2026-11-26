import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

universe v u

open CategoryTheory MonoidalCategory Simplicial

namespace CategoryTheory

namespace EnrichedFunctor

variable {V : Type*} [Category V] [MonoidalCategory V] {A B C D : Type*} [EnrichedCategory V A]
  [EnrichedCategory V B] [EnrichedCategory V C] [EnrichedCategory V D]

lemma comp_assoc (F : EnrichedFunctor V A B) (G : EnrichedFunctor V B C)
    (H : EnrichedFunctor V C D) : (F.comp V G).comp V H = F.comp V (G.comp V H) :=
  EnrichedFunctor.ext V (fun _ ↦ rfl) fun _ _ ↦ (Category.comp_id _).trans (Category.assoc _ _ _)

lemma id_comp (F : EnrichedFunctor V A B) : (EnrichedFunctor.id V A).comp V F = F :=
  EnrichedFunctor.ext V (fun _ ↦ rfl) fun _ _ ↦ (Category.comp_id _).trans (Category.id_comp _)

lemma comp_id (F : EnrichedFunctor V A B) : F.comp V (EnrichedFunctor.id V B) = F :=
  EnrichedFunctor.ext V (fun _ ↦ rfl) fun _ _ ↦ (Category.comp_id _).trans (Category.comp_id _)

end EnrichedFunctor

namespace SimplicialCategory

variable {C : Type u} [Category.{v} C] [SimplicialCategory C] {n : SimplexCategoryᵒᵖ}

/-- Composition of simplices of hom-objects. -/
def comp {A B D : C} (s : (sHom A B).obj n) (t : (sHom B D).obj n) : (sHom A D).obj n :=
  (eComp SSet A B D).app n (s, t)

/-- The identity simplex of `sHom A A`. -/
abbrev idS (A : C) (n : SimplexCategoryᵒᵖ) : (sHom A A).obj n :=
  (eId SSet A).app n PUnit.unit

lemma comp_assoc {A B D E : C} (s : (sHom A B).obj n) (t : (sHom B D).obj n)
    (w : (sHom D E).obj n) : comp (comp s t) w = comp s (comp t w) :=
  congr_arg (fun f ↦ f.app n (s, (t, w))) (e_assoc SSet A B D E)

lemma idS_comp {A B : C} (s : (sHom A B).obj n) : comp (idS A n) s = s :=
  congr_arg (fun f ↦ f.app n s) (e_id_comp SSet A B)

lemma comp_idS {A B : C} (s : (sHom A B).obj n) : comp s (idS B n) = s :=
  congr_arg (fun f ↦ f.app n s) (e_comp_id SSet A B)

lemma comp_map {n' : SimplexCategoryᵒᵖ} {A B D : C} (s : (sHom A B).obj n) (t : (sHom B D).obj n)
    (f : n ⟶ n') :
    (sHom A D).map f (comp s t) = comp ((sHom A B).map f s) ((sHom B D).map f t) :=
  (NatTrans.naturality_apply (eComp SSet A B D) f _).symm

lemma idS_map {n' : SimplexCategoryᵒᵖ} (A : C) (f : n ⟶ n') :
    (sHom A A).map f (idS A n) = idS A n' :=
  (NatTrans.naturality_apply (eId SSet A) f PUnit.unit).symm


/-- The category of `m`-simplices of a simplicial category `C`: the objects of `C`, and the
`m`-simplices of `sHom A B` as morphisms `A ⟶ B`. -/
@[kerodon 00JT]
structure Level (C : Type u) [Category.{v} C] [SimplicialCategory C]
    (m : SimplexCategoryᵒᵖ) : Type u where
  /-- The underlying object of `C`. -/
  as : C

instance (m : SimplexCategoryᵒᵖ) : Category.{v} (Level C m) where
  Hom A B := (sHom A.as B.as).obj m
  id A := idS A.as m
  comp s t := comp s t
  id_comp := idS_comp
  comp_id := comp_idS
  assoc := comp_assoc

end SimplicialCategory

end CategoryTheory
