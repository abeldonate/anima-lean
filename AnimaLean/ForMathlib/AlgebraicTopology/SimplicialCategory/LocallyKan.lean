import Mathlib.AlgebraicTopology.SimplicialCategory.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex

universe v u

namespace CategoryTheory

namespace SimplicialCategory

open SSet

variable (C : Type u) [Category.{v} C] [SimplicialCategory C]

/-- A simplicial category is *locally Kan* if all the `sHom X Y` are Kan complexes. -/
@[kerodon 00JY]
class LocallyKan : Prop where
  kanComplex_sHom (X Y : C) : KanComplex (sHom X Y)

attribute [instance] LocallyKan.kanComplex_sHom

lemma locallyKan_iff : LocallyKan C ↔ ∀ X Y : C, KanComplex (sHom X Y) :=
  ⟨fun h ↦ h.kanComplex_sHom, fun h ↦ ⟨h⟩⟩

/-- A full subcategory of a locally Kan simplicial category is locally Kan. -/
instance [LocallyKan C] (P : ObjectProperty C) : LocallyKan P.FullSubcategory where
  kanComplex_sHom X Y := inferInstanceAs (KanComplex (sHom X.obj Y.obj))

end SimplicialCategory

end CategoryTheory
