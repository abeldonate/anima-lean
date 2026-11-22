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

end SimplicialCategory

end CategoryTheory
