import Mathlib.AlgebraicTopology.Quasicategory.Basic
import Mathlib.AlgebraicTopology.SimplicialNerve
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialCategory.LocallyKan

universe v u

namespace CategoryTheory

open SimplicialCategory

variable (C : Type u) [Category.{v} C] [SimplicialCategory C]

/- Here we will need to prove **Cordier–Porter**: the simplicial nerve of a locally Kan simplicial category is a
quasicategory. -/

@[kerodon 00LJ]
instance SimplicialNerve.quasicategory [LocallyKan C] :
    SSet.Quasicategory (SimplicialNerve C) := by
  sorry

end CategoryTheory
