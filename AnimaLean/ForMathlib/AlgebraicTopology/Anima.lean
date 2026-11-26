import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialCategory.KanComplex
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialNerve
import Mathlib.AlgebraicTopology.Quasicategory.Basic

universe u

open CategoryTheory

namespace SSet

/-- The anima is the simplicial nerve (homotopy coherent Nerve) of the simplicial category of
Kan complexes. -/
@[kerodon 00TZ]
def anima : SSet.{u + 1} := SimplicialNerve KanComplexCat.{u}

/-- The inf-category of anima is a quasicategory. -/
@[kerodon 01YY]
instance : Quasicategory anima.{u} := sorry

end SSet
