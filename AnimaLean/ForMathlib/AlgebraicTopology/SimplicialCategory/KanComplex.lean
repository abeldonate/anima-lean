import Mathlib.AlgebraicTopology.ModelCategory.Bifibrant
import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialCategory.LocallyKan

universe u

open CategoryTheory MonoidalCategory SimplicialCategory HomotopicalAlgebra

namespace SSet

open modelCategoryQuillen

/-- If `Y` is a Kan complex, then so is `sHom X Y`. There is a similar instance with
`ihom X Y`, but they agree by rlf -/
@[kerodon 00TN]
instance kanComplex_sHom (X Y : SSet.{u}) [KanComplex Y] : KanComplex (sHom X Y) :=
  inferInstanceAs (KanComplex ((ihom X).obj Y))

/-- The simplicial category of Kan complexes: the full subcategory of `SSet` on the
Kan complexes, with mapping simplicial sets `sHom X Y = Fun(X, Y)`. -/
abbrev KanComplexCat : Type (u + 1) := FibrantObject SSet.{u}

namespace KanComplexCat

/-- Constructor for `KanComplexCat`. -/
abbrev of (X : SSet.{u}) [KanComplex X] : KanComplexCat.{u} := FibrantObject.mk X

instance (X : KanComplexCat.{u}) : KanComplex X.obj := X.property

/-- The simplicial category of Kan complexes is locally Kan. -/
instance : LocallyKan KanComplexCat.{u} where
  kanComplex_sHom X Y := inferInstanceAs (KanComplex (sHom X.obj Y.obj))

end KanComplexCat

end SSet
