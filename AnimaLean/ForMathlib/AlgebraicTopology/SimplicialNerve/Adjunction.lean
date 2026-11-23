import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialNerve

universe w

open CategoryTheory

/-- The homotopy coherent nerve `N^hc : Cat_Δ ⥤ Set_Δ` admits a left adjoint, the path category
functor `Path[-]`. This is the one black box of the project, and it is proved as a corollary
of the existence of colimits in `Cat_Δ` in Kerodon, which we don't have API for yet. -/
@[kerodon 00L4]
instance : SimplicialCat.simplicialNerve.{w, w}.IsRightAdjoint := sorry

namespace SSet

/-- The path category `Path[S]•` of a simplicial set `S`, as a functor: the left adjoint of the
homotopy coherent nerve. -/
@[kerodon 00L2]
noncomputable def thickening : SSet.{w} ⥤ SimplicialCat.{w, w} :=
  SimplicialCat.simplicialNerve.{w, w}.leftAdjoint

/-- The path category functor is left adjoint to the homotopy coherent nerve: simplicial functors
`Path[S]• ⟶ C` are the same as maps `S ⟶ N^hc(C)`, naturally in `S` and `C`. The unit is the
comparison map `S ⟶ N^hc(Path[S])` of Kerodon Definition 2.4.4.1. -/
@[kerodon 00L4]
noncomputable def thickeningAdjunction :
    thickening.{w} ⊣ SimplicialCat.simplicialNerve.{w, w} :=
  Adjunction.ofIsRightAdjoint _

end SSet
