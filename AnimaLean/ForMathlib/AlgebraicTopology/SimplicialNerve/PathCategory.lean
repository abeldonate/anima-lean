import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
import Mathlib.CategoryTheory.PathCategory.Basic
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialNerve.Adjunction

universe w

open CategoryTheory SimplicialCategory SimplicialThickening Simplicial

namespace CategoryTheory

/-- A category is *free* if it is isomorphic to the path category of a directed graph -/
@[kerodon 00HR]
def IsFree.{v, u} (C : Type u) [Category.{v} C] : Prop :=
  ∃ (G : Type u) (_ : Quiver.{v + 1} G) (F : Paths G ⥤ C), Function.Bijective F.obj ∧
    ∀ x y, Function.Bijective (F.map : (x ⟶ y) → (F.obj x ⟶ F.obj y))

/-- A morphism is *indecomposable* if it is not an identity, and whenever it is written as a
composite, one of the two factors is an identity -/
@[kerodon 00HS]
def IsIndecomposable.{v, u} {C : Type u} [Category.{v} C] {A B : C} (f : A ⟶ B) : Prop :=
  (∀ h : A = B, f ≠ eqToHom h) ∧ ∀ {X : C} (g : A ⟶ X) (h : X ⟶ B), g ≫ h = f →
    (∃ e : A = X, g = eqToHom e) ∨ ∃ e : X = B, h = eqToHom e

end CategoryTheory

namespace CategoryTheory.SimplicialCat

/-- The path category `Path[n]` of the linear order `[n]`, i.e. the simplicial thickening of
`[n]`, as a simplicial category. -/
def th (n : ℕ) : SimplicialCat.{w, w} := ⟨Th.{w} n⟩

/-- Simplicial functors `Path[n] ⥤ C` are the `n`-simplices of `N^hc(C)`: this is the definition
of the homotopy coherent nerve. -/
def thHomEquiv (n : ℕ) (C : SimplicialCat.{w, w}) :
    (th.{w} n ⟶ C) ≃ (simplicialNerve.obj C).obj (Opposite.op ⦋n⦌) := Equiv.refl _

end CategoryTheory.SimplicialCat

namespace SSet

section Description

variable (S : SSet.{w}) (m : SimplexCategoryᵒᵖ)

/-- The first vertex of `[n]`. -/
abbrev thStart (n : ℕ) : Th.{w} n := ⟨⟨0⟩⟩

/-- The last vertex of `[n]`. -/
abbrev thEnd (n : ℕ) : Th.{w} n := ⟨⟨Fin.last n⟩⟩

/-- The set `E(S, m)` of Kerodon: pairs `(σ, I)` of a nondegenerate
`n`-simplex `σ` of `S`, `n > 0`, and a chain `I` of paths from `0` to `n` which starts with
`{0, n}` and ends with all of `[n]`. (Mathlib orders paths by inclusion, Kerodon by reverse
inclusion, so Kerodon's `I₀ = [n]` and `Iₘ = {0, n}` become `I 0 = {0, n}` and `I m = [n]`.) -/
@[kerodon 00L9]
structure PathGen where
  /-- The dimension of the simplex. -/
  n : ℕ
  pos : 0 < n
  /-- The nondegenerate simplex. -/
  σ : S.nonDegenerate n
  /-- The chain of paths. -/
  I : (nerve (thStart.{w} n ⟶ thEnd n)).obj m
  first : (I.obj 0).I = {⟨0⟩, ⟨Fin.last n⟩}
  last : (I.obj (Fin.last _)).I = Set.univ

/-- The `n`-simplex of `N^hc(Path[S])` given by a simplex of `S`: the unit of the adjunction. -/
noncomputable abbrev PathGen.simplex (g : PathGen.{w} S m) :=
  ((thickeningAdjunction.{w}.unit.app S).app (Opposite.op ⦋g.n⦌)) g.σ.1

/-- The morphism `u(σ, I)` of `Path[S]ₘ` (with its endpoints) attached to an element of
`E(S, m)`. -/
noncomputable def PathGen.toSigma (g : PathGen.{w} S m) :
    Σ (A B : Level (thickening.{w}.obj S).α m), A ⟶ B :=
  ⟨⟨g.simplex.obj (thStart g.n)⟩, ⟨g.simplex.obj (thEnd g.n)⟩,
    (g.simplex.map (thStart g.n) (thEnd g.n)).app m g.I⟩

/-- The vertices of `S` as objects of `Path[S]`: the unit on `0`-simplices. -/
noncomputable def vtx (x : S _⦋0⦌) : (thickening.{w}.obj S).α :=
  (((thickeningAdjunction.{w}.unit.app S).app (Opposite.op ⦋0⦌)) x).obj (thStart 0)

/-- **The path category of a simplicial set**, objects: the vertices of `S` are the objects of
`Path[S]`. -/
@[kerodon 00LA]
theorem vtx_bijective : Function.Bijective (vtx.{w} S) := sorry

/-- **The path category of a simplicial set**, freeness: each category `Path[S]ₘ` is free. -/
@[kerodon 00LA]
theorem isFree_level_thickening : IsFree (Level (thickening.{w}.obj S).α m) := sorry

/-- **The path category of a simplicial set**, generators: the maps `u(σ, I)` identify `E(S, m)`
with the indecomposable morphisms of `Path[S]ₘ`. -/
@[kerodon 00LA]
theorem toSigma_injective_and_range :
    Function.Injective (PathGen.toSigma.{w} S m) ∧
      Set.range (PathGen.toSigma.{w} S m) = {p | IsIndecomposable p.2.2} := sorry

/-- **The path category of `[n]`**, freeness: the category `Path[n]ₘ` is free. -/
@[kerodon 00LF]
theorem isFree_level_th (n : ℕ) : IsFree (Level (Th.{w} n) m) := sorry

/-- **The path category of `[n]`**, generators: the indecomposable morphisms of `Path[n]ₘ` are the
chains of paths from `x < y` starting with `{x, y}`. -/
@[kerodon 00LF]
theorem isIndecomposable_level_th (n : ℕ) :
    {p : Σ (A B : Level (Th.{w} n) m), A ⟶ B | IsIndecomposable p.2.2} =
      {p | p.1.as.as.down < p.2.1.as.as.down ∧
        (p.2.2.obj 0).I = {p.1.as.as, p.2.1.as.as}} := sorry

/-- `Hom(Path[Δⁿ], C) ≅ Hom(Path[n], C)`, naturally in `C`: both are `N^hc_n(C)`. -/
noncomputable def thickeningStdSimplexNatIso (n : ℕ) :
    coyoneda.obj (Opposite.op (thickening.obj (stdSimplex.{w}.obj ⦋n⦌))) ≅
      coyoneda.obj (Opposite.op (SimplicialCat.th.{w} n)) :=
  NatIso.ofComponents (fun Z =>
    (((thickeningAdjunction.homEquiv _ _).trans yonedaEquiv).trans
      (SimplicialCat.thHomEquiv n Z).symm).toIso)
    (fun {Z Z'} g => by
      ext f
      simp [Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
      rfl)

/-- **The path category of a simplex**: `Path[Δⁿ] ≅ Path[n]`. Both corepresent `C ↦ N^hc_n(C)`: for
`Path[Δⁿ]` by the adjunction and Yoneda, for `Path[n]` by the definition of `N^hc`. -/
@[kerodon 00L6]
noncomputable def thickeningStdSimplex (n : ℕ) :
    SimplicialCat.th.{w} n ≅ thickening.obj (stdSimplex.{w}.obj ⦋n⦌) :=
  (Coyoneda.fullyFaithful.preimageIso (thickeningStdSimplexNatIso n)).unop

theorem thHomEquiv_thickeningStdSimplex_hom (n : ℕ) {C : SimplicialCat.{w, w}}
    (g : thickening.obj (stdSimplex.{w}.obj ⦋n⦌) ⟶ C) :
    SimplicialCat.thHomEquiv n C ((thickeningStdSimplex.{w} n).hom ≫ g) =
      yonedaEquiv (thickeningAdjunction.homEquiv _ _ g) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (Coyoneda.fullyFaithful.map_preimage
    (thickeningStdSimplexNatIso.{w} n).hom) C) g
  exact h

/-- Under `Path[Δⁿ] ≅ Path[n]`, a simplicial functor `E : Path[n] ⥤ C` corresponds under the
adjunction to the `n`-simplex `Δⁿ ⟶ N^hc(C)` it defines. -/
theorem homEquiv_thickeningStdSimplex (n : ℕ) {C : SimplicialCat.{w, w}}
    (E : SimplicialCat.th.{w} n ⟶ C) :
    thickeningAdjunction.homEquiv _ _ ((thickeningStdSimplex.{w} n).inv ≫ E) =
      yonedaEquiv.symm (SimplicialCat.thHomEquiv n C E) := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, ← thHomEquiv_thickeningStdSimplex_hom]
  simp

end Description

end SSet
