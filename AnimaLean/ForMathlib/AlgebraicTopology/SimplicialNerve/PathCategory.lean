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

namespace SSet

section Description

variable (S : SSet.{w}) (m : SimplexCategoryᵒᵖ)

/-- The first vertex of `[n]`. -/
abbrev thStart (n : ℕ) : Th.{w} n := ⟨⟨0⟩⟩

/-- The last vertex of `[n]`. -/
abbrev thEnd (n : ℕ) : Th.{w} n := ⟨⟨Fin.last n⟩⟩

/-- The set `E(S, m)` of Kerodon Notation 2.4.4.9 (`00L9`): pairs `(σ, I)` of a nondegenerate
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

/-- **The path category of a simplicial set** (Kerodon Theorem 2.4.4.10, `00LA`): (1) the
vertices of `S` are the objects of `Path[S]`; (2) each category `Path[S]ₘ` is free; (3) the maps
`u(σ, I)` identify `E(S, m)` with the indecomposable morphisms of `Path[S]ₘ`. -/
@[kerodon 00LA]
theorem thickening_description :
    Function.Bijective (vtx.{w} S) ∧ (∀ m, IsFree (Level (thickening.{w}.obj S).α m)) ∧
      ∀ m, Function.Injective (PathGen.toSigma.{w} S m) ∧
        Set.range (PathGen.toSigma.{w} S m) = {p | IsIndecomposable p.2.2} := sorry

/-- **The path category of `[n]`** (Kerodon Lemma 2.4.4.16, `00LF`, for the poset `[n]`): the
category `Path[n]ₘ` is free, and its indecomposable morphisms are the chains of paths from
`x < y` starting with `{x, y}`. -/
@[kerodon 00LF]
theorem th_description (n : ℕ) (m : SimplexCategoryᵒᵖ) :
    IsFree (Level (Th.{w} n) m) ∧
      {p : Σ (A B : Level (Th.{w} n) m), A ⟶ B | IsIndecomposable p.2.2} =
        {p | p.1.as.as.down < p.2.1.as.as.down ∧
          (p.2.2.obj 0).I = {p.1.as.as, p.2.1.as.as}} := sorry

end Description

end SSet
