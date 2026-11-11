import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialNerve
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialSet.Horn

universe v

open CategoryTheory MonoidalCategory Simplicial SimplicialThickening SimplicialNerve

namespace CategoryTheory.CordierPorter

variable (n : ℕ) (i : Fin (n + 3))

/-- The vertex `k` of `[n + 2]`. -/
abbrev pt (k : Fin (n + 3)) : Th.{v} (n + 2) := ⟨⟨k⟩⟩

variable {n} in
lemma th_ext {a b : Th.{v} (n + 2)} (h : a.as.down = b.as.down) : a = b := by
  obtain ⟨⟨a⟩⟩ := a
  obtain ⟨⟨b⟩⟩ := b
  obtain rfl : a = b := h
  rfl

/-- The chains of paths from `a` to `b` on which a horn `Λ[n + 2, i]` prescribes the value of a
filler: the chains avoiding some vertex `k ≠ i` (they lie in the face opposite `k`), and the chains
passing through some vertex `k` strictly between `a` and `b` (they are composites).

For `(a, b) = (0, n + 2)` this is the *hollow cube*: a path from `0` to `n + 2` is a set of interior
vertices, so `Hom(0, n + 2)` is a cube, and `hollow` consists of all its faces except `{i ∉ S}`,
the one that would come from the missing face of the horn. For all other `(a, b)` it is
everything. -/
def hollow (a b : Th.{v} (n + 2)) : (nerve (a ⟶ b)).Subcomplex where
  obj p := {x | (∃ k, k ≠ i ∧ ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∉ (x.obj t).I) ∨
    ∃ k, a.as.down < k ∧ k < b.as.down ∧ ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I}
  map f := by
    rintro x (⟨k, hk, h⟩ | ⟨k, h₁, h₂, h⟩)
    exacts [Or.inl ⟨k, hk, fun t ↦ h _⟩, Or.inr ⟨k, h₁, h₂, fun t ↦ h _⟩]

/-- The homotopy on `Hom(0, n + 2)` from the identity to "add the vertex `i`": it adds `i` to a
path where the `Δ[1]`-coordinate is `1`. -/
def addVertex : nerve (pt.{v} n 0 ⟶ pt n (Fin.last _)) ⊗ Δ[1] ⟶
    nerve (pt.{v} n 0 ⟶ pt n (Fin.last _)) where
  app p := TypeCat.ofHom fun y ↦
    { obj t :=
        { I := {c | c ∈ (y.1.obj t).I ∨ c = ⟨i⟩ ∧ SSet.stdSimplex.asOrderHom y.2 t = 1}
          left := Or.inl (y.1.obj t).left
          right := Or.inl (y.1.obj t).right
          left_le _ _ := Fin.zero_le _
          le_right _ _ := Fin.le_last _ }
      map {s t} φ := ⟨⟨⟨by
        rintro c (h | ⟨rfl, h⟩)
        · exact Or.inl ((y.1.map φ).hom.down.down h)
        · exact Or.inr ⟨rfl, le_antisymm (Fin.le_last _)
            (h ▸ (SSet.stdSimplex.asOrderHom y.2).monotone (leOfHom φ))⟩⟩⟩⟩
      map_id _ := Subsingleton.elim _ _
      map_comp _ _ := Subsingleton.elim _ _ }
  naturality _ _ _ := by
    ext
    rfl

/-- The inclusion of `hollow` is anodyne. For `(a, b) ≠ (0, n + 2)` every chain avoids `0` or
`n + 2`, so `hollow` is everything. For the hollow cube, `addVertex` exhibits the inclusion as a
retract of a pushout-product with `Λ[1, 1] ↪ Δ[1]`. This is what lets the Kan property extend
maps defined on `hollow`. -/
lemma anodyne_hollow (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (a b : Th.{v} (n + 2)) :
    SSet.anodyneExtensions (hollow n i a b).ι := by
  by_cases h : a = pt n 0 ∧ b = pt n (Fin.last _)
  · obtain ⟨rfl, rfl⟩ := h
    refine SSet.anodyneExtensions.of_retract_ι (SSet.anodyneExtensions_unionProd_ι (hollow n i _ _)
      _ (SSet.anodyneExtensions.horn_ι 1)) SSet.ι₀ (addVertex n i) ?_ (fun p x hx ↦ ?_) ?_
    · ext p x t c
      refine ⟨?_, fun h ↦ Or.inl h⟩
      rintro (h | ⟨-, h⟩)
      exacts [h, absurd (show (0 : Fin 2) = 1 from h) (by decide)]
    · exact (SSet.Subcomplex.mem_unionProd_iff _ _ _).2 (Or.inr hx)
    · rintro p ⟨y, w⟩ hy
      rcases (SSet.Subcomplex.mem_unionProd_iff _ _ _).1 hy with hw | ⟨k, hk, h⟩ | ⟨k, h₁, h₂, h⟩
      · exact Or.inr ⟨i, h0, hn, fun t ↦ Or.inr ⟨rfl, (SSet.mem_horn_one_iff 1 w).1 hw t⟩⟩
      · refine Or.inl ⟨k, hk, fun t ↦ ?_⟩
        rintro (h' | ⟨h', -⟩)
        exacts [h t h', hk (congr_arg ULift.down h')]
      · exact Or.inr ⟨k, h₁, h₂, fun t ↦ Or.inl (h t)⟩
  · have : hollow n i a b = ⊤ := top_unique fun p x _ ↦ Or.inl <| by
      by_cases ha : a.as.down = 0
      · exact ⟨Fin.last _, hn.ne', fun t ht ↦ h ⟨th_ext ha,
          th_ext (le_antisymm (Fin.le_last _) ((x.obj t).le_right _ ht))⟩⟩
      · exact ⟨0, h0.ne, fun t ht ↦ ha (Fin.le_zero_iff.1 ((x.obj t).left_le _ ht))⟩
    rw [this]
    exact .of_isIso (SSet.Subcomplex.topIso _).hom

end CategoryTheory.CordierPorter
