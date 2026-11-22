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

variable {n i}

/-- Away from `(0, n + 2)`, every chain avoids `0` or `n + 2`, so `hollow` is everything. -/
lemma hollow_eq_top (h0 : 0 < i) (hn : i < Fin.last (n + 2)) {a b : Th.{v} (n + 2)}
    (h : ¬ (a = pt n 0 ∧ b = pt n (Fin.last _))) : hollow n i a b = ⊤ :=
  top_unique fun p x _ ↦ Or.inl <| by
    by_cases ha : a.as.down = 0
    · exact ⟨Fin.last _, hn.ne', fun t ht ↦ h ⟨th_ext ha,
        th_ext (le_antisymm (Fin.le_last _) ((x.obj t).le_right _ ht))⟩⟩
    · exact ⟨0, h0.ne, fun t ht ↦ ha (Fin.le_zero_iff.1 ((x.obj t).left_le _ ht))⟩

/-- The identity chain `{a}` lies in `hollow`: it avoids a vertex other than `a` and `i`. -/
lemma id_mem_hollow (a : Th.{v} (n + 2)) (p : SimplexCategoryᵒᵖ) :
    (eId SSet a).app p PUnit.unit ∈ (hollow n i a a).obj p := by
  obtain ⟨k, hk, hka⟩ : ∃ k : Fin (n + 3), k ≠ i ∧ k ≠ a.as.down := by
    by_contra! h
    have h₀ := h ⟨0, by omega⟩
    have h₁ := h ⟨1, by omega⟩
    have h₂ := h ⟨2, by omega⟩
    simp only [ne_eq, Fin.ext_iff] at h₀ h₁ h₂
    omega
  exact Or.inl ⟨k, hk, fun t ht ↦ hka (congr_arg ULift.down (Set.mem_singleton_iff.1 ht))⟩

/-- `hollow` is closed under composition: a composite through a vertex `b` strictly between `a`
and `c` passes through `b`, and a composite with an identity changes nothing. -/
lemma union_mem_hollow {a b c : Th.{v} (n + 2)} {p : SimplexCategoryᵒᵖ}
    {x : (nerve (a ⟶ b)).obj p} {y : (nerve (b ⟶ c)).obj p} (hx : x ∈ (hollow n i a b).obj p)
    (hy : y ∈ (hollow n i b c).obj p) : union x y ∈ (hollow n i a c).obj p := by
  by_cases hab : a.as.down = b.as.down
  · obtain rfl := th_ext hab
    rwa [chain_eq_id x, id_union]
  by_cases hbc : b.as.down = c.as.down
  · obtain rfl := th_ext hbc
    rwa [chain_eq_id y, union_id]
  exact Or.inr ⟨b.as.down,
    lt_of_le_of_ne (show a.as.down ≤ b.as.down from (x.obj 0).left_le _ (x.obj 0).right) hab,
    lt_of_le_of_ne (show b.as.down ≤ c.as.down from (y.obj 0).left_le _ (y.obj 0).right) hbc,
    fun t ↦ Or.inr (y.obj t).left⟩

variable (n i)

/-- The inclusion of `hollow` is anodyne (Kerodon `00LV`, with `exists_extension`). For the hollow
cube, `addVertex` exhibits the inclusion as a retract of a pushout-product with `Λ[1, 1] ↪ Δ[1]`;
elsewhere `hollow` is everything. This is what lets the Kan property extend maps defined on
`hollow`. -/
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
  · rw [hollow_eq_top h0 hn h]
    exact .of_isIso (SSet.Subcomplex.topIso _).hom

end CategoryTheory.CordierPorter
