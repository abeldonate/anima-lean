import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialNerve
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialSet.Horn

universe v

open CategoryTheory MonoidalCategory Simplicial SimplicialThickening SimplicialNerve

namespace CategoryTheory.CordierPorter

section HollowPath

variable (n : ℕ) (i : Fin (n + 3))

/-- The first vertex of `[n + 2]`. -/
abbrev a0 : Th.{v} (n + 2) := ⟨⟨0⟩⟩

/-- The last vertex of `[n + 2]`. -/
abbrev am : Th.{v} (n + 2) := ⟨⟨Fin.last _⟩⟩

/-- The interior vertices of `[n + 2]` other than `i`. A path from `0` to `n + 2` is determined by
which interior vertices it contains, so `Hom(0, n + 2)` is a cube with one coordinate per interior
vertex. We split these coordinates into the ones in `J` and the special coordinate `i`, which
carries the face missing from the horn. -/
def J : Type v := {k : ULift.{v} (Fin (n + 3)) // 0 < k.down ∧ k.down < Fin.last _ ∧ k.down ≠ i}

/-- The `J`-coordinates of a path from `0` to `n + 2`: the vertices of `J` it passes through.
It is monotone, so it is a functor between the posets. -/
def Φ : (a0.{v} n ⟶ am n) ⥤ Set (J.{v} n i) where
  obj S := {k | k.1 ∈ S.I}
  map φ := homOfLE (fun _ hk ↦ φ.hom.down.down hk)

/-- The `i`-coordinate of a path from `0` to `n + 2`: `1` if it passes through `i`, and `0`
otherwise. It lands in `ULift (Fin 2)` because `Δ[1] ≅ nerve (ULift (Fin 2))`. -/
noncomputable def Ψ : (a0.{v} n ⟶ am n) ⥤ ULift.{v} (Fin 2) where
  obj S := ⟨by classical exact if (⟨i⟩ : ULift (Fin (n + 3))) ∈ S.I then 1 else 0⟩
  map {S T} φ := homOfLE (by
    classical
    change (if (⟨i⟩ : ULift (Fin (n + 3))) ∈ S.I then (1 : Fin 2) else 0) ≤
      (if (⟨i⟩ : ULift (Fin (n + 3))) ∈ T.I then 1 else 0)
    have := @φ.hom.down.down ⟨i⟩
    split_ifs <;> grind)

/-- The path from `0` to `n + 2` with `J`-coordinates `T` and `i`-coordinate `b`, i.e.
`{0, n + 2} ∪ T ∪ ({i} if b = 1)`. It inverts `(Φ, Ψ)` on single paths. -/
def mkPath (T : Set (J.{v} n i)) (b : ULift.{v} (Fin 2)) : (a0.{v} n ⟶ am n) where
  I := {c | c = ⟨0⟩ ∨ c = ⟨Fin.last _⟩ ∨ (∃ k ∈ T, k.1 = c) ∨ (c = ⟨i⟩ ∧ b.down = 1)}
  left := Or.inl rfl
  right := Or.inr (Or.inl rfl)
  left_le _ _ := Fin.zero_le _
  le_right _ _ := Fin.le_last _

/-- The inverse of `(Φ, Ψ)` on chains: apply `mkPath` levelwise to a chain `y` of subsets of `J`
and a chain `w` in `Fin 2`. The result is again a chain because `y` and `w` are increasing. -/
def Θ {m : SimplexCategoryᵒᵖ} (y : (nerve (Set (J.{v} n i))).obj m)
    (w : (nerve (ULift.{v} (Fin 2))).obj m) : (nerve (a0.{v} n ⟶ am n)).obj m where
  obj t := mkPath n i (y.obj t) (w.obj t)
  map {s t} φ := ⟨⟨⟨by
    have h : (w.obj s).down ≤ (w.obj t).down := show w.obj s ≤ w.obj t from leOfHom (w.map φ)
    rintro c (h | h | ⟨k, hk, rfl⟩ | ⟨rfl, hb⟩)
    exacts [Or.inl h, Or.inr (Or.inl h), Or.inr (Or.inr (Or.inl ⟨k, leOfHom (y.map φ) hk, rfl⟩)),
      Or.inr (Or.inr (Or.inr ⟨rfl, by grind⟩))]⟩⟩⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The `i`-coordinate of `S` is `1` exactly when `S` passes through `i`. -/
lemma Ψ_obj_eq_one_iff (S : a0.{v} n ⟶ am n) :
    ((Ψ n i).obj S).down = 1 ↔ (⟨i⟩ : ULift (Fin (n + 3))) ∈ S.I := by
  classical
  change (if (⟨i⟩ : ULift (Fin (n + 3))) ∈ S.I then (1 : Fin 2) else 0) = 1 ↔ _
  split_ifs with h <;> simp [h]

/-- A path is rebuilt from its coordinates: every vertex of `S` is `0`, `n + 2`, `i` or in `J`. -/
lemma mkPath_Φ_Ψ (S : a0.{v} n ⟶ am n) : (mkPath n i ((Φ n i).obj S) ((Ψ n i).obj S)).I = S.I := by
  ext c
  constructor
  · rintro (rfl | rfl | ⟨k, hk, rfl⟩ | ⟨rfl, hb⟩)
    exacts [S.left, S.right, hk, (Ψ_obj_eq_one_iff n i S).1 hb]
  · intro hc
    by_cases h₀ : c = ⟨0⟩
    · exact Or.inl h₀
    by_cases h₁ : c = ⟨Fin.last _⟩
    · exact Or.inr (Or.inl h₁)
    by_cases h₂ : c = ⟨i⟩
    · exact Or.inr (Or.inr (Or.inr ⟨h₂, (Ψ_obj_eq_one_iff n i S).2 (h₂ ▸ hc)⟩))
    refine Or.inr (Or.inr (Or.inl ⟨⟨c, ?_, ?_, ?_⟩, hc, rfl⟩))
    · exact Fin.pos_iff_ne_zero.2 fun e ↦ h₀ (ULift.ext _ _ e)
    · exact Fin.lt_last_iff_ne_last.2 fun e ↦ h₁ (ULift.ext _ _ e)
    · exact fun e ↦ h₂ (ULift.ext _ _ e)

/-- The `J`-coordinates of `mkPath T b` are `T`. -/
lemma Φ_mkPath (T : Set (J.{v} n i)) (b : ULift.{v} (Fin 2)) :
    (Φ n i).obj (mkPath n i T b) = T := by
  ext k
  obtain ⟨⟨k⟩, hk₀, hkm, hki⟩ := k
  constructor
  · rintro (h | h | ⟨k', hk', h⟩ | ⟨h, -⟩)
    · exact absurd (congr_arg ULift.down h) hk₀.ne'
    · exact absurd (congr_arg ULift.down h) hkm.ne
    · exact (Subtype.ext h : k' = _) ▸ hk'
    · exact absurd (congr_arg ULift.down h) hki
  · exact fun hk ↦ Or.inr (Or.inr (Or.inl ⟨_, hk, rfl⟩))

/-- The `i`-coordinate of `mkPath T b` is `b`. This needs `i` to be inner: if `i` were `0` or
`n + 2`, every path would pass through it. -/
lemma Ψ_mkPath (h0 : 0 < i) (hn : i < Fin.last (n + 2)) (T : Set (J.{v} n i))
    (b : ULift.{v} (Fin 2)) : (Ψ n i).obj (mkPath n i T b) = b := by
  have key : ((Ψ n i).obj (mkPath n i T b)).down = 1 ↔ b.down = 1 := by
    rw [Ψ_obj_eq_one_iff]
    constructor
    · rintro (h | h | ⟨k, -, h⟩ | ⟨-, h⟩)
      · exact absurd (congr_arg ULift.down h) h0.ne'
      · exact absurd (congr_arg ULift.down h) hn.ne
      · exact absurd (congr_arg ULift.down h) k.2.2.2
      · exact h
    · exact fun h ↦ Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  exact ULift.ext _ _ (by grind)

/-- The boundary of the cube on `J`: the chains along which some `k ∈ J` is always absent
(`b = false`) or always present (`b = true`). These are the union of the faces `{k ∉ S}` and
`{k ∈ S}`; a chain lies in a face iff all of its sets do. -/
def bdry : (nerve (Set (J.{v} n i))).Subcomplex where
  obj p := {y | ∃ (k : J n i) (b : Bool), ∀ t, k ∈ y.obj t ↔ b = true}
  map f := by
    rintro y ⟨k, b, h⟩
    exact ⟨k, b, fun t ↦ h _⟩

/-- The nerve of the paths from `0` to `n + 2` is the cube `nerve (Set J) ⊗ nerve [1]`: a chain
of paths goes to its chains of `J`-coordinates and of `i`-coordinates, with inverse `Θ`. -/
noncomputable def pathIso₀ (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    nerve (a0.{v} n ⟶ am n) ≅ nerve (Set (J.{v} n i)) ⊗ nerve (ULift.{v} (Fin 2)) :=
  NatIso.ofComponents (fun p ↦ Equiv.toIso
    { toFun x := ((nerveMap (Φ n i)).app p x, (nerveMap (Ψ n i)).app p x)
      invFun y := Θ n i y.1 y.2
      left_inv x := chain_ext fun t ↦ mkPath_Φ_Ψ n i (x.obj t)
      right_inv y := Prod.ext (nerve.ext_of_isThin (funext fun t ↦ Φ_mkPath n i _ _))
        (nerve.ext_of_isThin (funext fun t ↦ Ψ_mkPath n i h0 hn _ _)) })

/-- The nerve of the paths from `0` to `n + 2` is the cube `nerve (Set J) ⊗ Δ[1]`, where the
`Δ[1]` factor is the `i`-coordinate. This is `pathIso₀` composed with `Δ[1] ≅ nerve [1]`; the two
are kept separate because merging them breaks elaboration. -/
noncomputable def pathIso (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    nerve (a0.{v} n ⟶ am n) ≅ nerve (Set (J.{v} n i)) ⊗ Δ[1] :=
  pathIso₀ n i h0 hn ≪≫ whiskerLeftIso _ (SSet.stdSimplex.isoNerve.{v} 1).symm

/-- The hollow cube: the part of `Hom(0, n + 2)` determined by the horn `Λ[n + 2, i]`. It is the
preimage, under `pathIso`, of the pushout-product `(cube × Λ[1, 1]) ∪ (bdry × Δ[1])`. Since
`Λ[1, 1]` is the vertex `1` ("passes through `i`"), these are all the faces of the cube except
`{i ∉ S}`, the one that would come from the missing face of the horn. -/
noncomputable def hollowP (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    (nerve (a0.{v} n ⟶ am n)).Subcomplex :=
  ((bdry n i).unionProd (SSet.horn.{v} 1 1)).preimage (pathIso n i h0 hn).hom

/-- The inclusion of the hollow cube is anodyne (Kerodon `00LU`): `Λ[1, 1] ↪ Δ[1]` is anodyne,
so is its pushout-product with `bdry ↪ cube`, and anodyne inclusions are stable under preimage
along an isomorphism. This is what lets the Kan property extend the map on the hollow cube. -/
lemma anodyne_hollowP (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    SSet.anodyneExtensions (hollowP n i h0 hn).ι :=
  SSet.anodyneExtensions.preimage_ι _ _
    (SSet.anodyneExtensions_unionProd_ι _ _ (SSet.anodyneExtensions.horn_ι 1))

/-- A chain of paths lies in the hollow cube iff every set of it contains `i`, or some `k ∈ J` lies
in all of its sets or in none of them. This is the concrete form used to glue the values on the
hollow cube in `Quasicategory.lean`. -/
lemma mem_hollowP (h0 : 0 < i) (hn : i < Fin.last (n + 2)) {p : SimplexCategoryᵒᵖ}
    (x : (nerve (a0.{v} n ⟶ am n)).obj p) :
    x ∈ (hollowP n i h0 hn).obj p ↔ (∀ t, (⟨i⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I) ∨
      ∃ (k : J n i) (b : Bool), ∀ t, (k.1 ∈ (x.obj t).I ↔ b = true) := by
  change (pathIso n i h0 hn).hom.app p x ∈ ((bdry n i).unionProd _).obj p ↔ _
  refine (SSet.Subcomplex.mem_unionProd_iff _ _ _).trans (or_congr ?_ Iff.rfl)
  refine (SSet.mem_horn_one_iff _ _).trans ?_
  exact forall_congr' fun t ↦ Ψ_obj_eq_one_iff n i (x.obj t)

end HollowPath

end CategoryTheory.CordierPorter
