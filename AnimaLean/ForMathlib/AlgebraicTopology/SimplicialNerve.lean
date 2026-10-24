import Mathlib.AlgebraicTopology.SimplicialNerve
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic

universe v u

open CategoryTheory Simplicial

namespace CategoryTheory.SimplicialThickening

section LinearOrder

variable {J : Type*} [LinearOrder J] {a b c : SimplicialThickening J} {n n' : SimplexCategoryᵒᵖ}

instance (a b : SimplicialThickening J) : Quiver.IsThin (a ⟶ b) :=
  fun _ _ ↦ ⟨fun _ _ ↦ InducedCategory.hom_ext (Subsingleton.elim _ _)⟩

/-- Two chains of paths with the same sets are equal -/
lemma chain_ext {x x' : (nerve (a ⟶ b)).obj n} (h : ∀ t, (x.obj t).I = (x'.obj t).I) : x = x' :=
  nerve.ext_of_isThin (funext fun t ↦ hom_ext _ _ _ _ fun _ ↦ by rw [h t])

/-- The union of two chains of paths -/
abbrev union (x₁ : (nerve (a ⟶ b)).obj n) (x₂ : (nerve (b ⟶ c)).obj n) :
    (nerve (a ⟶ c)).obj n :=
  (eComp SSet a b c).app n (x₁, x₂)

/-- Every chain of paths from `a` to `a` is the identity. -/
lemma chain_eq_id (x : (nerve (a ⟶ a)).obj n) : x = (eId SSet a).app n PUnit.unit :=
  chain_ext fun t ↦ Set.ext fun c ↦ ⟨fun hc ↦ le_antisymm ((x.obj t).le_right c hc)
    ((x.obj t).left_le c hc), fun hc ↦ hc ▸ (x.obj t).left⟩

lemma id_union (y : (nerve (a ⟶ b)).obj n) : union ((eId SSet a).app n PUnit.unit) y = y :=
  chain_ext fun t ↦ Set.union_eq_right.2 (Set.singleton_subset_iff.2 (y.obj t).left)

lemma union_id (x : (nerve (a ⟶ b)).obj n) : union x ((eId SSet b).app n PUnit.unit) = x :=
  chain_ext fun t ↦ Set.union_eq_left.2 (Set.singleton_subset_iff.2 (x.obj t).right)

/-- The chain of paths obtained by taking preimages under an injective monotone map. -/
def preChain {K : Type*} [LinearOrder K] (f : J →o K) (hf : Function.Injective f)
    {a b : SimplicialThickening K} {a' b' : J} (ha : f a' = a.as) (hb : f b' = b.as)
    (x : (nerve (a ⟶ b)).obj n) : (nerve ((mk a' : SimplicialThickening J) ⟶ mk b')).obj n where
  obj t :=
    { I := f ⁻¹' (x.obj t).I
      left := by simpa [Set.mem_preimage, ha] using (x.obj t).left
      right := by simpa [Set.mem_preimage, hb] using (x.obj t).right
      left_le c hc :=
        (f.monotone.strictMono_of_injective hf).le_iff_le.1 (ha ▸ (x.obj t).left_le _ hc)
      le_right c hc :=
        (f.monotone.strictMono_of_injective hf).le_iff_le.1 (hb ▸ (x.obj t).le_right _ hc) }
  map φ := ⟨⟨⟨Set.preimage_mono (x.map φ).hom.down.down⟩⟩⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The part of `S` in `[a, b]`, together with the endpoints. -/
def subI (S : Set J) (a b : J) : Set J := {c | (c ∈ S ∧ a ≤ c ∧ c ≤ b) ∨ c = a ∨ c = b}

lemma subI_ne {S : Set J} {a b c k : J} (hc : c ∈ subI S a b) (hk : k ∉ S) (ha : a ≠ k)
    (hb : b ≠ k) : c ≠ k := by
  grind [subI]

lemma subI_union (S : Set J) {a c b : J} (hc : c ∈ S) (ha : a ≤ c) (hb : c ≤ b) :
    subI S a c ∪ subI S c b = subI S a b := by
  ext x
  simp only [subI, Set.mem_union, Set.mem_ofPred_eq]
  rcases le_total x c with h | h <;> grind

lemma subI_self (S : Set J) {a b : J} (ha : a ∈ S) (hb : b ∈ S) (hS : ∀ c ∈ S, a ≤ c ∧ c ≤ b) :
    subI S a b = S := by
  ext x
  simp only [subI, Set.mem_ofPred_eq]
  grind

lemma subI_union_left (S T : Set J) {a c : J} (ha : a ∈ S) (hc : c ∈ S)
    (hS : ∀ x ∈ S, a ≤ x ∧ x ≤ c) (hT : ∀ x ∈ T, c ≤ x) : subI (S ∪ T) a c = S := by
  ext x
  simp only [subI, Set.mem_union, Set.mem_ofPred_eq]
  grind

lemma subI_union_right (S T : Set J) {c b : J} (hc : c ∈ T) (hb : b ∈ T)
    (hS : ∀ x ∈ S, x ≤ c) (hT : ∀ x ∈ T, c ≤ x ∧ x ≤ b) : subI (S ∪ T) c b = T := by
  ext x
  simp only [subI, Set.mem_union, Set.mem_ofPred_eq]
  grind

/-- The restriction of a chain of paths to an interval `[a', b']`. -/
def sub (a' b' : SimplicialThickening J) (h : a'.as ≤ b'.as) (x : (nerve (a ⟶ b)).obj n) :
    (nerve (a' ⟶ b')).obj n where
  obj t :=
    { I := subI (x.obj t).I a'.as b'.as
      left := Or.inr (Or.inl rfl)
      right := Or.inr (Or.inr rfl)
      left_le := by
        rintro c (⟨_, h', _⟩ | rfl | rfl)
        exacts [h', le_rfl, h]
      le_right := by
        rintro c (⟨_, _, h'⟩ | rfl | rfl)
        exacts [h', h, le_rfl] }
  map φ := ⟨⟨⟨by
    rintro c (⟨hc, h₁⟩ | h₂)
    exacts [Or.inl ⟨(x.map φ).hom.down.down hc, h₁⟩, Or.inr h₂]⟩⟩⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

lemma sub_map (a' b' : SimplicialThickening J) (h : a'.as ≤ b'.as) (f : n ⟶ n')
    (x : (nerve (a ⟶ b)).obj n) :
    sub a' b' h ((nerve (a ⟶ b)).map f x) = (nerve (a' ⟶ b')).map f (sub a' b' h x) :=
  chain_ext fun _ ↦ rfl

end LinearOrder

end CategoryTheory.SimplicialThickening

namespace CategoryTheory.SimplicialNerve

open MonoidalCategory SimplicialCategory SimplicialThickening

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- The simplicial thickening of `[k]`, whose simplicial functors to `C` are the `k`-simplices of
the simplicial nerve of `C`. -/
abbrev Th (k : ℕ) := SimplicialThickening (ULift.{v} (Fin (k + 1)))

/-- The order map on `ULift`s induced by `f : [p] ⟶ [k]`. -/
abbrev uf {p k : ℕ} (f : ⦋p⦌ ⟶ ⦋k⦌) : ULift.{v} (Fin (p + 1)) →o ULift.{v} (Fin (k + 1)) :=
  f.toOrderHom.uliftMap

/-- The map on hom-objects of the simplicial thickening induced by `f : [p] ⟶ [k]`. -/
abbrev thickMap {p k : ℕ} (f : ⦋p⦌ ⟶ ⦋k⦌) (a b : Th p) :=
  nerveMap (functorMap (uf f) a b)

/-- A `k`-simplex of the simplicial nerve, as an enriched functor. -/
abbrev Simplex (C : Type u) [Category.{v} C] [SimplicialCategory C] (k : ℕ) :=
  EnrichedFunctor SSet.{v} (Th k) C

section Val

variable {k : ℕ} {a b : Th k} {n n' : SimplexCategoryᵒᵖ}

/-- The value of an enriched functor on an `n`-simplex of a hom-object. -/
def val (E : Simplex C k) (x : (nerve (a ⟶ b)).obj n) : HSimplex C n :=
  ⟨E.obj a, E.obj b, (E.map a b).app n x⟩

lemma val_congr (E : Simplex C k) {a' b' : Th k} (ha : a = a') (hb : b = b')
    (x : (nerve (a ⟶ b)).obj n) (x' : (nerve (a' ⟶ b')).obj n)
    (h : ∀ t, (x.obj t).I = (x'.obj t).I) : val E x = val E x' := by
  subst ha hb
  rw [chain_ext h]

lemma val_union (E : Simplex C k) {c : Th k} (x₁ : (nerve (a ⟶ b)).obj n)
    (x₂ : (nerve (b ⟶ c)).obj n) : val E (union x₁ x₂) = (val E x₁).hcomp (val E x₂) :=
  (congr_arg (HSimplex.mk _ _) (congr_arg (fun f ↦ f.app n (x₁, x₂)) (E.map_comp a b c))).trans
    (HSimplex.hcomp_mk _ _).symm

lemma map_idS (E : Simplex C k) (a : Th k) (n : SimplexCategoryᵒᵖ) :
    (E.map a a).app n (idS a n) = idS (E.obj a) n :=
  congr_arg (fun f ↦ f.app n PUnit.unit) (E.map_id a)

lemma val_map (E : Simplex C k) (f : n ⟶ n') (x : (nerve (a ⟶ b)).obj n) :
    val E ((nerve (a ⟶ b)).map f x) = (val E x).map f :=
  congr_arg (HSimplex.mk _ _) (NatTrans.naturality_apply (E.map a b) f x)

/-- Two simplices of the simplicial nerve agreeing on all values are equal. -/
lemma eq_of_val {E E' : Simplex C k}
    (h : ∀ (a b : Th k) (n : SimplexCategoryᵒᵖ) (x : (nerve (a ⟶ b)).obj n), val E x = val E' x) :
    E = E' := by
  obtain ⟨o, m, _, _⟩ := E
  obtain ⟨o', m', _, _⟩ := E'
  obtain rfl : o = o' :=
    funext fun a ↦ congr_arg HSimplex.src (h a a (Opposite.op ⦋0⦌) (idS a _))
  obtain rfl : m = m' := by
    funext a b
    ext n x
    exact eq_of_heq (HSimplex.mk.inj (h a b n x)).2.2
  rfl

end Val

/-- Restriction of a `k`-simplex of the simplicial nerve along `f : [p] ⟶ [k]`. -/
abbrev restr {p k : ℕ} (f : ⦋p⦌ ⟶ ⦋k⦌) (E : Simplex C k) : Simplex C p :=
  (SimplicialNerve C).map f.op E

lemma val_restr {p k : ℕ} (f : ⦋p⦌ ⟶ ⦋k⦌) (E : Simplex C k) {a b : Th p} {n : SimplexCategoryᵒᵖ}
    (x : (nerve (a ⟶ b)).obj n) : val (restr f E) x = val E ((thickMap f a b).app n x) :=
  rfl

/-- If two `k`-simplices agree after restriction along a monomorphism `d : [p] ⟶ [k]`, then they
have the same values on every chain of paths contained in the image of `d`. -/
lemma val_eq_of_restr_eq {p k : ℕ} (d : ⦋p⦌ ⟶ ⦋k⦌) [Mono d] {E E' : Simplex C k}
    (h : restr d E = restr d E') {a b : Th k} {n : SimplexCategoryᵒᵖ} (x : (nerve (a ⟶ b)).obj n)
    (hx : ∀ t, (x.obj t).I ⊆ Set.range (uf.{v} d)) : val E x = val E' x := by
  have hinj : Function.Injective (uf.{v} d) := by
    have := (SimplexCategory.mono_iff_injective (f := d)).1 inferInstance
    exact fun x y e ↦ ULift.ext _ _ (this (congr_arg ULift.down e))
  obtain ⟨a', ha⟩ := hx 0 (x.obj 0).left
  obtain ⟨b', hb⟩ := hx 0 (x.obj 0).right
  let x' := preChain _ hinj ha hb x
  have key : ∀ E₀ : Simplex C k, val E₀ x = val E₀ ((thickMap d _ _).app n x') := fun E₀ ↦
    val_congr E₀ (by rw [ha]) (by rw [hb]) _ _ (fun t ↦
      (Set.image_preimage_eq_of_subset (hx t)).symm)
  rw [key E, key E', ← val_restr, ← val_restr, h]

end CategoryTheory.SimplicialNerve
