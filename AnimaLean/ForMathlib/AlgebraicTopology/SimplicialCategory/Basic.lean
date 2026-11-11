import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

universe v u

open CategoryTheory MonoidalCategory Simplicial

namespace CategoryTheory.SimplicialCategory

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

section HSimplex

variable {n n' : SimplexCategoryᵒᵖ}

/-- Composition of simplices of hom-objects. -/
def comp {A B D : C} (s : (sHom A B).obj n) (t : (sHom B D).obj n) : (sHom A D).obj n :=
  (eComp SSet A B D).app n (s, t)

/-- The identity simplex of `sHom A A`. -/
abbrev idS (A : C) (n : SimplexCategoryᵒᵖ) : (sHom A A).obj n :=
  (eId SSet A).app n PUnit.unit

lemma comp_assoc {A B D E : C} (s : (sHom A B).obj n) (t : (sHom B D).obj n)
    (w : (sHom D E).obj n) : comp (comp s t) w = comp s (comp t w) :=
  congr_arg (fun f ↦ f.app n (s, (t, w))) (e_assoc SSet A B D E)

lemma idS_comp {A B : C} (s : (sHom A B).obj n) : comp (idS A n) s = s :=
  congr_arg (fun f ↦ f.app n s) (e_id_comp SSet A B)

lemma comp_idS {A B : C} (s : (sHom A B).obj n) : comp s (idS B n) = s :=
  congr_arg (fun f ↦ f.app n s) (e_comp_id SSet A B)

lemma comp_map {A B D : C} (s : (sHom A B).obj n) (t : (sHom B D).obj n) (f : n ⟶ n') :
    (sHom A D).map f (comp s t) = comp ((sHom A B).map f s) ((sHom B D).map f t) :=
  (NatTrans.naturality_apply (eComp SSet A B D) f _).symm

lemma idS_map (A : C) (f : n ⟶ n') : (sHom A A).map f (idS A n) = idS A n' :=
  (NatTrans.naturality_apply (eId SSet A) f PUnit.unit).symm

/-- A simplex of some hom-object of `C`, together with its source and target. -/
structure HSimplex (C : Type u) [Category.{v} C] [SimplicialCategory C]
    (n : SimplexCategoryᵒᵖ) where
  /-- The source object. -/
  src : C
  /-- The target object. -/
  tgt : C
  /-- The simplex of `sHom src tgt`. -/
  s : (sHom src tgt).obj n

namespace HSimplex

/-- The underlying simplex of `v`, seen in a prescribed hom-object. -/
def get (v : HSimplex C n) {A B : C} (ha : v.src = A) (hb : v.tgt = B) : (sHom A B).obj n :=
  match v, ha, hb with
  | ⟨_, _, s⟩, rfl, rfl => s

lemma mk_get (v : HSimplex C n) {A B : C} (ha : v.src = A) (hb : v.tgt = B) :
    (⟨A, B, v.get ha hb⟩ : HSimplex C n) = v := by
  subst ha hb
  rfl

lemma get_congr {v w : HSimplex C n} (h : v = w) {A B : C} (ha : v.src = A) (hb : v.tgt = B) :
    v.get ha hb = w.get (h ▸ ha) (h ▸ hb) := by
  subst h
  rfl

/-- Restriction of a simplex along `f : n ⟶ n'`. -/
def map (v : HSimplex C n) (f : n ⟶ n') : HSimplex C n' :=
  ⟨v.src, v.tgt, (sHom v.src v.tgt).map f v.s⟩

lemma get_map (v : HSimplex C n) (f : n ⟶ n') {A B : C} (ha : v.src = A) (hb : v.tgt = B) :
    (v.map f).get ha hb = (sHom A B).map f (v.get ha hb) := by
  subst ha hb
  rfl

open Classical in
/-- Composition of simplices with matching target and source (junk value otherwise). -/
noncomputable def hcomp (v w : HSimplex C n) : HSimplex C n :=
  if h : v.tgt = w.src then ⟨v.src, w.tgt, comp v.s (w.get h.symm rfl)⟩ else v

lemma hcomp_src (v w : HSimplex C n) : (hcomp v w).src = v.src := by
  unfold hcomp
  split_ifs <;> rfl

lemma hcomp_tgt (v w : HSimplex C n) (h : v.tgt = w.src) : (hcomp v w).tgt = w.tgt := by
  rw [hcomp, dite_eq_left h]

lemma hcomp_mk {A B D : C} (s : (sHom A B).obj n) (t : (sHom B D).obj n) :
    hcomp ⟨A, B, s⟩ ⟨B, D, t⟩ = ⟨A, D, comp s t⟩ :=
  dite_eq_left rfl

lemma hcomp_assoc (u v w : HSimplex C n) (h₁ : u.tgt = v.src) (h₂ : v.tgt = w.src) :
    hcomp (hcomp u v) w = hcomp u (hcomp v w) := by
  obtain ⟨A, B, s⟩ := u
  obtain ⟨_, D, t⟩ := v
  obtain ⟨_, E, r⟩ := w
  subst h₁ h₂
  rw [hcomp_mk, hcomp_mk, hcomp_mk, hcomp_mk, comp_assoc]

lemma hcomp_map (v w : HSimplex C n) (f : n ⟶ n') :
    (hcomp v w).map f = hcomp (v.map f) (w.map f) := by
  by_cases h : v.tgt = w.src
  · obtain ⟨A, B, s⟩ := v
    obtain ⟨_, D, t⟩ := w
    subst h
    rw [hcomp_mk]
    exact (congr_arg (mk _ _) (comp_map s t f)).trans (hcomp_mk _ _).symm
  · simp_all [hcomp, dite_eq_right (show (v.map f).tgt ≠ (w.map f).src from h)]

lemma mk_idS_congr {A B : C} (h : A = B) (n : SimplexCategoryᵒᵖ) :
    (⟨A, A, idS A n⟩ : HSimplex C n) = ⟨B, B, idS B n⟩ := by
  subst h
  rfl

lemma mk_injective {A B : C} {s t : (sHom A B).obj n}
    (h : (⟨A, B, s⟩ : HSimplex C n) = ⟨A, B, t⟩) : s = t :=
  eq_of_heq (mk.inj h).2.2

end HSimplex

/-- A morphism into `sHom A B` built from a natural `HSimplex`-valued function. -/
def mkHom {X : SSet.{v}} {A B : C} (V : ∀ ⦃n⦄, X.obj n → HSimplex C n)
    (hs : ∀ ⦃n⦄ (x : X.obj n), (V x).src = A) (ht : ∀ ⦃n⦄ (x : X.obj n), (V x).tgt = B)
    (nat : ∀ ⦃n n'⦄ (f : n ⟶ n') (x : X.obj n), V (X.map f x) = (V x).map f) :
    X ⟶ sHom A B where
  app n := TypeCat.ofHom fun x ↦ (V x).get (hs x) (ht x)
  naturality n n' f := by
    ext x
    exact (HSimplex.get_congr (nat f x) _ _).trans (HSimplex.get_map _ _ _ _)

lemma mk_mkHom_app {X : SSet.{v}} {A B : C} (V : ∀ ⦃n⦄, X.obj n → HSimplex C n) hs ht nat
    (x : X.obj n) : (⟨A, B, (mkHom V hs ht nat).app n x⟩ : HSimplex C n) = V x :=
  HSimplex.mk_get _ _ _

section EnrichedFunctor

variable {A : Type*} [EnrichedCategory SSet.{v} A]

/-- The value of a simplicial functor on a simplex of a hom-object, with its endpoints. -/
def hval (F : EnrichedFunctor SSet.{v} A C) {a b : A} (x : (a ⟶[SSet] b).obj n) : HSimplex C n :=
  ⟨F.obj a, F.obj b, (F.map a b).app n x⟩

/-- Two simplicial functors with the same values are equal. -/
lemma enrichedFunctor_ext {F F' : EnrichedFunctor SSet.{v} A C}
    (h : ∀ (a b : A) (n : SimplexCategoryᵒᵖ) (x : (a ⟶[SSet] b).obj n), hval F x = hval F' x) :
    F = F' := by
  obtain ⟨o, m, _, _⟩ := F
  obtain ⟨o', m', _, _⟩ := F'
  obtain rfl : o = o' := funext fun a ↦
    congr_arg HSimplex.src (h a a (Opposite.op ⦋0⦌) ((eId SSet a).app _ PUnit.unit))
  obtain rfl : m = m' := by
    funext a b
    ext n x
    exact HSimplex.mk_injective (h a b n x)
  rfl

lemma hval_comp (F : EnrichedFunctor SSet.{v} A C) {a b c : A} (x : (a ⟶[SSet] b).obj n)
    (y : (b ⟶[SSet] c).obj n) :
    hval F ((eComp SSet a b c).app n (x, y)) = (hval F x).hcomp (hval F y) :=
  (congr_arg (HSimplex.mk _ _) (congr_arg (fun f ↦ f.app n (x, y)) (F.map_comp a b c))).trans
    (HSimplex.hcomp_mk _ _).symm

lemma hval_id (F : EnrichedFunctor SSet.{v} A C) (a : A) (n : SimplexCategoryᵒᵖ) :
    hval F ((eId SSet a).app n PUnit.unit) = ⟨F.obj a, F.obj a, idS (F.obj a) n⟩ :=
  congr_arg (HSimplex.mk _ _) (congr_arg (fun f ↦ f.app n PUnit.unit) (F.map_id a))

end EnrichedFunctor

end HSimplex

/-- The category of `n`-simplices of a simplicial category `C`: it has the objects of `C`, and its
morphisms from `A` to `B` are the `n`-simplices of `sHom A B`. -/
structure Level (C : Type u) (n : SimplexCategoryᵒᵖ) : Type u where
  /-- The underlying object of `C`. -/
  as : C

instance (n : SimplexCategoryᵒᵖ) : Category.{v} (Level C n) where
  Hom A B := (sHom A.as B.as).obj n
  id A := idS A.as n
  comp s t := comp s t
  id_comp := idS_comp
  comp_id := comp_idS
  assoc := comp_assoc

end CategoryTheory.SimplicialCategory
