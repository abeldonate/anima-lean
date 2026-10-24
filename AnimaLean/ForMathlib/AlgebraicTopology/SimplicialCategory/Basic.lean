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

lemma hcomp_map (v w : HSimplex C n) (h : v.tgt = w.src) (f : n ⟶ n') :
    (hcomp v w).map f = hcomp (v.map f) (w.map f) := by
  obtain ⟨A, B, s⟩ := v
  obtain ⟨_, D, t⟩ := w
  subst h
  rw [hcomp_mk]
  exact (congr_arg (mk _ _) (comp_map s t f)).trans (hcomp_mk _ _).symm

lemma idS_hcomp {A : C} (w : HSimplex C n) (h : w.src = A) : hcomp ⟨A, A, idS A n⟩ w = w := by
  obtain ⟨B, D, t⟩ := w
  subst h
  rw [hcomp_mk, idS_comp]

lemma hcomp_idS {A : C} (w : HSimplex C n) (h : w.tgt = A) : hcomp w ⟨A, A, idS A n⟩ = w := by
  obtain ⟨B, D, t⟩ := w
  subst h
  rw [hcomp_mk, comp_idS]

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

end HSimplex

end CategoryTheory.SimplicialCategory
