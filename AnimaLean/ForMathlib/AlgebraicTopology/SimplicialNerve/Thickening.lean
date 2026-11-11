import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.CategoryTheory.Quotient
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialNerve

universe u

open CategoryTheory MonoidalCategory Simplicial SimplicialCategory SimplicialThickening
  SimplicialNerve Opposite

namespace SSet

variable (S : SSet.{u})

namespace Thickening

/-- The vertex `a` of a simplex `σ`. -/
def vertex {n : ℕ} (σ : S _⦋n⦌) (a : Th.{u} n) : S _⦋0⦌ :=
  S.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ a.as.down).op σ

variable {S} in
lemma vertex_map {n n' : ℕ} (θ : ⦋n'⦌ ⟶ ⦋n⦌) (σ : S _⦋n⦌) (a : Th.{u} n') :
    vertex S (S.map θ.op σ) a = vertex S σ ⟨uf θ a.as⟩ := by
  rw [vertex, vertex, ← Functor.map_comp_apply]
  rfl

/-- A generating morphism from `x` to `y` in simplicial degree `m` of the path category of `S`:
a simplex `σ` of `S` and an `m`-simplex `c` of a hom-object of `Path[n]`, i.e. a chain of paths
from `a` to `b`, such that `x` and `y` are the vertices `a` and `b` of `σ`. -/
structure Gen (m : SimplexCategoryᵒᵖ) (x y : S _⦋0⦌) : Type u where
  /-- The dimension of the simplex. -/
  {n : ℕ}
  /-- The simplex. -/
  σ : S _⦋n⦌
  /-- The endpoints of the chain. -/
  {a b : Th.{u} n}
  /-- The chain of paths. -/
  c : (nerve (a ⟶ b)).obj m
  src : vertex S σ a = x
  tgt : vertex S σ b = y

/-- The vertices of `S`, with the quiver of generating morphisms in simplicial degree `m`. -/
structure Vtx (m : SimplexCategoryᵒᵖ) : Type u where
  /-- The underlying vertex. -/
  as : S _⦋0⦌

instance (m : SimplexCategoryᵒᵖ) : Quiver.{u} (Vtx S m) := ⟨fun x y ↦ Gen S m x.as y.as⟩

variable {S} in
/-- A generating morphism, as a morphism of the path category of the quiver `Vtx S m`. -/
abbrev Gen.toPath {m : SimplexCategoryᵒᵖ} {x y : S _⦋0⦌} (g : Gen S m x y) :
    (Paths.of (Vtx S m)).obj ⟨x⟩ ⟶ (Paths.of (Vtx S m)).obj ⟨y⟩ :=
  (Paths.of (Vtx S m)).map (X := ⟨x⟩) (Y := ⟨y⟩) g

/-- The relations between the generating morphisms: compatibility with the simplicial operators
of `S`, with composition in `Path[n]` and with identities of `Path[n]`. -/
inductive Rel (m : SimplexCategoryᵒᵖ) : HomRel (Paths (Vtx S m))
  | restr {n n' : ℕ} (θ : ⦋n'⦌ ⟶ ⦋n⦌) (σ : S _⦋n⦌) {a b : Th.{u} n'} (c : (nerve (a ⟶ b)).obj m)
      {x y : S _⦋0⦌} (hx : vertex S (S.map θ.op σ) a = x) (hy : vertex S (S.map θ.op σ) b = y)
      (hx' : vertex S σ ⟨uf θ a.as⟩ = x) (hy' : vertex S σ ⟨uf θ b.as⟩ = y) :
      Rel m (Gen.toPath ⟨S.map θ.op σ, c, hx, hy⟩)
        (Gen.toPath ⟨σ, (thickMap θ a b).app m c, hx', hy'⟩)
  | comp {n : ℕ} (σ : S _⦋n⦌) {a b d : Th.{u} n} (c : (nerve (a ⟶ b)).obj m)
      (c' : (nerve (b ⟶ d)).obj m) {x y z : S _⦋0⦌} (hx : vertex S σ a = x)
      (hy : vertex S σ b = y) (hz : vertex S σ d = z) :
      Rel m (Gen.toPath ⟨σ, c, hx, hy⟩ ≫ Gen.toPath ⟨σ, c', hy, hz⟩)
        (Gen.toPath ⟨σ, union c c', hx, hz⟩)
  | id {n : ℕ} (σ : S _⦋n⦌) (a : Th.{u} n) {x : S _⦋0⦌} (hx : vertex S σ a = x) :
      Rel m (Gen.toPath ⟨σ, idS a m, hx, hx⟩) (𝟙 ((Paths.of (Vtx S m)).obj ⟨x⟩))

/-- The category of `m`-simplices of the path category of `S`. -/
abbrev P (m : SimplexCategoryᵒᵖ) : Type u := CategoryTheory.Quotient (Rel S m)

variable {S}

/-- A vertex of `S` as an object of `P S m`. -/
abbrev P.mk {m : SimplexCategoryᵒᵖ} (x : S _⦋0⦌) : P S m := ⟨(Paths.of (Vtx S m)).obj ⟨x⟩⟩

variable {m m' m'' : SimplexCategoryᵒᵖ} {x y z : S _⦋0⦌}

/-- A generating morphism, as a morphism of `P S m`. -/
def ι (g : Gen S m x y) : (P.mk x : P S m) ⟶ P.mk y :=
  (CategoryTheory.Quotient.functor (Rel S m)).map g.toPath

lemma ι_restr {n n' : ℕ} (θ : ⦋n'⦌ ⟶ ⦋n⦌) (σ : S _⦋n⦌) {a b : Th.{u} n'}
    (c : (nerve (a ⟶ b)).obj m) (hx : vertex S (S.map θ.op σ) a = x)
    (hy : vertex S (S.map θ.op σ) b = y) (hx' : vertex S σ ⟨uf θ a.as⟩ = x)
    (hy' : vertex S σ ⟨uf θ b.as⟩ = y) :
    ι ⟨S.map θ.op σ, c, hx, hy⟩ = ι ⟨σ, (thickMap θ a b).app m c, hx', hy'⟩ :=
  CategoryTheory.Quotient.sound _ (Rel.restr θ σ c hx hy hx' hy')

lemma ι_comp {n : ℕ} (σ : S _⦋n⦌) {a b d : Th.{u} n} (c : (nerve (a ⟶ b)).obj m)
    (c' : (nerve (b ⟶ d)).obj m) (hx : vertex S σ a = x) (hy : vertex S σ b = y)
    (hz : vertex S σ d = z) :
    ι ⟨σ, c, hx, hy⟩ ≫ ι ⟨σ, c', hy, hz⟩ = ι ⟨σ, union c c', hx, hz⟩ :=
  ((CategoryTheory.Quotient.functor (Rel S m)).map_comp _ _).symm.trans
    (CategoryTheory.Quotient.sound _ (Rel.comp σ c c' hx hy hz))

lemma ι_id {n : ℕ} (σ : S _⦋n⦌) (a : Th.{u} n) (hx : vertex S σ a = x) :
    ι ⟨σ, idS a m, hx, hx⟩ = 𝟙 (P.mk x : P S m) :=
  CategoryTheory.Quotient.sound _ (Rel.id σ a hx)

/-- Induction on the morphisms of `P S m`: they are composites of generating morphisms. -/
lemma P.induction {motive : ∀ {x y : S _⦋0⦌}, ((P.mk x : P S m) ⟶ P.mk y) → Prop}
    (id : ∀ x, motive (𝟙 (P.mk x)))
    (comp : ∀ {x y z} (p : (P.mk x : P S m) ⟶ P.mk y) (g : Gen S m y z),
      motive p → motive (p ≫ ι g))
    {x y : S _⦋0⦌} (p : (P.mk x : P S m) ⟶ P.mk y) : motive p := by
  obtain ⟨p, rfl⟩ := (CategoryTheory.Quotient.functor (Rel S m)).map_surjective p
  have key (b : Vtx S m) (p : Quiver.Path (V := Vtx S m) ⟨x⟩ b) : motive (y := b.as)
      ((CategoryTheory.Quotient.functor (Rel S m)).map
        (show (Paths.of (Vtx S m)).obj ⟨x⟩ ⟶ (Paths.of (Vtx S m)).obj b from p)) := by
    induction p with
    | nil => exact id x
    | cons p q ih => exact comp _ q ih
  exact key ⟨y⟩ p

lemma ι_congr {n : ℕ} (σ : S _⦋n⦌) {a b : Th.{u} n} {c c' : (nerve (a ⟶ b)).obj m} (h : c = c')
    (hx : vertex S σ a = x) (hy : vertex S σ b = y) : ι ⟨σ, c, hx, hy⟩ = ι ⟨σ, c', hx, hy⟩ := by
  subst h
  rfl

/-- The action of a simplicial operator on a generating morphism. -/
def Gen.map (f : m ⟶ m') (g : Gen S m x y) : Gen S m' x y :=
  ⟨g.σ, (nerve _).map f g.c, g.src, g.tgt⟩

lemma Gen.map_id (g : Gen S m x y) : g.map (𝟙 m) = g := by
  obtain ⟨σ, c, hx, hy⟩ := g
  exact congr_arg (fun c ↦ (⟨σ, c, hx, hy⟩ : Gen S m x y)) ((nerve _).map_id_apply m c)

lemma Gen.map_comp (f : m ⟶ m') (f' : m' ⟶ m'') (g : Gen S m x y) :
    g.map (f ≫ f') = (g.map f).map f' := by
  obtain ⟨σ, c, hx, hy⟩ := g
  exact congr_arg (fun c ↦ (⟨σ, c, hx, hy⟩ : Gen S m'' x y)) ((nerve _).map_comp_apply f f' c)

/-- The action of a simplicial operator on generating morphisms, as a prefunctor. -/
def P.genMap (f : m ⟶ m') : Vtx S m ⥤q P S m' where
  obj x := P.mk x.as
  map g := ι (Gen.map f g)

lemma P.lift_genMap (f : m ⟶ m') (g : Gen S m x y) :
    (Paths.lift (P.genMap f)).map g.toPath = ι (g.map f) :=
  Paths.lift_toPath (P.genMap f) (X := ⟨x⟩) (Y := ⟨y⟩) g

/-- The action of a simplicial operator on the categories `P S m`. -/
def P.map (f : m ⟶ m') : P S m ⥤ P S m' :=
  CategoryTheory.Quotient.lift _ (Paths.lift (P.genMap f)) (by
    rintro _ _ _ _ (⟨θ, σ, c, hx, hy, hx', hy'⟩ | ⟨σ, c, c', hx, hy, hz⟩ | ⟨σ, a, hx⟩)
    · rw [P.lift_genMap, P.lift_genMap]
      exact (ι_restr θ σ _ hx hy hx' hy').trans
        (ι_congr σ (NatTrans.naturality_apply (thickMap θ _ _) f c) hx' hy')
    · rw [CategoryTheory.Functor.map_comp, P.lift_genMap, P.lift_genMap, P.lift_genMap]
      exact (ι_comp σ _ _ hx hy hz).trans (ι_congr σ (show union ((nerve _).map f c)
        ((nerve _).map f c') = (nerve _).map f (union c c') from
          (SimplicialCategory.comp_map (C := Th.{u} _) c c' f).symm) hx hz)
    · rw [CategoryTheory.Functor.map_id, P.lift_genMap]
      exact (ι_congr σ (idS_map a f) hx hx).trans (ι_id σ a hx))

/-- The action of a simplicial operator on the morphisms of the categories `P S m`. -/
def P.mapHom (f : m ⟶ m') (p : (P.mk x : P S m) ⟶ P.mk y) : (P.mk x : P S m') ⟶ P.mk y :=
  (P.map f).map p

@[simp]
lemma P.mapHom_id (f : m ⟶ m') (x : S _⦋0⦌) : P.mapHom f (𝟙 (P.mk x)) = 𝟙 (P.mk x) :=
  (P.map f).map_id _

@[simp]
lemma P.mapHom_comp (f : m ⟶ m') (p : (P.mk x : P S m) ⟶ P.mk y) (q : (P.mk y : P S m) ⟶ P.mk z) :
    P.mapHom f (p ≫ q) = P.mapHom f p ≫ P.mapHom f q :=
  (P.map f).map_comp p q

@[simp]
lemma P.mapHom_ι (f : m ⟶ m') (g : Gen S m x y) : P.mapHom f (ι g) = ι (g.map f) :=
  P.lift_genMap f g

lemma P.mapHom_one (p : (P.mk x : P S m) ⟶ P.mk y) : P.mapHom (𝟙 m) p = p := by
  induction p using P.induction with
  | id x => exact P.mapHom_id _ x
  | comp p g h =>
    rw [P.mapHom_comp, h, P.mapHom_ι, Gen.map_id]

lemma P.mapHom_mapHom (f : m ⟶ m') (f' : m' ⟶ m'') (p : (P.mk x : P S m) ⟶ P.mk y) :
    P.mapHom (f ≫ f') p = P.mapHom f' (P.mapHom f p) := by
  induction p using P.induction with
  | id x => simp only [P.mapHom_id]
  | comp p g h =>
    rw [P.mapHom_comp, h, P.mapHom_comp, P.mapHom_comp, P.mapHom_ι, P.mapHom_ι, P.mapHom_ι,
      Gen.map_comp]

end Thickening

/-- The path category `Path[S]` of a simplicial set `S` (Kerodon), also written `𝔠[S]` (HTT): the
simplicial category freely generated by `S`. Its objects are the vertices of `S`. -/
def Thickening (S : SSet.{u}) : Type u := S _⦋0⦌

namespace Thickening

variable {m m' m'' : SimplexCategoryᵒᵖ}

/-- The simplicial set of morphisms from `x` to `y` in the path category of `S`. -/
def Hom (x y : S _⦋0⦌) : SSet.{u} where
  obj m := (P.mk x : P S m) ⟶ P.mk y
  map f := TypeCat.ofHom fun p ↦ P.mapHom f p
  map_id m := by
    ext p
    exact P.mapHom_one p
  map_comp f f' := by
    ext p
    exact P.mapHom_mapHom f f' p

variable {S}

instance : Category.{u} (Thickening S) where
  Hom x y := (P.mk x : P S (op ⦋0⦌)) ⟶ P.mk y
  id x := 𝟙 (P.mk x)
  comp p q := p ≫ q

instance : SimplicialCategory (Thickening S) where
  Hom x y := Hom S x y
  id x :=
    { app := fun m ↦ TypeCat.ofHom fun _ ↦ 𝟙 (P.mk x)
      naturality := fun _ _ f ↦ by
        ext
        exact (P.mapHom_id f x).symm }
  comp x y z :=
    { app := fun m ↦ TypeCat.ofHom fun p ↦ p.1 ≫ p.2
      naturality := fun _ _ f ↦ by
        ext p
        exact (P.mapHom_comp f p.1 p.2).symm }
  id_comp x y := by
    ext m p
    exact Category.id_comp p
  comp_id x y := by
    ext m p
    exact Category.comp_id p
  assoc w x y z := by
    ext m ⟨p, q, r⟩
    exact Category.assoc p q r
  homEquiv {x y} := (SSet.unitHomEquiv (Hom S x y)).symm
  homEquiv_id x := by
    ext m ⟨⟩
    exact P.mapHom_id _ x
  homEquiv_comp p q := by
    ext m ⟨⟩
    exact P.mapHom_comp _ p q

lemma mk_ι {x y : S _⦋0⦌} (g : Gen S m x y) :
    (⟨x, y, ι g⟩ : HSimplex (Thickening S) m) = ⟨_, _, ι ⟨g.σ, g.c, rfl, rfl⟩⟩ := by
  obtain ⟨σ, c, rfl, rfl⟩ := g
  rfl

/-- The simplicial functor `Path[n] ⥤ Path[S]` given by an `n`-simplex of `S`. -/
def unitSimplex {n : ℕ} (σ : S _⦋n⦌) : Simplex (Thickening S) n where
  obj a := vertex S σ a
  map a b :=
    { app := fun m ↦ TypeCat.ofHom fun c ↦ ι ⟨σ, c, rfl, rfl⟩
      naturality := fun _ _ f ↦ by
        ext c
        exact (P.mapHom_ι f (⟨σ, c, rfl, rfl⟩ : Gen S _ (vertex S σ a) (vertex S σ b))).symm }
  map_id a := by
    ext m ⟨⟩
    exact ι_id σ a rfl
  map_comp a b d := by
    ext m ⟨c, c'⟩
    exact (ι_comp σ c c' rfl rfl rfl).symm

variable (S) in
/-- The unit of the adjunction between the path category and the simplicial nerve. -/
def unit : S ⟶ SimplicialNerve (Thickening S) where
  app n := TypeCat.ofHom fun σ ↦ unitSimplex (n := n.unop.len) σ
  naturality n n' f := by
    ext σ
    change unitSimplex (S.map f.unop.op σ) = restr f.unop (unitSimplex σ)
    refine eq_of_val fun a b m c ↦ ?_
    exact (congr_arg (HSimplex.mk _ _) (ι_restr f.unop σ c rfl rfl
      (vertex_map f.unop σ a).symm (vertex_map f.unop σ b).symm)).trans (mk_ι _)

lemma vertex_zero (x : S _⦋0⦌) : vertex S x ⟨⟨0⟩⟩ = x := by
  rw [vertex, SimplexCategory.const_eq_id]
  exact S.map_id_apply _ x

section Lift

variable {D : Type u} [Category.{u} D] [SimplicialCategory D] (φ : S ⟶ SimplicialNerve D)
  {x y z : S _⦋0⦌}

/-- The simplex of the simplicial nerve of `D` given by a simplex of `S`. -/
abbrev simplex {n : ℕ} (σ : S _⦋n⦌) : Simplex D n := φ.app _ σ

lemma simplex_map {n n' : ℕ} (θ : ⦋n'⦌ ⟶ ⦋n⦌) (σ : S _⦋n⦌) :
    simplex φ (S.map θ.op σ) = restr θ (simplex φ σ) :=
  NatTrans.naturality_apply φ θ.op σ

/-- The value on objects of the simplicial functor `Path[S] ⥤ D` given by `φ`. -/
def liftObj (x : S _⦋0⦌) : D := (simplex φ x).obj ⟨⟨0⟩⟩

lemma simplex_obj {n : ℕ} (σ : S _⦋n⦌) (a : Th.{u} n) :
    (simplex φ σ).obj a = liftObj φ (vertex S σ a) := by
  rw [liftObj, vertex, simplex_map]
  rfl

/-- The value on a generating morphism of the simplicial functor `Path[S] ⥤ D` given by `φ`. -/
def genVal (g : Gen S m x y) : (sHom (liftObj φ x) (liftObj φ y)).obj m :=
  (val (simplex φ g.σ) g.c).get ((simplex_obj φ g.σ g.a).trans (congr_arg _ g.src))
    ((simplex_obj φ g.σ g.b).trans (congr_arg _ g.tgt))

lemma mk_genVal (g : Gen S m x y) :
    (⟨_, _, genVal φ g⟩ : HSimplex D m) = val (simplex φ g.σ) g.c :=
  HSimplex.mk_get _ _ _

/-- The values on generating morphisms, as a prefunctor. -/
def liftGen (m : SimplexCategoryᵒᵖ) : Vtx S m ⥤q Level D m where
  obj x := ⟨liftObj φ x.as⟩
  map g := genVal φ g

lemma lift_liftGen (g : Gen S m x y) : (Paths.lift (liftGen φ m)).map g.toPath = genVal φ g :=
  Paths.lift_toPath (liftGen φ m) (X := ⟨x⟩) (Y := ⟨y⟩) g

/-- The functor `P S m ⥤ Level D m` given by `φ`. -/
def liftFunctor (m : SimplexCategoryᵒᵖ) : P S m ⥤ Level D m :=
  CategoryTheory.Quotient.lift _ (Paths.lift (liftGen φ m)) (by
    rintro _ _ _ _ (⟨θ, σ, c, hx, hy, hx', hy'⟩ | ⟨σ, c, c', hx, hy, hz⟩ | ⟨σ, a, hx⟩)
    · rw [lift_liftGen, lift_liftGen]
      refine HSimplex.mk_injective ?_
      rw [mk_genVal, mk_genVal, simplex_map]
      rfl
    · rw [CategoryTheory.Functor.map_comp, lift_liftGen, lift_liftGen, lift_liftGen]
      exact HSimplex.mk_injective ((HSimplex.hcomp_mk _ _).symm.trans
        ((congr_arg₂ HSimplex.hcomp (mk_genVal φ ⟨σ, c, hx, hy⟩)
          (mk_genVal φ ⟨σ, c', hy, hz⟩)).trans
          ((val_union _ c c').symm.trans (mk_genVal φ ⟨σ, union c c', hx, hz⟩).symm)))
    · rw [CategoryTheory.Functor.map_id, lift_liftGen]
      exact HSimplex.mk_injective ((mk_genVal φ ⟨σ, idS a m, hx, hx⟩).trans
        ((congr_arg (HSimplex.mk _ _) (map_idS _ a m)).trans
          (HSimplex.mk_idS_congr ((simplex_obj φ σ a).trans (congr_arg _ hx)) m))))

/-- The value on a morphism of `P S m` of the simplicial functor `Path[S] ⥤ D` given by `φ`. -/
def liftHom (p : (P.mk x : P S m) ⟶ P.mk y) : (sHom (liftObj φ x) (liftObj φ y)).obj m :=
  (liftFunctor φ m).map p

lemma liftHom_id (x : S _⦋0⦌) (m : SimplexCategoryᵒᵖ) :
    liftHom φ (𝟙 (P.mk x : P S m)) = idS (liftObj φ x) m :=
  (liftFunctor φ m).map_id _

lemma liftHom_comp (p : (P.mk x : P S m) ⟶ P.mk y) (q : (P.mk y : P S m) ⟶ P.mk z) :
    liftHom φ (p ≫ q) = comp (liftHom φ p) (liftHom φ q) :=
  (liftFunctor φ m).map_comp p q

lemma liftHom_ι (g : Gen S m x y) : liftHom φ (ι g) = genVal φ g :=
  lift_liftGen φ g

lemma liftHom_mapHom (f : m ⟶ m') (p : (P.mk x : P S m) ⟶ P.mk y) :
    liftHom φ (P.mapHom f p) = (sHom _ _).map f (liftHom φ p) := by
  induction p using P.induction with
  | id x => rw [P.mapHom_id, liftHom_id, liftHom_id, idS_map]
  | comp p g h =>
    rw [P.mapHom_comp, liftHom_comp, h, P.mapHom_ι, liftHom_ι, liftHom_comp, liftHom_ι,
      SimplicialCategory.comp_map]
    congr 1
    refine HSimplex.mk_injective ?_
    rw [mk_genVal]
    exact (val_map _ f g.c).trans (congr_arg (HSimplex.map · f) (mk_genVal φ g).symm)

/-- The simplicial functor `Path[S] ⥤ D` corresponding to a map `φ : S ⟶ N^hc(D)`. -/
def lift : EnrichedFunctor SSet.{u} (Thickening S) D where
  obj x := liftObj φ x
  map x y :=
    { app := fun m ↦ TypeCat.ofHom fun p ↦ liftHom φ p
      naturality := fun _ _ f ↦ by
        ext p
        exact liftHom_mapHom φ f p }
  map_id x := by
    ext m ⟨⟩
    exact liftHom_id φ x m
  map_comp x y z := by
    ext m ⟨p, q⟩
    exact liftHom_comp φ p q

/-- `lift φ` extends `φ` along the unit. -/
lemma unit_lift : unit S ≫ SimplicialNerve.map (lift φ) = φ := by
  ext n σ
  change (unitSimplex (n := n.unop.len) σ).comp SSet (lift φ) = simplex φ σ
  refine eq_of_val fun a b m c ↦ ?_
  exact (congr_arg (HSimplex.mk _ _) (liftHom_ι φ _)).trans (mk_genVal φ ⟨σ, c, rfl, rfl⟩)

/-- A simplicial functor out of `Path[S]` is determined by its restriction along the unit. -/
lemma lift_unit_comp (F : EnrichedFunctor SSet.{u} (Thickening S) D) :
    lift (unit S ≫ SimplicialNerve.map F) = F := by
  set φ := unit S ≫ SimplicialNerve.map F
  have hobj (x : S _⦋0⦌) : liftObj φ x = F.obj x := congr_arg F.obj (vertex_zero x)
  have hgen {m : SimplexCategoryᵒᵖ} {x y : S _⦋0⦌} (g : Gen S m x y) :
      val (simplex φ g.σ) g.c = hval F (ι g) := by
    obtain ⟨σ, c, rfl, rfl⟩ := g
    rfl
  refine enrichedFunctor_ext fun x y m p ↦ ?_
  induction p using P.induction with
  | id x =>
    exact (congr_arg (HSimplex.mk _ _) (liftHom_id φ x m)).trans
      ((HSimplex.mk_idS_congr (hobj x) m).trans (hval_id F x m).symm)
  | comp p g h =>
    exact (hval_comp (lift φ) p (ι g)).trans ((congr_arg₂ HSimplex.hcomp h
      ((congr_arg (HSimplex.mk _ _) (liftHom_ι φ g)).trans ((mk_genVal φ g).trans (hgen g)))).trans
        (hval_comp F p (ι g)).symm)

variable (S D) in
/-- The universal property of the path category `Path[S]`: simplicial functors `Path[S] ⥤ D`
correspond to maps of simplicial sets `S ⟶ N^hc(D)`. This is the adjunction between the path
category and the simplicial nerve (homotopy coherent nerve). -/
@[kerodon 00L4]
def homEquiv : EnrichedFunctor SSet.{u} (Thickening S) D ≃ (S ⟶ SimplicialNerve D) where
  toFun F := unit S ≫ SimplicialNerve.map F
  invFun φ := lift φ
  left_inv := lift_unit_comp
  right_inv := unit_lift

end Lift

end Thickening

end SSet
