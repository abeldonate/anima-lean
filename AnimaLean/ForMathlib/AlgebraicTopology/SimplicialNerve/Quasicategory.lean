import Mathlib.AlgebraicTopology.Quasicategory.Basic
import AnimaLean.ForMathlib.AlgebraicTopology.SimplexCategory.Basic
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialCategory.LocallyKan
import AnimaLean.ForMathlib.AlgebraicTopology.SimplicialNerve.HollowCube

universe v u

open CategoryTheory MonoidalCategory Simplicial SimplicialCategory SimplicialThickening
  SimplicialNerve

namespace CategoryTheory.CordierPorter

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

section Fin

variable {k : ℕ} {a b : Th.{v} k} {n : SimplexCategoryᵒᵖ}

lemma Path.bounds (S : a ⟶ b) : ∀ c ∈ S.I, a.as.down ≤ c.down ∧ c.down ≤ b.as.down :=
  fun c hc ↦ ⟨S.left_le c hc, S.le_right c hc⟩

lemma le_of_chain (x : (nerve (a ⟶ b)).obj n) : a.as.down ≤ b.as.down :=
  (x.obj 0).left_le _ (x.obj 0).right

end Fin

section Horn

variable {n : ℕ} {i : Fin (n + 3)}
  (σ₀ : (SSet.horn.{max u v} (n + 2) i : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- A map `f : [p] ⟶ [n + 2]` lies in the horn `Λ[n + 2, i]` if it misses a vertex `c ≠ i`. -/
def InHorn {p : ℕ} (i : Fin (n + 3)) (f : ⦋p⦌ ⟶ ⦋n + 2⦌) : Prop :=
  ∃ c, c ≠ i ∧ ∀ t, f.toOrderHom t ≠ c

/-- The simplex of the horn given by a map `f` in the horn. -/
def hs.{w} {p : ℕ} (f : ⦋p⦌ ⟶ ⦋n + 2⦌) (hf : InHorn i f) :
    (SSet.horn.{w} (n + 2) i : SSet.{w}).obj (Opposite.op ⦋p⦌) :=
  ⟨SSet.stdSimplex.objEquiv.symm f, by
    obtain ⟨c, hci, hc⟩ := hf
    rw [SSet.mem_horn_iff, Ne, Set.eq_univ_iff_forall]
    exact fun h ↦ (h c).elim (fun ⟨t, ht⟩ ↦ hc t ht) hci⟩

/-- The value of `σ₀` on the horn simplex given by `f`. -/
def sv {p : ℕ} (f : ⦋p⦌ ⟶ ⦋n + 2⦌) (hf : InHorn i f) : Simplex C p :=
  σ₀.app _ (hs.{max u v} f hf)

lemma InHorn.comp {p q : ℕ} {f : ⦋p⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i f) (g : ⦋q⦌ ⟶ ⦋p⦌) :
    InHorn i (g ≫ f) := by
  obtain ⟨c, hci, hc⟩ := hf
  exact ⟨c, hci, fun t ↦ hc _⟩

lemma restr_sv {p q : ℕ} (f : ⦋p⦌ ⟶ ⦋n + 2⦌) (hf : InHorn i f) (g : ⦋q⦌ ⟶ ⦋p⦌) :
    restr g (sv σ₀ f hf) = sv σ₀ (g ≫ f) (hf.comp g) :=
  (NatTrans.naturality_apply σ₀ g.op (hs.{max u v} f hf)).symm

lemma sv_congr {p : ℕ} {f f' : ⦋p⦌ ⟶ ⦋n + 2⦌} (hf : InHorn i f) (h : f = f') :
    sv σ₀ f hf = sv σ₀ f' (h ▸ hf) := by
  subst h
  rfl

lemma InHorn.of_ne {p : ℕ} {f : ⦋p⦌ ⟶ ⦋n + 2⦌} {c : Fin (n + 3)} (hc : c ≠ i)
    (hf : ∀ t, f.toOrderHom t ≠ c) : InHorn i f :=
  ⟨c, hc, hf⟩

/-- The degenerate `(n + 2)`-simplex `s_j(F_j)` built from the face `F_j` of the horn. -/
noncomputable def G (j : Fin (n + 3)) (hj : j ≠ i) : Simplex C (n + 2) :=
  sv σ₀ (SimplexCategory.collapse j j) (.of_ne hj fun t ↦ (SimplexCategory.collapse_ne j j t).1)

lemma restr_δ_G (j : Fin (n + 3)) (hj : j ≠ i) :
    restr (SimplexCategory.δ j) (G σ₀ j hj) = σ₀.app _ (SSet.horn.face i j hj) :=
  (restr_sv ..).trans (sv_congr σ₀ (f' := SimplexCategory.δ j) _
    (SimplexCategory.comp_collapse _ fun t ↦ ⟨Fin.succAbove_ne j t, Fin.succAbove_ne j t⟩))

/-- The degenerate simplices `G j` and `G k` agree on every chain of paths avoiding `j` and
`k`: both agree there with the horn simplex given by a collapse onto the face missing `j` and
`k`. -/
lemma val_G_eq {j k : Fin (n + 3)} (hj : j ≠ i) (hk : k ≠ i) {a b : Th (n + 2)}
    {m : SimplexCategoryᵒᵖ} (x : (nerve (a ⟶ b)).obj m)
    (hx : ∀ t, ∀ c ∈ (x.obj t).I, c.down ≠ j ∧ c.down ≠ k) :
    val (G σ₀ j hj) x = val (G σ₀ k hk) x := by
  have key (l : Fin (n + 3)) (hl : l ≠ i)
      (hg : ∀ t, (SimplexCategory.collapse j k).toOrderHom t ≠ l) :
      val (G σ₀ l hl) x = val (sv σ₀ (SimplexCategory.collapse j k) (.of_ne hl hg)) x := by
    rw [← val_restr_of_fix (SimplexCategory.collapse j k) _ x fun t c hc ↦ ULift.ext _ _
      (SimplexCategory.collapse_apply (hx t c hc).1 (hx t c hc).2), G, restr_sv]
    exact congr_arg (val · x) (sv_congr σ₀ _
      (SimplexCategory.comp_collapse _ fun t ↦ ⟨hg t, hg t⟩))
  exact (key j hj fun t ↦ (SimplexCategory.collapse_ne j k t).1).trans
    (key k hk fun t ↦ (SimplexCategory.collapse_ne j k t).2).symm

lemma obj_G_eq {j k : Fin (n + 3)} (hj : j ≠ i) (hk : k ≠ i) (a : Th (n + 2))
    (haj : a.as.down ≠ j) (hak : a.as.down ≠ k) :
    (G σ₀ j hj).obj a = (G σ₀ k hk).obj a :=
  congr_arg HSimplex.src (val_G_eq σ₀ hj hk (idS a (Opposite.op ⦋0⦌)) (fun _ c hc ↦ by
    obtain rfl : c = a.as := hc
    exact ⟨haj, hak⟩))

end Horn

section Filler

variable {n : ℕ} {i : Fin (n + 3)}
  (σ₀ : (SSet.horn.{max u v} (n + 2) i : SSet.{max u v}) ⟶ SimplicialNerve C)
  (h0 : 0 < i) (hn : i < Fin.last (n + 2))

/-- The degenerate simplex built from the last face. -/
noncomputable abbrev Gl : Simplex C (n + 2) := G σ₀ (Fin.last (n + 2)) hn.ne'

/-- The degenerate simplex built from the first face. -/
noncomputable abbrev G0 : Simplex C (n + 2) := G σ₀ 0 h0.ne

/-- The objects of the filler. -/
noncomputable def X (a : Th.{v} (n + 2)) : C :=
  if a.as.down < Fin.last _ then (Gl σ₀ hn).obj a else (G0 σ₀ h0).obj a

lemma obj_G {k : Fin (n + 3)} (hk : k ≠ i) (a : Th.{v} (n + 2)) (ha : a.as.down ≠ k) :
    (G σ₀ k hk).obj a = X σ₀ h0 hn a := by
  rw [X]
  split_ifs with h
  · exact obj_G_eq σ₀ hk _ a ha h.ne
  · exact obj_G_eq σ₀ hk _ a ha (Fin.last_pos.trans_le (not_lt.1 h)).ne'

variable {a b : Th.{v} (n + 2)} {p : SimplexCategoryᵒᵖ} (x : (nerve (a ⟶ b)).obj p)

/-- The value on a chain of paths through the vertex `k`, obtained by composing the values on the
two halves: the first half avoids `n + 2` and the second half avoids `0`. -/
noncomputable def contVal (k : Fin (n + 3)) (h₁ : a.as.down ≤ k) (h₂ : k ≤ b.as.down) :
    HSimplex C p :=
  HSimplex.hcomp (val (Gl σ₀ hn) (sub a (pt n k) h₁ x)) (val (G0 σ₀ h0) (sub (pt n k) b h₂ x))

/-- `v` is a value on the chain `x` prescribed by the horn: `x` avoids some `k ≠ i` and `v` is
the value of the face opposite `k`, or `x` passes through some `k` and `v` is the composite of
the values on the two halves. -/
def Valid (v : HSimplex C p) : Prop :=
  (∃ (k : Fin (n + 3)) (hk : k ≠ i), (∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∉ (x.obj t).I) ∧
    v = val (G σ₀ k hk) x) ∨
  (∃ (k : Fin (n + 3)) (h₁ : a.as.down < k) (h₂ : k < b.as.down),
    (∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I) ∧ v = contVal σ₀ h0 hn x k h₁.le h₂.le)

/-- The chains with a valid value are those of `hollow`. -/
lemma exists_valid_iff : (∃ v, Valid σ₀ h0 hn x v) ↔ x ∈ (hollow n i a b).obj p :=
  ⟨by
    rintro ⟨v, ⟨k, hk, hx, -⟩ | ⟨k, h₁, h₂, hx, -⟩⟩
    exacts [Or.inl ⟨k, hk, hx⟩, Or.inr ⟨k, h₁, h₂, hx⟩], by
    rintro (⟨k, hk, hx⟩ | ⟨k, h₁, h₂, hx⟩)
    exacts [⟨_, Or.inl ⟨k, hk, hx, rfl⟩⟩, ⟨_, Or.inr ⟨k, h₁, h₂, hx, rfl⟩⟩]⟩

section Unique

lemma ulift_ne {k : ℕ} {c : ULift.{v} (Fin (k + 1))} {j : Fin (k + 1)} (h : c ≠ ⟨j⟩) : c.down ≠ j :=
  fun e ↦ h (ULift.ext _ _ e)

/-- On a chain through `k`, splitting at `k` and composing recovers the value of any `E`. -/
lemma val_eq_hcomp (E : Simplex C (n + 2)) (k : Fin (n + 3)) {a₁ b₁ a b : Th (n + 2)}
    (y : (nerve (a₁ ⟶ b₁)).obj p) (ha : a.as ≤ ⟨k⟩) (hb : (⟨k⟩ : ULift (Fin (n + 3))) ≤ b.as)
    (hy : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ (y.obj t).I) :
    val E (sub a b (ha.trans hb) y) =
      HSimplex.hcomp (val E (sub a (pt n k) ha y)) (val E (sub (pt n k) b hb y)) :=
  (val_congr E rfl rfl _ (union (sub a (pt n k) ha y) (sub (pt n k) b hb y))
    (fun t ↦ (subI_union _ (hy t) ha hb).symm)).trans (val_union _ _ _)

lemma sub_self_eq (a b : Th (n + 2)) (y : (nerve (a ⟶ b)).obj p) :
    sub a b ((y.obj 0).left_le _ (y.obj 0).right) y = y :=
  chain_ext fun t ↦ subI_self _ (y.obj t).left (y.obj t).right (Path.bounds _)

include h0 hn in
lemma val_eq_contVal {k : Fin (n + 3)} (hk : k ≠ i)
    (hx : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∉ (x.obj t).I) {k' : Fin (n + 3)}
    (h₁ : a.as.down < k') (h₂ : k' < b.as.down)
    (hx' : ∀ t, (⟨k'⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I) :
    val (G σ₀ k hk) x = contVal σ₀ h0 hn x k' h₁.le h₂.le := by
  have hka : a.as ≠ ⟨k⟩ := fun e ↦ hx 0 (e ▸ (x.obj 0).left)
  have hkb : b.as ≠ ⟨k⟩ := fun e ↦ hx 0 (e ▸ (x.obj 0).right)
  have hkk' : (⟨k'⟩ : ULift (Fin (n + 3))) ≠ ⟨k⟩ := fun e ↦ hx 0 (e ▸ hx' 0)
  conv_lhs => rw [← sub_self_eq _ _ x]
  rw [val_eq_hcomp _ k' x h₁.le h₂.le hx', contVal]
  congr 1
  · refine val_G_eq σ₀ _ _ _ (fun t c hc ↦ ⟨ulift_ne (subI_ne hc (hx t) hka hkk'), ?_⟩)
    exact ((Path.bounds _ c hc).2.trans_lt (h₂.trans_le (Fin.le_last _))).ne
  · refine val_G_eq σ₀ _ _ _ (fun t c hc ↦ ⟨ulift_ne (subI_ne hc (hx t) hkk' hkb), ?_⟩)
    exact ((Fin.zero_le _).trans_lt (h₁.trans_le (Path.bounds _ c hc).1)).ne'

include h0 hn in
lemma contVal_eq_of_lt {k k' : Fin (n + 3)} (h₁ : a.as.down < k) (hkk' : k < k')
    (h₂ : k' < b.as.down) (hx : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I)
    (hx' : ∀ t, (⟨k'⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I) :
    contVal σ₀ h0 hn x k h₁.le (hkk'.trans h₂).le =
      contVal σ₀ h0 hn x k' (h₁.trans hkk').le h₂.le := by
  have hk : 0 < k := (Fin.zero_le _).trans_lt h₁
  have hk' : k' < Fin.last _ := h₂.trans_le (Fin.le_last _)
  have e₁ := val_eq_hcomp (G0 σ₀ h0) k' x (a := pt n k) (b := b) hkk'.le h₂.le hx'
  have e₂ := val_eq_hcomp (Gl σ₀ hn) k x (a := a) (b := pt n k') h₁.le hkk'.le hx
  have e₃ : val (G0 σ₀ h0) (sub (pt n k) (pt n k') hkk'.le x) =
      val (Gl σ₀ hn) (sub (pt n k) (pt n k') hkk'.le x) :=
    val_G_eq σ₀ _ _ _ (fun t c hc ↦ ⟨(hk.trans_le (Path.bounds _ c hc).1).ne',
      ((Path.bounds _ c hc).2.trans_lt hk').ne⟩)
  rw [contVal, contVal, e₁, e₃, e₂]
  exact (HSimplex.hcomp_assoc _ _ _ rfl
    (obj_G_eq σ₀ _ _ (pt n k') hk'.ne (hk.trans hkk').ne')).symm

include h0 hn in
lemma valid_unique {v w : HSimplex C p} (hv : Valid σ₀ h0 hn x v) (hw : Valid σ₀ h0 hn x w) :
    v = w := by
  rcases hv with ⟨k, hk, hx, rfl⟩ | ⟨k, h₁, h₂, hx, rfl⟩ <;>
    rcases hw with ⟨k', hk', hx', rfl⟩ | ⟨k', h₁', h₂', hx', rfl⟩
  · exact val_G_eq σ₀ hk hk' x (fun t c hc ↦
      ⟨ulift_ne (fun e ↦ hx t (e ▸ hc)), ulift_ne (fun e ↦ hx' t (e ▸ hc))⟩)
  · exact val_eq_contVal σ₀ h0 hn x hk hx h₁' h₂' hx'
  · exact (val_eq_contVal σ₀ h0 hn x hk' hx' h₁ h₂ hx).symm
  · rcases lt_trichotomy k k' with h | rfl | h
    · exact contVal_eq_of_lt σ₀ h0 hn x h₁ h h₂' hx hx'
    · rfl
    · exact (contVal_eq_of_lt σ₀ h0 hn x h₁' h h₂ hx' hx).symm

lemma valid_map {v : HSimplex C p} (hv : Valid σ₀ h0 hn x v) {p' : SimplexCategoryᵒᵖ}
    (f : p ⟶ p') : Valid σ₀ h0 hn ((nerve _).map f x) (v.map f) := by
  rcases hv with ⟨k, hk, hx, rfl⟩ | ⟨k, h₁, h₂, hx, rfl⟩
  · exact Or.inl ⟨k, hk, fun t ↦ hx _, (val_map _ f x).symm⟩
  · refine Or.inr ⟨k, h₁, h₂, fun t ↦ hx _, ?_⟩
    rw [contVal, contVal, sub_map, sub_map, val_map, val_map, HSimplex.hcomp_map]

lemma valid_src {v : HSimplex C p} (hv : Valid σ₀ h0 hn x v) : v.src = X σ₀ h0 hn a := by
  rcases hv with ⟨k, hk, hx, rfl⟩ | ⟨k, h₁, h₂, hx, rfl⟩
  · exact obj_G σ₀ h0 hn hk a (ulift_ne fun e ↦ hx 0 (e ▸ (x.obj 0).left))
  · exact (HSimplex.hcomp_src _ _).trans (obj_G σ₀ h0 hn _ a (h₁.trans_le (Fin.le_last _)).ne)

lemma valid_tgt {v : HSimplex C p} (hv : Valid σ₀ h0 hn x v) : v.tgt = X σ₀ h0 hn b := by
  rcases hv with ⟨k, hk, hx, rfl⟩ | ⟨k, h₁, h₂, hx, rfl⟩
  · exact obj_G σ₀ h0 hn hk b (ulift_ne fun e ↦ hx 0 (e ▸ (x.obj 0).right))
  · have hk : 0 < k := (Fin.zero_le _).trans_lt h₁
    exact (HSimplex.hcomp_tgt _ _ (obj_G_eq σ₀ _ _ (pt n k)
      (h₂.trans_le (Fin.le_last _)).ne hk.ne')).trans (obj_G σ₀ h0 hn _ b (hk.trans h₂).ne')

end Unique

variable (a b) in
/-- The map on `hollow` determined by the horn: it sends a chain to its valid value. -/
noncomputable def hollowMap :
    (hollow.{v} n i a b : SSet.{v}) ⟶ sHom (X σ₀ h0 hn a) (X σ₀ h0 hn b) :=
  have hv {p} (x : (hollow.{v} n i a b).obj p) := (exists_valid_iff σ₀ h0 hn x.1).2 x.2
  mkHom (fun _ x ↦ (hv x).choose) (fun _ x ↦ valid_src σ₀ h0 hn x.1 (hv x).choose_spec)
    (fun _ x ↦ valid_tgt σ₀ h0 hn x.1 (hv x).choose_spec)
    (fun _ _ f x ↦ valid_unique σ₀ h0 hn _ (hv _).choose_spec
      (valid_map σ₀ h0 hn x.1 (hv x).choose_spec f))

variable [LocallyKan C]

variable (a b) in
/-- The maps on hom-objects of the filler: an extension of `hollowMap` to all chains of paths,
which exists because `sHom (X a) (X b)` is a Kan complex. -/
noncomputable def fillerMap : nerve (a ⟶ b) ⟶ sHom (X σ₀ h0 hn a) (X σ₀ h0 hn b) :=
  (SSet.anodyneExtensions.exists_extension (anodyne_hollow n i h0 hn a b)
    (hollowMap σ₀ h0 hn a b)).choose

/-- The filler takes the valid value on every chain which has one. -/
lemma fillerMap_eq {v : HSimplex C p} (hv : Valid σ₀ h0 hn x v) :
    (⟨_, _, (fillerMap σ₀ h0 hn a b).app p x⟩ : HSimplex C p) = v := by
  have hx := (exists_valid_iff σ₀ h0 hn x).1 ⟨v, hv⟩
  have h := congr_arg (fun g ↦ g.app p ⟨x, hx⟩)
    (SSet.anodyneExtensions.exists_extension (anodyne_hollow n i h0 hn a b)
      (hollowMap σ₀ h0 hn a b)).choose_spec
  change (fillerMap σ₀ h0 hn a b).app p x = (hollowMap σ₀ h0 hn a b).app p ⟨x, hx⟩ at h
  rw [h, hollowMap, mk_mkHom_app]
  exact valid_unique σ₀ h0 hn x ((exists_valid_iff σ₀ h0 hn x).2 hx).choose_spec hv

lemma fillerMap_idS (a : Th.{v} (n + 2)) (p : SimplexCategoryᵒᵖ) :
    (fillerMap σ₀ h0 hn a a).app p (idS a p) = idS (X σ₀ h0 hn a) p := by
  refine eq_of_heq (HSimplex.mk.inj (fillerMap_eq σ₀ h0 hn (idS a p) (v := ⟨_, _, idS _ p⟩) ?_)).2.2
  by_cases ha : a.as.down < Fin.last _
  · refine Or.inl ⟨Fin.last _, hn.ne', fun t ht ↦ ha.ne (congr_arg ULift.down ht).symm, ?_⟩
    rw [X, ite_eq_left ha]
    exact congr_arg (HSimplex.mk _ _) (map_idS _ a p).symm
  · refine Or.inl ⟨0, h0.ne, fun t ht ↦ ha ((congr_arg ULift.down ht).symm ▸ Fin.last_pos), ?_⟩
    rw [X, ite_eq_right ha]
    exact congr_arg (HSimplex.mk _ _) (map_idS _ a p).symm

lemma fillerMap_union {c : Th.{v} (n + 2)} (y : (nerve (b ⟶ c)).obj p) :
    (fillerMap σ₀ h0 hn a c).app p (union x y) =
      comp ((fillerMap σ₀ h0 hn a b).app p x) ((fillerMap σ₀ h0 hn b c).app p y) := by
  rcases (le_of_chain x).eq_or_lt with hab | hab
  · obtain rfl := th_ext hab
    rw [chain_eq_id x, id_union, fillerMap_idS, idS_comp]
  rcases (le_of_chain y).eq_or_lt with hbc | hbc
  · obtain rfl := th_ext hbc
    rw [chain_eq_id y, union_id, fillerMap_idS, comp_idS]
  obtain ⟨⟨k⟩⟩ := b
  -- `x` avoids `n + 2`, `y` avoids `0`, and `union x y` passes through `k`
  have hx : Valid σ₀ h0 hn x (val (Gl σ₀ hn) x) := Or.inl ⟨_, hn.ne', fun t ht ↦
    (((x.obj t).le_right _ ht).trans_lt hbc).not_ge (Fin.le_last _), rfl⟩
  have hy : Valid σ₀ h0 hn y (val (G0 σ₀ h0) y) := Or.inl ⟨_, h0.ne, fun t ht ↦
    (hab.trans_le ((y.obj t).left_le _ ht)).not_ge (Fin.zero_le _), rfl⟩
  have hxy : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ ((union x y).obj t).I :=
    fun t ↦ Or.inr (y.obj t).left
  refine eq_of_heq (HSimplex.mk.inj ((fillerMap_eq σ₀ h0 hn _
    (Or.inr ⟨k, hab, hbc, hxy, rfl⟩)).trans ?_)).2.2
  rw [← HSimplex.hcomp_mk, fillerMap_eq σ₀ h0 hn x hx, fillerMap_eq σ₀ h0 hn y hy, contVal]
  congr 1
  · exact val_congr _ rfl rfl _ _ fun t ↦ subI_union_left _ _ (x.obj t).left (x.obj t).right
      (Path.bounds _) (fun c hc ↦ (y.obj t).left_le c hc)
  · exact val_congr _ rfl rfl _ _ fun t ↦ subI_union_right _ _ (y.obj t).left (y.obj t).right
      (fun c hc ↦ (x.obj t).le_right c hc) (Path.bounds _)

/-- The filler of the horn. -/
noncomputable def filler : Simplex C (n + 2) where
  obj := X σ₀ h0 hn
  map a b := fillerMap σ₀ h0 hn a b
  map_id a := by
    ext p ⟨⟩
    exact fillerMap_idS σ₀ h0 hn a p
  map_comp a b c := by
    ext p ⟨x, y⟩
    exact fillerMap_union σ₀ h0 hn x y

lemma val_filler {v : HSimplex C p} (hv : Valid σ₀ h0 hn x v) : val (filler σ₀ h0 hn) x = v :=
  fillerMap_eq σ₀ h0 hn x hv

lemma filler_face (j : Fin (n + 3)) (hj : j ≠ i) :
    (SimplicialNerve C).δ j (filler σ₀ h0 hn) = σ₀.app _ (SSet.horn.face i j hj) := by
  rw [← restr_δ_G σ₀ j hj]
  change restr (SimplexCategory.δ j) (filler σ₀ h0 hn) = restr (SimplexCategory.δ j) (G σ₀ j hj)
  refine eq_of_val fun a b q x ↦ ?_
  rw [val_restr, val_restr]
  refine val_filler σ₀ h0 hn _ (Or.inl ⟨j, hj, fun t ht ↦ ?_, rfl⟩)
  obtain ⟨c, -, hc⟩ := ht
  exact Fin.succAbove_ne j c.down (congr_arg ULift.down hc)

end Filler

end CategoryTheory.CordierPorter

namespace CategoryTheory

open SimplicialCategory

variable (C : Type u) [Category.{v} C] [SimplicialCategory C]

/-- **Cordier–Porter**: the simplicial nerve of a locally Kan simplicial category is a
quasicategory. -/
@[kerodon 00LJ]
instance SimplicialNerve.quasicategory [LocallyKan C] :
    SSet.Quasicategory (SimplicialNerve C) :=
  SSet.quasicategory_of_filler _ fun _ _ σ₀ h0 hn ↦
    ⟨CordierPorter.filler σ₀ h0 hn, CordierPorter.filler_face σ₀ h0 hn⟩

end CategoryTheory
