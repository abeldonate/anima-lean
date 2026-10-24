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

lemma InHorn.collapse {j : Fin (n + 3)} (hj : j ≠ i) : InHorn i (SimplexCategory.collapse j) :=
  ⟨j, hj, fun _ ↦ Fin.succAbove_ne j _⟩

/-- The degenerate `(n + 2)`-simplex `s_j(F_j)` built from the face `F_j` of the horn. -/
noncomputable def G (j : Fin (n + 3)) (hj : j ≠ i) : Simplex C (n + 2) :=
  sv σ₀ (SimplexCategory.collapse j) (InHorn.collapse hj)

lemma restr_δ_G (j : Fin (n + 3)) (hj : j ≠ i) :
    restr (SimplexCategory.δ j) (G σ₀ j hj) = σ₀.app _ (SSet.horn.face i j hj) :=
  (restr_sv ..).trans (sv_congr σ₀ (f' := SimplexCategory.δ j) _ (by
    rw [SimplexCategory.collapse, ← Category.assoc,
      (SimplexCategory.exists_retraction_δ j).choose_spec, Category.id_comp]))

/-- The degenerate simplices `G j` and `G k` agree on every chain of paths avoiding `j` and
`k`. -/
lemma val_G_eq {j k : Fin (n + 3)} (hj : j ≠ i) (hk : k ≠ i) {a b : Th (n + 2)}
    {m : SimplexCategoryᵒᵖ} (x : (nerve (a ⟶ b)).obj m)
    (hx : ∀ t, ∀ c ∈ (x.obj t).I, c.down ≠ j ∧ c.down ≠ k) :
    val (G σ₀ j hj) x = val (G σ₀ k hk) x := by
  by_cases hjk : j = k
  · subst hjk
    rfl
  obtain ⟨d, _, hd, hd'⟩ := SimplexCategory.exists_codim_two hjk
  refine val_eq_of_restr_eq d ?_ x (fun t c hc ↦ ?_)
  · rw [G, G, restr_sv, restr_sv]
    exact (sv_congr σ₀ _ (SimplexCategory.comp_collapse d (fun t ↦ (hd t).1))).trans
      (sv_congr σ₀ _ (SimplexCategory.comp_collapse d (fun t ↦ (hd t).2))).symm
  · obtain ⟨t', ht'⟩ := hd' c.down (hx t c hc).1 (hx t c hc).2
    exact ⟨⟨t'⟩, congr_arg ULift.up ht'⟩

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

/-- The vertex `k` of `[n + 2]`. -/
abbrev pt (k : Fin (n + 3)) : Th.{v} (n + 2) := ⟨⟨k⟩⟩

/-- The degenerate simplex built from the last face. -/
noncomputable abbrev Gl : Simplex C (n + 2) := G σ₀ (Fin.last (n + 2)) hn.ne'

/-- The degenerate simplex built from the first face. -/
noncomputable abbrev G0 : Simplex C (n + 2) := G σ₀ 0 h0.ne

/-- The value on a chain of paths from `0` to `n + 2` through the interior vertex `k`, obtained by
composing the values on the two halves. -/
noncomputable def contVal {p : SimplexCategoryᵒᵖ} (x : (nerve (a0.{v} n ⟶ am n)).obj p)
    (k : Fin (n + 3)) : HSimplex C p :=
  HSimplex.hcomp (val (Gl σ₀ hn) (sub (a0 n) (pt k) (Fin.zero_le _) x))
    (val (G0 σ₀ h0) (sub (pt k) (am n) (Fin.le_last _) x))

/-- `v` is a value on the chain `x` prescribed by the horn. -/
def Valid {p : SimplexCategoryᵒᵖ} (x : (nerve (a0.{v} n ⟶ am n)).obj p) (v : HSimplex C p) :
    Prop :=
  (∃ (k : Fin (n + 3)) (hk : k ≠ i), (∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∉ (x.obj t).I) ∧
    v = val (G σ₀ k hk) x) ∨
  (∃ (k : Fin (n + 3)) (_ : 0 < k) (_ : k < Fin.last _),
    (∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I) ∧ v = contVal σ₀ h0 hn x k)

section Unique

variable {p : SimplexCategoryᵒᵖ} (x : (nerve (a0.{v} n ⟶ am n)).obj p)

lemma ulift_ne {k : ℕ} {c : ULift.{v} (Fin (k + 1))} {j : Fin (k + 1)} (h : c ≠ ⟨j⟩) : c.down ≠ j :=
  fun e ↦ h (ULift.ext _ _ e)

/-- On a chain through `k`, splitting at `k` and composing recovers the value of any `E`. -/
lemma val_eq_hcomp (E : Simplex C (n + 2)) (k : Fin (n + 3)) {a₁ b₁ a b : Th (n + 2)}
    (y : (nerve (a₁ ⟶ b₁)).obj p) (ha : a.as ≤ ⟨k⟩) (hb : (⟨k⟩ : ULift (Fin (n + 3))) ≤ b.as)
    (hy : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ (y.obj t).I) :
    val E (sub a b (ha.trans hb) y) =
      HSimplex.hcomp (val E (sub a (pt k) ha y)) (val E (sub (pt k) b hb y)) :=
  (val_congr E rfl rfl _ (union (sub a (pt k) ha y) (sub (pt k) b hb y))
    (fun t ↦ (subI_union _ (hy t) ha hb).symm)).trans (val_union _ _ _)

lemma sub_self_eq (a b : Th (n + 2)) (y : (nerve (a ⟶ b)).obj p) :
    sub a b ((y.obj 0).left_le _ (y.obj 0).right) y = y :=
  chain_ext fun t ↦ subI_self _ (y.obj t).left (y.obj t).right (Path.bounds _)

include h0 hn in
lemma val_eq_contVal {k : Fin (n + 3)} (hk : k ≠ i)
    (hx : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∉ (x.obj t).I) {k' : Fin (n + 3)} (h₁ : 0 < k')
    (h₂ : k' < Fin.last _) (hx' : ∀ t, (⟨k'⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I) :
    val (G σ₀ k hk) x = contVal σ₀ h0 hn x k' := by
  have hk0 : (⟨0⟩ : ULift (Fin (n + 3))) ≠ ⟨k⟩ := fun e ↦ hx 0 (e ▸ (x.obj 0).left)
  have hkm : (⟨Fin.last _⟩ : ULift (Fin (n + 3))) ≠ ⟨k⟩ := fun e ↦ hx 0 (e ▸ (x.obj 0).right)
  have hkk' : (⟨k'⟩ : ULift (Fin (n + 3))) ≠ ⟨k⟩ := fun e ↦ hx 0 (e ▸ hx' 0)
  conv_lhs => rw [← sub_self_eq _ _ x]
  rw [val_eq_hcomp _ k' x (Fin.zero_le _) (Fin.le_last _) hx', contVal]
  congr 1
  · refine val_G_eq σ₀ _ _ _ (fun t c hc ↦ ⟨ulift_ne (subI_ne hc (hx t) hk0 hkk'), ?_⟩)
    exact (lt_of_le_of_lt (Path.bounds _ c hc).2 h₂).ne
  · refine val_G_eq σ₀ _ _ _ (fun t c hc ↦ ⟨ulift_ne (subI_ne hc (hx t) hkk' hkm), ?_⟩)
    exact (lt_of_lt_of_le h₁ (Path.bounds _ c hc).1).ne'

include h0 hn in
lemma contVal_eq_of_lt {k k' : Fin (n + 3)} (h₁ : 0 < k) (hkk' : k < k') (h₂ : k' < Fin.last _)
    (hx : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I)
    (hx' : ∀ t, (⟨k'⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I) :
    contVal σ₀ h0 hn x k = contVal σ₀ h0 hn x k' := by
  have e₁ := val_eq_hcomp (G0 σ₀ h0) k' x (a := pt k) (b := am n) hkk'.le (Fin.le_last _) hx'
  have e₂ := val_eq_hcomp (Gl σ₀ hn) k x (a := a0 n) (b := pt k') (Fin.zero_le _) hkk'.le hx
  have e₃ : val (G0 σ₀ h0) (sub (pt k) (pt k') hkk'.le x) =
      val (Gl σ₀ hn) (sub (pt k) (pt k') hkk'.le x) :=
    val_G_eq σ₀ _ _ _ (fun t c hc ↦ ⟨(lt_of_lt_of_le h₁ (Path.bounds _ c hc).1).ne',
      (lt_of_le_of_lt (Path.bounds _ c hc).2 h₂).ne⟩)
  rw [contVal, contVal, e₁, e₃, e₂]
  exact (HSimplex.hcomp_assoc _ _ _ rfl
    (obj_G_eq σ₀ _ _ (pt k') h₂.ne (h₁.trans hkk').ne')).symm

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
    rw [contVal, contVal, sub_map, sub_map, val_map, val_map,
      HSimplex.hcomp_map _ _ (obj_G_eq σ₀ _ _ (pt k) h₂.ne h₁.ne')]

end Unique

/-- The objects of the filler. -/
noncomputable def X (a : Th.{v} (n + 2)) : C :=
  if a.as.down < Fin.last _ then (Gl σ₀ hn).obj a else (G0 σ₀ h0).obj a

section Hollow

variable {p : SimplexCategoryᵒᵖ} (x : (nerve (a0.{v} n ⟶ am n)).obj p)

lemma valid_src {v : HSimplex C p} (hv : Valid σ₀ h0 hn x v) : v.src = X σ₀ h0 hn (a0 n) := by
  rw [X, ite_eq_left Fin.last_pos]
  rcases hv with ⟨k, hk, hx, rfl⟩ | ⟨k, h₁, h₂, hx, rfl⟩
  · exact obj_G_eq σ₀ hk _ (a0 n) (fun e ↦ hx 0 (e ▸ (x.obj 0).left)) Fin.last_pos.ne
  · exact HSimplex.hcomp_src _ _

lemma valid_tgt {v : HSimplex C p} (hv : Valid σ₀ h0 hn x v) : v.tgt = X σ₀ h0 hn (am n) := by
  rw [X, ite_eq_right (lt_irrefl _)]
  rcases hv with ⟨k, hk, hx, rfl⟩ | ⟨k, h₁, h₂, hx, rfl⟩
  · exact obj_G_eq σ₀ hk _ (am n) (fun e ↦ hx 0 (e ▸ (x.obj 0).right)) Fin.last_pos.ne'
  · exact HSimplex.hcomp_tgt _ _ (obj_G_eq σ₀ _ _ (pt k) h₂.ne h₁.ne')

lemma exists_valid (hx : x ∈ (hollowP n i h0 hn).obj p) : ∃ v, Valid σ₀ h0 hn x v := by
  rcases (mem_hollowP n i h0 hn x).1 hx with h | ⟨⟨⟨k⟩, h₁, h₂, hki⟩, b, h⟩
  · exact ⟨_, Or.inr ⟨i, h0, hn, h, rfl⟩⟩
  · cases b
    · exact ⟨_, Or.inl ⟨k, hki, fun t ht ↦ by simpa using (h t).1 ht, rfl⟩⟩
    · exact ⟨_, Or.inr ⟨k, h₁, h₂, fun t ↦ (h t).2 rfl, rfl⟩⟩

lemma mem_hollowP_of_avoid {k : Fin (n + 3)} (hk : k ≠ i)
    (hx : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∉ (x.obj t).I) : x ∈ (hollowP n i h0 hn).obj p := by
  refine (mem_hollowP n i h0 hn x).2 (Or.inr ⟨⟨⟨k⟩, ?_, ?_, hk⟩, false, fun t ↦ ?_⟩)
  · exact Fin.pos_iff_ne_zero.2 fun e ↦ hx 0 (by subst e; exact (x.obj 0).left)
  · exact Fin.lt_last_iff_ne_last.2 fun e ↦ hx 0 (by subst e; exact (x.obj 0).right)
  · simpa using hx t

lemma mem_hollowP_of_contain {k : Fin (n + 3)} (h₁ : 0 < k) (h₂ : k < Fin.last _)
    (hx : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ (x.obj t).I) : x ∈ (hollowP n i h0 hn).obj p := by
  by_cases hk : k = i
  · subst hk
    exact (mem_hollowP n k h0 hn x).2 (Or.inl hx)
  · exact (mem_hollowP n i h0 hn x).2
      (Or.inr ⟨⟨⟨k⟩, h₁, h₂, hk⟩, true, fun t ↦ by simpa using hx t⟩)

end Hollow

/-- The map on the hollow cube determined by the horn. -/
noncomputable def hollowMap :
    (hollowP.{v} n i h0 hn : SSet.{v}) ⟶ sHom (X σ₀ h0 hn (a0 n)) (X σ₀ h0 hn (am n)) :=
  mkHom (fun _ x ↦ (exists_valid σ₀ h0 hn x.1 x.2).choose)
    (fun _ x ↦ valid_src σ₀ h0 hn x.1 (exists_valid σ₀ h0 hn x.1 x.2).choose_spec)
    (fun _ x ↦ valid_tgt σ₀ h0 hn x.1 (exists_valid σ₀ h0 hn x.1 x.2).choose_spec)
    (fun _ _ f x ↦ valid_unique σ₀ h0 hn _
      (exists_valid σ₀ h0 hn _ ((hollowP n i h0 hn : SSet.{v}).map f x).2).choose_spec
      (valid_map σ₀ h0 hn x.1 (exists_valid σ₀ h0 hn x.1 x.2).choose_spec f))

variable [LocallyKan C]

/-- An extension of the hollow map to all paths from `0` to `n + 2`. -/
noncomputable def ext :
    nerve (a0.{v} n ⟶ am n) ⟶ sHom (X σ₀ h0 hn (a0 n)) (X σ₀ h0 hn (am n)) :=
  (SSet.anodyneExtensions.exists_extension (anodyne_hollowP n i h0 hn) (hollowMap σ₀ h0 hn)).choose

lemma ext_eq {p : SimplexCategoryᵒᵖ} (x : (nerve (a0.{v} n ⟶ am n)).obj p)
    (hx : x ∈ (hollowP n i h0 hn).obj p) {v : HSimplex C p} (hv : Valid σ₀ h0 hn x v) :
    (⟨_, _, (ext σ₀ h0 hn).app p x⟩ : HSimplex C p) = v := by
  have h := congr_arg (fun g ↦ g.app p ⟨x, hx⟩)
    (SSet.anodyneExtensions.exists_extension (anodyne_hollowP n i h0 hn)
      (hollowMap σ₀ h0 hn)).choose_spec
  change (ext σ₀ h0 hn).app p x = (hollowMap σ₀ h0 hn).app p ⟨x, hx⟩ at h
  rw [h, hollowMap, mk_mkHom_app]
  exact valid_unique σ₀ h0 hn x (exists_valid σ₀ h0 hn x hx).choose_spec hv

section W

variable {a b : Th.{v} (n + 2)} {p : SimplexCategoryᵒᵖ}

open Classical in
/-- The values of the filler on chains of paths from `a` to `b`. -/
noncomputable def W (x : (nerve (a ⟶ b)).obj p) : HSimplex C p :=
  if h : a = a0 n ∧ b = am n then
    (by obtain ⟨rfl, rfl⟩ := h; exact ⟨_, _, (ext σ₀ h0 hn).app p x⟩)
  else if b.as.down < Fin.last _ then val (Gl σ₀ hn) x else val (G0 σ₀ h0) x

lemma W_end (x : (nerve (a0.{v} n ⟶ am n)).obj p) :
    W σ₀ h0 hn x = ⟨_, _, (ext σ₀ h0 hn).app p x⟩ := by
  rw [W, dite_eq_left ⟨rfl, rfl⟩]

lemma W_of_ne (h : ¬ (a = a0 n ∧ b = am n)) (x : (nerve (a ⟶ b)).obj p) :
    W σ₀ h0 hn x = if b.as.down < Fin.last _ then val (Gl σ₀ hn) x else val (G0 σ₀ h0) x := by
  rw [W, dite_eq_right h]

lemma eq_pt {a : Th.{v} (n + 2)} {k : Fin (n + 3)} (h : a.as.down = k) : a = pt k := by
  obtain ⟨⟨a⟩⟩ := a
  subst h
  rfl

lemma ne_zero_of_not_end (h : ¬ (a = a0 n ∧ b = am n)) (hb : ¬ b.as.down < Fin.last _) :
    a.as.down ≠ 0 :=
  fun ha ↦ h ⟨eq_pt ha, eq_pt (Fin.eq_last_of_not_lt hb)⟩

lemma W_src (x : (nerve (a ⟶ b)).obj p) : (W σ₀ h0 hn x).src = X σ₀ h0 hn a := by
  by_cases h : a = a0 n ∧ b = am n
  · obtain ⟨rfl, rfl⟩ := h
    rw [W_end]
  rw [W_of_ne σ₀ h0 hn h, X]
  split_ifs with hb ha ha
  · rfl
  · exact absurd (lt_of_le_of_lt (le_of_chain x) hb) ha
  · exact obj_G_eq σ₀ _ _ a (ne_zero_of_not_end h hb) ha.ne
  · rfl

lemma W_tgt (x : (nerve (a ⟶ b)).obj p) : (W σ₀ h0 hn x).tgt = X σ₀ h0 hn b := by
  by_cases h : a = a0 n ∧ b = am n
  · obtain ⟨rfl, rfl⟩ := h
    rw [W_end]
  rw [W_of_ne σ₀ h0 hn h, X]
  split_ifs <;> rfl

lemma W_map (x : (nerve (a ⟶ b)).obj p) {p' : SimplexCategoryᵒᵖ} (f : p ⟶ p') :
    W σ₀ h0 hn ((nerve (a ⟶ b)).map f x) = (W σ₀ h0 hn x).map f := by
  by_cases h : a = a0 n ∧ b = am n
  · obtain ⟨rfl, rfl⟩ := h
    rw [W_end, W_end]
    exact congr_arg (HSimplex.mk _ _) (NatTrans.naturality_apply (ext σ₀ h0 hn) f x)
  rw [W_of_ne σ₀ h0 hn h, W_of_ne σ₀ h0 hn h]
  split_ifs <;> exact val_map _ f x

lemma W_idS (a : Th.{v} (n + 2)) (p : SimplexCategoryᵒᵖ) :
    W σ₀ h0 hn (idS a p) = ⟨X σ₀ h0 hn a, X σ₀ h0 hn a, idS _ p⟩ := by
  have h : ¬ (a = a0 n ∧ a = am n) := fun h ↦
    Fin.last_pos.ne (congr_arg (·.as.down) (h.1.symm.trans h.2))
  rw [W_of_ne σ₀ h0 hn h, X]
  by_cases ha : a.as.down < Fin.last _
  · rw [ite_eq_left ha, ite_eq_left ha]
    exact congr_arg (HSimplex.mk _ _) (map_idS _ a p)
  · rw [ite_eq_right ha, ite_eq_right ha]
    exact congr_arg (HSimplex.mk _ _) (map_idS _ a p)

lemma W_comp {c : Th.{v} (n + 2)} (x : (nerve (a ⟶ b)).obj p) (y : (nerve (b ⟶ c)).obj p) :
    W σ₀ h0 hn (union x y) = HSimplex.hcomp (W σ₀ h0 hn x) (W σ₀ h0 hn y) := by
  have hab := le_of_chain x
  have hbc := le_of_chain y
  by_cases h : a = a0 n ∧ c = am n
  · obtain ⟨rfl, rfl⟩ := h
    by_cases hb₀ : b.as.down = 0
    · obtain rfl := eq_pt hb₀
      rw [chain_eq_id x, id_union, W_idS, HSimplex.idS_hcomp _ (W_src σ₀ h0 hn y)]
    replace hb₀ := Fin.pos_iff_ne_zero.2 hb₀
    rcases eq_or_lt_of_le (Fin.le_last b.as.down) with hbm | hbm
    · obtain rfl := eq_pt hbm
      rw [chain_eq_id y, union_id, W_idS, HSimplex.hcomp_idS _ (W_tgt σ₀ h0 hn x)]
    obtain ⟨⟨k⟩⟩ := b
    have hmem : ∀ t, (⟨k⟩ : ULift (Fin (n + 3))) ∈ ((union x y).obj t).I :=
      fun t ↦ Or.inr (y.obj t).left
    rw [W_end, ext_eq σ₀ h0 hn _ (mem_hollowP_of_contain h0 hn _ hb₀ hbm hmem)
      (Or.inr ⟨k, hb₀, hbm, hmem, rfl⟩), contVal]
    have h₁ : ¬ (a0 n = a0 n ∧ pt k = am n) := fun h ↦ hbm.ne (congr_arg (·.as.down) h.2)
    have h₂ : ¬ (pt k = a0 n ∧ am n = am n) := fun h ↦ hb₀.ne' (congr_arg (·.as.down) h.1)
    rw [W_of_ne σ₀ h0 hn h₁, W_of_ne σ₀ h0 hn h₂, ite_eq_left hbm, ite_eq_right (lt_irrefl _)]
    congr 1
    · exact val_congr _ rfl rfl _ _ fun t ↦ subI_union_left _ _ (x.obj t).left (x.obj t).right
        (Path.bounds _) (fun c hc ↦ (y.obj t).left_le c hc)
    · exact val_congr _ rfl rfl _ _ fun t ↦ subI_union_right _ _ (y.obj t).left (y.obj t).right
        (fun c hc ↦ (x.obj t).le_right c hc) (Path.bounds _)
  have h₁ : ¬ (a = a0 n ∧ b = am n) := fun h' ↦ h ⟨h'.1, eq_pt (le_antisymm (Fin.le_last _)
    (by rw [h'.2] at hbc; exact hbc))⟩
  have h₂ : ¬ (b = a0 n ∧ c = am n) := fun h' ↦ h ⟨eq_pt (by
    rw [h'.1] at hab; exact Fin.le_zero_iff.1 hab), h'.2⟩
  rw [W_of_ne σ₀ h0 hn h, W_of_ne σ₀ h0 hn h₁, W_of_ne σ₀ h0 hn h₂]
  split_ifs with hc hb hb
  · exact val_union _ x y
  · exact absurd (lt_of_le_of_lt hbc hc) hb
  · rw [val_union]
    congr 1
    exact val_G_eq σ₀ _ _ x fun t c' hc' ↦
      ⟨(lt_of_lt_of_le (Fin.pos_iff_ne_zero.2 (ne_zero_of_not_end h hc))
        (Path.bounds _ c' hc').1).ne',
       (lt_of_le_of_lt (Path.bounds _ c' hc').2 hb).ne⟩
  · exact val_union _ x y

end W

/-- The maps on hom-objects of the filler. -/
noncomputable def fillerMap (a b : Th.{v} (n + 2)) :
    nerve (a ⟶ b) ⟶ sHom (X σ₀ h0 hn a) (X σ₀ h0 hn b) :=
  mkHom (fun _ x ↦ W σ₀ h0 hn x) (fun _ x ↦ W_src σ₀ h0 hn x)
    (fun _ x ↦ W_tgt σ₀ h0 hn x) (fun _ _ f x ↦ W_map σ₀ h0 hn x f)

lemma mk_fillerMap_app {a b : Th.{v} (n + 2)} {p : SimplexCategoryᵒᵖ} (x : (nerve (a ⟶ b)).obj p) :
    (⟨_, _, (fillerMap σ₀ h0 hn a b).app p x⟩ : HSimplex C p) = W σ₀ h0 hn x :=
  mk_mkHom_app _ _ _ _ x

/-- The filler of the horn. -/
noncomputable def filler : Simplex C (n + 2) where
  obj := X σ₀ h0 hn
  map := fillerMap σ₀ h0 hn
  map_id a := by
    ext p ⟨⟩
    exact eq_of_heq (HSimplex.mk.inj ((mk_fillerMap_app σ₀ h0 hn (idS a p)).trans
      (W_idS σ₀ h0 hn a p))).2.2
  map_comp a b c := by
    ext p ⟨x, y⟩
    have e : (⟨_, _, (fillerMap σ₀ h0 hn a c).app p (union x y)⟩ : HSimplex C p) =
        ⟨_, _, comp ((fillerMap σ₀ h0 hn a b).app p x) ((fillerMap σ₀ h0 hn b c).app p y)⟩ := by
      rw [mk_fillerMap_app, W_comp, ← HSimplex.hcomp_mk, mk_fillerMap_app, mk_fillerMap_app]
    exact eq_of_heq (HSimplex.mk.inj e).2.2

lemma val_filler_eq_G (j : Fin (n + 3)) (hj : j ≠ i) {a b : Th.{v} (n + 2)}
    {p : SimplexCategoryᵒᵖ} (x : (nerve (a ⟶ b)).obj p)
    (hx : ∀ t, ∀ c ∈ (x.obj t).I, c.down ≠ j) : val (filler σ₀ h0 hn) x = val (G σ₀ j hj) x := by
  refine (mk_fillerMap_app σ₀ h0 hn x).trans ?_
  have hx' : ∀ t, (⟨j⟩ : ULift (Fin (n + 3))) ∉ (x.obj t).I := fun t hc ↦ hx t _ hc rfl
  by_cases h : a = a0 n ∧ b = am n
  · obtain ⟨rfl, rfl⟩ := h
    rw [W_end]
    exact ext_eq σ₀ h0 hn x (mem_hollowP_of_avoid h0 hn x hj hx') (Or.inl ⟨j, hj, hx', rfl⟩)
  rw [W_of_ne σ₀ h0 hn h]
  split_ifs with hb
  · exact val_G_eq σ₀ _ hj x fun t c hc ↦ ⟨(lt_of_le_of_lt
      (Path.bounds _ c hc).2 hb).ne, hx t c hc⟩
  · exact val_G_eq σ₀ _ hj x fun t c hc ↦ ⟨(lt_of_lt_of_le
      (Fin.pos_iff_ne_zero.2 (ne_zero_of_not_end h hb))
      (Path.bounds _ c hc).1).ne', hx t c hc⟩

lemma filler_face (j : Fin (n + 3)) (hj : j ≠ i) :
    (SimplicialNerve C).δ j (filler σ₀ h0 hn) = σ₀.app _ (SSet.horn.face i j hj) := by
  rw [← restr_δ_G σ₀ j hj]
  change restr (SimplexCategory.δ j) (filler σ₀ h0 hn) = restr (SimplexCategory.δ j) (G σ₀ j hj)
  refine eq_of_val fun a b q x ↦ ?_
  rw [val_restr, val_restr]
  refine val_filler_eq_G σ₀ h0 hn j hj _ fun t c hc ↦ ?_
  obtain ⟨c', -, rfl⟩ := hc
  exact Fin.succAbove_ne j c'.down

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
