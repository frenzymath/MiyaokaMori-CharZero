import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit

/-! # The standard basis of the stalk of a free sheaf of modules

Let `Y` be a scheme, `y ∈ Y`, `A = O_{Y,y}`. Write `e_i` for the `i`-th standard global section of the
free sheaf `O_Y^{(I)}` and `b_i` for its germ at `y` (the stalk `(O_Y^{(I)})_y` carries the
`A`-module structure of Mathlib's `PresheafOfModules` stalks, `AlgebraicGeometry.Scheme.Modules.moduleStalkModule`). Then
(a) for any `I`, `{b_i}` is linearly independent over `A` (`linearIndependent_b`);
(b) for finite `J`, `{b_j}` spans `(O_Y^{⊕J})_y` (`span_b_eq_top`);
(c) an epimorphism of sheaves of modules is surjective on stalks (`stalkMap_surjective_of_epi`);
(d) consequently (`finite_of_epi_of_iso_free`), if there are an epimorphism `π : O_Y^{⊕J} → N`
(`J` finite) and an isomorphism `N ≅ O_Y^{(I)}`, then `I` is finite.

Proof:
1. Let `inc_i : O → O^{(I)}` be the coproduct inclusion (`SheafOfModules.ιFree`) and
   `proj_i : O^{(I)} → O` the coordinate projection given by the universal property
   (`inc_j ≫ proj_i = δ_{ji}`). By definition of `unitHomEquiv`, `e_i|_V = inc_i(1_V)`, hence
   `inc_i(r) = r • e_i|_V` (morphisms commute with scalars).
2. (b): for finite `J`, `id = Σ_j proj_j ≫ inc_j` (check on each `inc_k`, `hom_ext` for coproducts).
   So a section `s` on `V` is `Σ_j proj_j(s) • e_j|_V`; taking germs and using
   `PresheafOfModules.germ_smul`, `germ(s) = Σ_j germ(proj_j s) • b_j ∈ span{b_j}`. Every stalk
   element is the germ of a section, so the `b_j` span.
3. (a): suppose `Σ_{i∈s} g_i • b_i = 0`. Apply the `A`-linear stalk map `(proj_i)_y`
   (`AlgebraicGeometry.Scheme.Modules.moduleStalkMap`); from `proj_i(e_j) = δ_{ji}·1` we get `g_i • germ(1) = 0` in the
   stalk of `O`. Writing `g_i = germ_V(r)`, `germ_V(r) = germ_V(r • 1) = 0` as a germ of the
   underlying abelian presheaf of the unit sheaf, so by `TopCat.Presheaf.germ_eq` there is a smaller
   neighbourhood `W` with `r|_W = 0`, hence `g_i = germ_W(r|_W) = 0`.
4. (c): the forgetful functor `SheafOfModules.toSheaf` preserves finite colimits (it commutes with the
   sheafification adjunction), hence epimorphisms; an epimorphism of abelian sheaves is locally
   surjective (`TopCat.Sheaf.isLocallySurjective_iff_epi`), i.e. surjective on stalks
   (`TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks`).
5. (d): `ψ = π ≫ ε` is an epimorphism, so by (c) `ψ_y` is a surjective `A`-linear map; by (b)
   `(O^{⊕J})_y` is spanned by finitely many `b_j`, so `{ψ_y(b_j)}` is a finite spanning set of
   `(O^{(I)})_y`. By (a) `{b_i}_{i∈I}` is linearly independent. `A` is a local ring, hence nonzero, and
   nonzero commutative rings satisfy the strong rank condition: a linearly independent family inside
   the span of a finite set has finite index set (Mathlib `LinearIndependent.finite_of_le_span_finite`).

Source: Stacks 01B5 (finite type), Stacks 007U (surjectivity on stalks), and linear algebra.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.FreeStalk

open AlgebraicGeometry

variable {Y : Scheme.{u}}

/-- The free sheaf `O_Y^{(I)}`. -/
abbrev freeM (Y : Scheme.{u}) (I : Type u) : Y.Modules :=
  SheafOfModules.free (R := Y.ringCatSheaf) I

/-- The value of the standard section `e_i` on the open `V`. -/
def e (I : Type u) (i : I) (V : Y.Opens) : Γ(freeM Y I, V) :=
  (SheafOfModules.freeSection (R := Y.ringCatSheaf) i).val (op V)

/-- A section of the structure sheaf viewed as a section of `unit` (definitionally equal). -/
def uSec (V : Y.Opens) (r : Γ(Y, V)) : Γ(Scheme.Modules.unitModule Y, V) := r

/-- The inverse direction. -/
def ofUSec (V : Y.Opens) (t : Γ(Scheme.Modules.unitModule Y, V)) : Γ(Y, V) := t

@[simp] lemma uSec_ofUSec (V : Y.Opens) (t : Γ(Scheme.Modules.unitModule Y, V)) : uSec V (ofUSec V t) = t := rfl

lemma uSec_eq_smul (V : Y.Opens) (r : Γ(Y, V)) : uSec V r = r • uSec V 1 :=
  (mul_one r).symm

/-- The `i`-th coordinate inclusion `O → O^{(I)}`. -/
def inc (Y : Scheme.{u}) (I : Type u) (i : I) : Scheme.Modules.unitModule Y ⟶ freeM Y I :=
  SheafOfModules.ιFree (R := Y.ringCatSheaf) i

open Classical in
/-- The `i`-th coordinate projection `O^{(I)} → O`. -/
def proj (Y : Scheme.{u}) (I : Type u) (i : I) : freeM Y I ⟶ Scheme.Modules.unitModule Y :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan (R := Y.ringCatSheaf) I)
    (fun j => if j = i then 𝟙 _ else 0)

open Classical in
lemma inc_proj (I : Type u) (i j : I) :
    inc Y I j ≫ proj Y I i = if j = i then 𝟙 _ else 0 :=
  Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (R := Y.ringCatSheaf) I) _ _

lemma e_eq (I : Type u) (i : I) (V : Y.Opens) :
    e I i V = (inc Y I i).app V (uSec V 1) := by
  simp [e, SheafOfModules.freeSection, SheafOfModules.freeHomEquiv]
  rfl

lemma inc_app (I : Type u) (i : I) (V : Y.Opens) (r : Γ(Y, V)) :
    (inc Y I i).app V (uSec V r) = r • e I i V := by
  rw [e_eq, ← Scheme.Modules.Hom.app_smul, ← uSec_eq_smul]

lemma e_res (I : Type u) (i : I) {V W : Y.Opens} (h : W ⟶ V) :
    (freeM Y I).presheaf.map h.op (e I i V) = e I i W :=
  PresheafOfModules.sections_property
    (SheafOfModules.freeSection (R := Y.ringCatSheaf) i) h.op

open Classical in
lemma id_eq_sum (J : Type u) [Fintype J] :
    𝟙 (freeM Y J) = ∑ j, proj Y J j ≫ inc Y J j := by
  refine Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (R := Y.ringCatSheaf) J) _ _ (fun k => ?_)
  change inc Y J k ≫ 𝟙 _ = inc Y J k ≫ _
  rw [Preadditive.comp_sum, Category.comp_id]
  have h : ∀ j, inc Y J k ≫ proj Y J j ≫ inc Y J j = if k = j then inc Y J j else 0 := by
    intro j
    rw [← Category.assoc, inc_proj]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => h j]
  simp

/-- `φ ↦ φ.app V` is an additive homomorphism. -/
def appAddHom (M N : Y.Modules) (V : Y.Opens) : (M ⟶ N) →+ (Γ(M, V) →+ Γ(N, V)) where
  toFun φ := (φ.app V).hom
  map_zero' := rfl
  map_add' _ _ := rfl

lemma section_decomp (J : Type u) [Fintype J] (V : Y.Opens) (s : Γ(freeM Y J, V)) :
    s = ∑ j, ofUSec V ((proj Y J j).app V s) • e J j V := by
  have h := congrArg (fun φ => appAddHom _ _ V φ s) (id_eq_sum (Y := Y) J)
  simp only [map_sum, AddMonoidHom.finsetSum_apply] at h
  refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [← inc_app, uSec_ofUSec]
  rfl

/-- The germ of `e_i` at `y`. -/
def b (I : Type u) (i : I) (y : Y) : (freeM Y I).presheaf.stalk y :=
  (freeM Y I).presheaf.germ ⊤ y trivial (e I i ⊤)

lemma germ_e (I : Type u) (i : I) (y : Y) (V : Y.Opens) (hy : y ∈ V) :
    (freeM Y I).presheaf.germ V y hy (e I i V) = b I i y := by
  rw [b, ← e_res I i (homOfLE le_top : V ⟶ ⊤), TopCat.Presheaf.germ_res_apply]

lemma germ_smul' (M : Y.Modules) (y : Y) (V : Y.Opens) (hy : y ∈ V) (r : Γ(Y, V)) (m : Γ(M, V)) :
    M.presheaf.germ V y hy (r • m) = Y.presheaf.germ V y hy r • M.presheaf.germ V y hy m :=
  PresheafOfModules.germ_smul (R := Y.presheaf) M.val y V hy r m

/-- For a finite index set, the germs of the `e_j` span the stalk of the free sheaf. -/
theorem span_b_eq_top (J : Type u) [Finite J] (y : Y) :
    Submodule.span (Y.presheaf.stalk y) (Set.range fun j => b (Y := Y) J j y) = ⊤ := by
  have := Fintype.ofFinite J
  rw [eq_top_iff]
  rintro m -
  obtain ⟨V, hy, s, rfl⟩ := (freeM Y J).presheaf.exists_germ_eq m
  rw [section_decomp J V s, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [germ_smul', germ_e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

lemma uSec_res {V W : Y.Opens} (h : W ⟶ V) (r : Γ(Y, V)) :
    (Scheme.Modules.unitModule Y).presheaf.map h.op (uSec V r) = uSec W (Y.presheaf.map h.op r) := rfl

/-- In the stalk of `unit`, `a • germ(1) = 0` implies `a = 0`. -/
lemma smul_germ_one_eq_zero (y : Y) (a : Y.presheaf.stalk y)
    (h : a • (Scheme.Modules.unitModule Y).presheaf.germ ⊤ y trivial (uSec ⊤ 1) = 0) : a = 0 := by
  obtain ⟨V, hy, r, rfl⟩ := Y.presheaf.exists_germ_eq a
  have h1 : (Scheme.Modules.unitModule Y).presheaf.germ ⊤ y trivial (uSec ⊤ 1) =
      (Scheme.Modules.unitModule Y).presheaf.germ V y hy (uSec V 1) := by
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE le_top : V ⟶ ⊤) y hy, uSec_res, map_one]
  rw [h1, ← germ_smul', ← uSec_eq_smul] at h
  have h0 : (Scheme.Modules.unitModule Y).presheaf.germ V y hy (uSec V r) =
      (Scheme.Modules.unitModule Y).presheaf.germ V y hy 0 := by rw [h, map_zero]
  obtain ⟨W, hyW, iU, iV, hW⟩ := (Scheme.Modules.unitModule Y).presheaf.germ_eq y hy hy _ _ h0
  rw [uSec_res, map_zero] at hW
  have hr : Y.presheaf.map iU.op r = 0 := hW
  rw [← TopCat.Presheaf.germ_res_apply _ iU y hyW, hr, map_zero]

open Classical in
lemma proj_app_e (I : Type u) (i j : I) (V : Y.Opens) :
    (proj Y I i).app V (e I j V) = if j = i then uSec V 1 else 0 := by
  have h := congrArg (fun φ => appAddHom _ _ V φ (uSec V 1)) (inc_proj (Y := Y) I i j)
  rw [e_eq]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · split_ifs <;> rfl

open Classical in
lemma stalkMap_proj_b (I : Type u) (i j : I) (y : Y) :
    AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y (proj Y I i) (b I j y) =
      if j = i then (Scheme.Modules.unitModule Y).presheaf.germ ⊤ y trivial (uSec ⊤ 1) else 0 := by
  refine (AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ Y y (proj Y I i) ⊤ trivial (e I j ⊤)).trans ?_
  rw [proj_app_e]
  split_ifs
  · rfl
  · exact map_zero _

/-- The germs of the `e_i` are linearly independent in the stalk of the free sheaf. -/
theorem linearIndependent_b (I : Type u) (y : Y) :
    LinearIndependent (Y.presheaf.stalk y) (fun i => b (Y := Y) I i y) := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h := congrArg (AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y (proj Y I i)) hg
  rw [map_sum, map_zero] at h
  simp only [map_smul, stalkMap_proj_b] at h
  rw [Finset.sum_eq_single i] at h
  · exact smul_germ_one_eq_zero y (g i) (by simpa using h)
  · intro j _ hji
    simp [hji]
  · intro h'; exact absurd hi h'

lemma toSheaf_preservesFiniteColimits (Y : Scheme.{u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} Y.ringCatSheaf) := by
  constructor
  intro J _ _
  apply (Adjunction.preservesColimitsOfShape_iff
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 Y.ringCatSheaf.obj))
    (SheafOfModules.toSheaf.{u} Y.ringCatSheaf) J).mpr
  exact preservesColimitsOfShape_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf.{u} (𝟙 Y.ringCatSheaf.obj)).symm

/-- An epimorphism of sheaves of modules is surjective on every stalk. -/
theorem stalkMap_surjective_of_epi {M N : Y.Modules} (φ : M ⟶ N) [Epi φ] (y : Y) :
    Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y φ) := by
  have := toSheaf_preservesFiniteColimits Y
  have hφ : Epi (C := SheafOfModules.{u} Y.ringCatSheaf) φ := ‹Epi φ›
  have hepi : Epi ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map φ) :=
    (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map_epi φ
  have hloc := (TopCat.Sheaf.isLocallySurjective_iff_epi
    ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map φ)).mpr hepi
  exact (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mp hloc y

/-- If on a scheme `Y` with a point `y` there are an epimorphism `O^{⊕J} → N` (`J` finite) and an
isomorphism `N ≅ O^{(I)}`, then `I` is finite. -/
theorem finite_of_epi_of_iso_free (y : Y) (J : Type u) [Finite J] (N : Y.Modules)
    (π : freeM Y J ⟶ N) [Epi π] (I : Type u) (ε : N ≅ freeM Y I) : Finite I := by
  have hsurj := stalkMap_surjective_of_epi (π ≫ ε.hom) y
  set G := AlgebraicGeometry.Scheme.Modules.moduleStalkMap Y y (π ≫ ε.hom) with hG
  refine LinearIndependent.finite_of_le_span_finite _ (linearIndependent_b I y)
    (Set.range fun j => G (b J j y)) ?_
  have : Submodule.span (Y.presheaf.stalk y) (Set.range fun j => G (b J j y)) = ⊤ := by
    rw [show (Set.range fun j => G (b J j y)) = G '' (Set.range fun j => b J j y) from
      (Set.range_comp G _), ← Submodule.map_span, span_b_eq_top, Submodule.map_top,
      LinearMap.range_eq_top.mpr hsurj]
  rw [this]
  exact le_top

end MiyaokaMori.FreeStalk
