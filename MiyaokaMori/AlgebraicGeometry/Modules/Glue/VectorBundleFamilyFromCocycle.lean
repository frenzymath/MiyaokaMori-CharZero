import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeHomOfCoeffs
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueConstruction
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle

/-! # The vector bundle family on `C × A¹` glued from a matrix cocycle

The sheaf of modules on `C × A¹` glued from a matrix cocycle: take `O^r` on each `U_α × A¹` and
glue along `G_{αα'}` (matrices with polynomial coefficients in `Γ(U_α ∩ U_α')[λ]`) on the
overlaps.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Components of `bundleFamilyOfCocycle` and its proof obligations

The proof obligations `hom_inv_id` / `inv_hom_id` / `cocycle` are proved along the following
route: (1) algebraic consequences of `IsMatrixCocycle` (diagonal blocks are `1`,
`g α α' · swap (g α' α) = 1`, the multiplicative relation on triple overlaps restricted to any
smaller open); (2) section computations for morphisms of free sheaves: `matrixHom` sends the
standard section `e_i` to `Σ_j g_{ji} e_j`, whence `matrixHom g ≫ matrixHom h = matrixHom (h * g)`
and `matrixHom 1 = 𝟙`; (3) compatibility of restriction: the action of `restrictFreeIso` on
generators (via naturality of `restrictFunctorIsoPullback` and Mathlib's
`pullback_map_ιFree_comp_pullbackObjFreeIso_hom`), the commutation of `restrictFreeIso` with
`matrixHom` (coefficients transported by `appIso`), and the compatibility of `restrictRestrictIso`
with `restrictFreeIso`; (4) using (3), the long chain in `IsModulesGlueCocycle` is reduced to
`restrictFreeIso.hom ≫ matrixHom (…) ≫ restrictFreeIso.inv`, and (1)(2) compare the matrices. -/

/-- The functor `Opens.map` induced by an inclusion of opens `V' ≤ V` is **final**.

`Y.homOfLE h` is an open immersion with open embedding `j` as base map; `opensFunctorAdjunction`
gives `j.opensFunctor ⊣ Opens.map j`, so `Opens.map j` is a right adjoint and hence final by
`CategoryTheory.Functor.final_of_adjunction`. (A more general global instance
`AlgebraicGeometry.Scheme.opensMap_final` exists elsewhere; this file provides the instance with
`haveI`.) -/
theorem bundleFamilyOfCocycle_opensMap_final
    {Y : AlgebraicGeometry.Scheme.{u}} {V V' : Y.Opens} (h : V' ≤ V) :
    (TopologicalSpace.Opens.map (Y.homOfLE h).base).Final :=
  CategoryTheory.Functor.final_of_adjunction
    (AlgebraicGeometry.Scheme.Hom.opensFunctorAdjunction (Y.homOfLE h))

/-- The restriction of a free sheaf to an open subset is the free sheaf on the same index set
(Mathlib's `restrictFunctorIsoPullback` followed by `SheafOfModules.pullbackObjFreeIso`). -/
noncomputable def bundleFamilyOfCocycle.restrictFreeIso {Y : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    {V V' : Y.Opens} (h : V' ≤ V) :
    AlgebraicGeometry.Scheme.Modules.restrict
        (SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) (Y.homOfLE h) ≅
      SheafOfModules.free (R := V'.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
  haveI : (TopologicalSpace.Opens.map (Y.homOfLE h).base).Final :=
    bundleFamilyOfCocycle_opensMap_final h
  haveI : (SheafOfModules.pushforward.{u} (Y.homOfLE h).toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (Y.homOfLE h)).isRightAdjoint
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (Y.homOfLE h)).app _ ≪≫
    SheafOfModules.pullbackObjFreeIso (Y.homOfLE h).toRingCatSheafHom (ULift.{u} (Fin r))

/-- A matrix `g` with coefficients in `Γ(Y, V)` as an endomorphism of the free sheaf `O_V^r`:
`e_i ↦ Σ_j g_{ji} e_j` (the column vector of coordinates is multiplied on the left by `g`). -/
noncomputable def bundleFamilyOfCocycle.matrixHom {Y : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    (V : Y.Opens) (g : Matrix (Fin r) (Fin r) Γ(Y, V)) :
    SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) ⟶
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin r)) :=
  AlgebraicGeometry.Scheme.Modules.freeHomOfCoeffs fun i =>
    Finsupp.equivFunOnFinite.symm fun j => V.topIso.inv.hom (g j.down i.down)

/-- Transport a matrix over `V' ⊓ V` to `V ⊓ V'`. -/
noncomputable def bundleFamilyOfCocycle.swapMatrix {Y : AlgebraicGeometry.Scheme.{u}} {r : ℕ}
    (V V' : Y.Opens) (g : Matrix (Fin r) (Fin r) Γ(Y, V' ⊓ V)) :
    Matrix (Fin r) (Fin r) Γ(Y, V ⊓ V') :=
  g.map (Y.presheaf.map (CategoryTheory.homOfLE (le_of_eq (inf_comm _ _))).op).hom

/-! ## Algebraic consequences of the matrix cocycle condition -/

namespace IsMatrixCocycle

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Restrictions along two mutually inverse inclusions compose to the identity. -/
theorem res_res_eq {V W : X.Opens} (h : V ≤ W) (h' : W ≤ V) (a : Γ(X, W)) :
    (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) = a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  have : (homOfLE h' ≫ homOfLE h : W ⟶ W) = 𝟙 W := Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem res_injective_of_eq {V W : X.Opens} (h : V ≤ W) (h' : W ≤ V) :
    Function.Injective (X.presheaf.map (homOfLE h).op).hom := by
  intro a b hab
  have := congrArg (X.presheaf.map (homOfLE h').op).hom hab
  rwa [res_res_eq h h', res_res_eq h h'] at this

/-- Two successive restrictions combine into one. -/
theorem matrix_map_res_res {r : ℕ} {V W Z : X.Opens} (h₁ : W ≤ V) (h₂ : Z ≤ W)
    (M : Matrix (Fin r) (Fin r) Γ(X, V)) :
    (M.map (X.presheaf.map (homOfLE h₁).op).hom).map (X.presheaf.map (homOfLE h₂).op).hom =
      M.map (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom := by
  rw [Matrix.map_map]
  congr 1
  funext a
  simp only [Function.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem matrix_map_res_self {r : ℕ} {V : X.Opens} (h : V ≤ V)
    (M : Matrix (Fin r) (Fin r) Γ(X, V)) :
    M.map (X.presheaf.map (homOfLE h).op).hom = M := by
  have : (homOfLE h : V ⟶ V) = 𝟙 V := Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id]
  ext i j
  rfl

variable {ι : Type u} {r : ℕ} {U : ι → X.Opens}
  {g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α')}

/-- The cocycle relation restricted to any smaller open `W`. -/
theorem mul_res (hg : IsMatrixCocycle U g) (α α' α'' : ι) {W : X.Opens}
    (h₁ : W ≤ U α ⊓ U α') (h₂ : W ≤ U α' ⊓ U α'') (h₃ : W ≤ U α ⊓ U α'') :
    (g α α').map (X.presheaf.map (homOfLE h₁).op).hom *
      (g α' α'').map (X.presheaf.map (homOfLE h₂).op).hom =
    (g α α'').map (X.presheaf.map (homOfLE h₃).op).hom := by
  have hW : W ≤ U α ⊓ U α' ⊓ U α'' := le_inf h₁ (h₂.trans inf_le_right)
  have e := congrArg (fun M => M.map (X.presheaf.map (homOfLE hW).op).hom) (hg.2 α α' α'')
  rw [Matrix.map_mul, matrix_map_res_res, matrix_map_res_res, matrix_map_res_res] at e
  exact e

/-- The diagonal blocks are the identity matrix. -/
theorem diag_eq_one (hg : IsMatrixCocycle U g) (α : ι) : g α α = 1 := by
  have e := hg.mul_res α α α (W := U α ⊓ U α) le_rfl le_rfl le_rfl
  rw [matrix_map_res_self] at e
  have hu : IsUnit (g α α) := (Matrix.isUnit_iff_isUnit_det _).mpr (hg.1 α α)
  exact hu.mul_left_cancel (by rw [e, mul_one])

/-- `g α α' · (g α' α transported to U α ⊓ U α') = 1`. -/
theorem mul_swap_eq_one (hg : IsMatrixCocycle U g) (α α' : ι) :
    g α α' * (g α' α).map (X.presheaf.map (homOfLE (le_of_eq (inf_comm _ _))).op).hom = 1 := by
  have e := hg.mul_res α α' α (W := U α ⊓ U α') le_rfl (le_of_eq (inf_comm _ _)) (le_inf inf_le_left inf_le_left)
  rw [matrix_map_res_self, hg.diag_eq_one, Matrix.map_one _ (map_zero _) (map_one _)] at e
  exact e

theorem swap_mul_eq_one (hg : IsMatrixCocycle U g) (α α' : ι) :
    (g α' α).map (X.presheaf.map (homOfLE (le_of_eq (inf_comm _ _))).op).hom * g α α' = 1 :=
  _root_.mul_eq_one_comm.mp (hg.mul_swap_eq_one α α')

end IsMatrixCocycle

/-! ## Section computations for morphisms of free sheaves and compatibility with restriction

Convention: `Modules.unitModule X`, `Modules.free I`, `ιFree'`, `matrixHom'`, `restrictFreeIso'`
are reducible abbreviations of the Mathlib objects / the objects of this file with the same name,
typed as objects and morphisms of `X.Modules`, so that keyword matching in `rw` works uniformly
between `X.Modules` and `SheafOfModules X.ringCatSheaf`; the mathematical content is unchanged. -/

namespace bundleFamilyOfCocycle

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

noncomputable abbrev freeSec (I : Type u) (i : I) (U : X.Opens) :
    Γ(Modules.free (X := X) I, U) :=
  (SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op U)

/-- The `i`-th generator `𝒪_X ⟶ O_X^{(I)}`, typed as a morphism in `X.Modules`. -/
noncomputable abbrev ιFree' (I : Type u) (i : I) : Modules.unitModule X ⟶ Modules.free (X := X) I :=
  SheafOfModules.ιFree i

/-- The section `1` of the structure sheaf `𝒪_X` on `U`, typed as a section of a sheaf of modules. -/
noncomputable abbrev unitOne (X : AlgebraicGeometry.Scheme.{u}) (U : X.Opens) : Γ(Modules.unitModule X, U) :=
  (1 : Γ(X, U))

/-- A ring section viewed as a section of the structure sheaf (as a sheaf of modules). -/
noncomputable abbrev toUnit {U : X.Opens} (s : Γ(X, U)) : Γ(Modules.unitModule X, U) := s

/-- `bundleFamilyOfCocycle.matrixHom`, typed as a morphism in `V.Modules`. -/
noncomputable abbrev matrixHom' {Y : AlgebraicGeometry.Scheme.{u}} {r : ℕ} (V : Y.Opens)
    (g : Matrix (Fin r) (Fin r) Γ(Y, V)) :
    Modules.free (X := V.toScheme) (ULift.{u} (Fin r)) ⟶ Modules.free (X := V.toScheme) (ULift.{u} (Fin r)) :=
  bundleFamilyOfCocycle.matrixHom V g

/-- `bundleFamilyOfCocycle.restrictFreeIso`, typed as an isomorphism in `V'.Modules`. -/
noncomputable abbrev restrictFreeIso' {Y : AlgebraicGeometry.Scheme.{u}} {r : ℕ} {V V' : Y.Opens}
    (h : V' ≤ V) :
    Modules.restrict (Modules.free (X := V.toScheme) (ULift.{u} (Fin r))) (Y.homOfLE h) ≅
      Modules.free (X := V'.toScheme) (ULift.{u} (Fin r)) :=
  bundleFamilyOfCocycle.restrictFreeIso h

theorem unitHomEquiv_ιFree {I : Type u} (i : I) :
    SheafOfModules.unitHomEquiv _ (SheafOfModules.ιFree (R := X.ringCatSheaf) i) =
      SheafOfModules.freeSection i := by
  show _ = SheafOfModules.unitHomEquiv _ (SheafOfModules.ιFree i ≫ 𝟙 _)
  rw [Category.comp_id]

theorem ιFree_app_one {I : Type u} (i : I) (U : X.Opens) :
    (ιFree' I i).app U (unitOne X U) = freeSec I i U := by
  show _ = (SheafOfModules.freeSection (R := X.ringCatSheaf) i).val (op U)
  rw [← unitHomEquiv_ιFree]
  rfl

/-- A morphism out of a free sheaf is determined by the images of the standard sections. -/
theorem free_hom_ext {I : Type u} {M : X.Modules} (f g : Modules.free I ⟶ M)
    (h : ∀ i U, f.app U (freeSec I i U) = g.app U (freeSec I i U)) : f = g := by
  apply (SheafOfModules.freeHomEquiv M).injective
  funext i
  ext U
  exact h i U.unop

theorem freeHomOfCoeffs_app_freeSec {I J : Type u} (c : I → J →₀ Γ(X, ⊤)) (i : I) (U : X.Opens) :
    Modules.Hom.app (M := Modules.free I) (N := Modules.free J)
      (Modules.freeHomOfCoeffs c) U (freeSec I i U) =
      Modules.freeHomOfCoeffs.sectionFamily (c i) (op U) :=
  congrArg (fun s => s.val (op U))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i => ⟨Modules.freeHomOfCoeffs.sectionFamily (c i),
        Modules.freeHomOfCoeffs.sectionFamily_compat (c i)⟩) i)

theorem sectionFamily_equivFunOnFinite {J : Type u} [Fintype J] (f : J → Γ(X, ⊤)) (U : X.Opens) :
    Modules.freeHomOfCoeffs.sectionFamily (Finsupp.equivFunOnFinite.symm f) (op U) =
      ∑ j, (X.presheaf.map (homOfLE le_top).op (f j) : Γ(X, U)) • freeSec J j U := by
  unfold Modules.freeHomOfCoeffs.sectionFamily
  rw [Finsupp.sum_fintype]
  · simp only [Finsupp.coe_equivFunOnFinite_symm, unitHomEquiv_ιFree]
    rfl
  · intro j
    simp only [map_zero]
    exact zero_smul _ _

variable {Y : AlgebraicGeometry.Scheme.{u}} {r : ℕ}

theorem matrixHom_app_freeSec (V : Y.Opens) (g : Matrix (Fin r) (Fin r) Γ(Y, V))
    (i : ULift.{u} (Fin r)) (U : V.toScheme.Opens) :
    (matrixHom' V g).app U (freeSec (ULift.{u} (Fin r)) i U) =
      ∑ j : ULift.{u} (Fin r),
        (V.toScheme.presheaf.map (homOfLE le_top).op (V.topIso.inv (g j.down i.down)) : Γ(V, U)) •
          freeSec (ULift.{u} (Fin r)) j U := by
  unfold matrixHom' bundleFamilyOfCocycle.matrixHom
  rw [freeHomOfCoeffs_app_freeSec, sectionFamily_equivFunOnFinite]

theorem matrixHom_one (V : Y.Opens) :
    matrixHom' (r := r) V 1 = 𝟙 _ := by
  apply free_hom_ext
  intro i U
  change (matrixHom' V 1).app U _ = freeSec (ULift.{u} (Fin r)) i U
  rw [matrixHom_app_freeSec]
  simp only [Matrix.one_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : j.down ≠ i.down := fun h => hj (ULift.ext _ _ h)
    simp [this]
  · simp

@[reassoc]
theorem matrixHom_comp (V : Y.Opens) (g h : Matrix (Fin r) (Fin r) Γ(Y, V)) :
    matrixHom' V g ≫ matrixHom' V h = matrixHom' V (h * g) := by
  apply free_hom_ext
  intro i U
  change (matrixHom' V h).app U ((matrixHom' V g).app U _) = _
  rw [matrixHom_app_freeSec, map_sum]
  have step : ∀ j : ULift.{u} (Fin r),
      (matrixHom' V h).app U
        ((V.toScheme.presheaf.map (homOfLE le_top).op (V.topIso.inv (g j.down i.down)) : Γ(V, U)) •
          freeSec (ULift.{u} (Fin r)) j U) =
      ∑ k : ULift.{u} (Fin r),
        ((V.toScheme.presheaf.map (homOfLE le_top).op (V.topIso.inv (h k.down j.down)) : Γ(V, U)) *
          V.toScheme.presheaf.map (homOfLE le_top).op (V.topIso.inv (g j.down i.down))) •
          freeSec (ULift.{u} (Fin r)) k U := by
    intro j
    erw [Modules.Hom.app_smul]
    rw [matrixHom_app_freeSec, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, mul_comm]
  simp only [step]
  rw [matrixHom_app_freeSec, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_smul]
  congr 1
  rw [Matrix.mul_apply, map_sum, map_sum,
    ← Equiv.sum_comp (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, map_mul]
  rfl


theorem app_res {M N : X.Modules} (φ : M ⟶ N) {U U' : X.Opens} (h : U' ≤ U) (x : Γ(M, U)) :
    φ.app U' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app U x) :=
  congr($(φ.val.naturality (homOfLE h).op) x)

theorem unit_map_one {U U' : (X.Opens)ᵒᵖ} (f : U ⟶ U') :
    (Modules.unitModule X).presheaf.map f (unitOne X U.unop) = unitOne X U'.unop :=
  PresheafOfModules.unit_map_one (R := X.ringCatSheaf.val) f

theorem smul_unitOne {U : X.Opens} (s : Γ(X, U)) : s • unitOne X U = toUnit s := mul_one s

/-- (E) If every section on every open is a multiple of a fixed section `e`, a morphism is
determined by the image of `e`. -/
theorem hom_ext_of_gen {N M : X.Modules} (e : ∀ O : X.Opens, Γ(N, O))
    (gen : ∀ O (x : Γ(N, O)), ∃ r : Γ(X, O), x = r • e O)
    (k₁ k₂ : N ⟶ M) (hk : ∀ O, k₁.app O (e O) = k₂.app O (e O)) : k₁ = k₂ := by
  apply Modules.hom_ext
  intro O
  ext x
  obtain ⟨r, rfl⟩ := gen O x
  rw [Modules.Hom.app_smul, Modules.Hom.app_smul, hk]

variable {V V' : Y.Opens} (h : V' ≤ V)

/-- The section `1` of the restricted sheaf `𝒪_V|_{V'}` on `O` (transported to the section type of
the restriction via `restrictAppIso.inv`). -/
noncomputable abbrev unitOne₁ (O : V'.toScheme.Opens) :
    Γ((Modules.unitModule V.toScheme).restrict (Y.homOfLE h), O) :=
  ((Modules.unitModule V.toScheme).restrictAppIso (Y.homOfLE h) O).inv
    (unitOne V.toScheme ((Y.homOfLE h) ''ᵁ O))

theorem gen_restrict_unit (O : V'.toScheme.Opens)
    (x : Γ((Modules.unitModule V.toScheme).restrict (Y.homOfLE h), O)) :
    ∃ r : Γ(V', O), x = r • unitOne₁ h O :=
  ⟨((Y.homOfLE h).appIso O).hom (((Modules.unitModule V.toScheme).restrictAppIso (Y.homOfLE h) O).hom x), by
    have e := Modules.smul_restrictAppIso_inv_apply (Y.homOfLE h) (Modules.unitModule V.toScheme) O
      (((Modules.unitModule V.toScheme).restrictAppIso (Y.homOfLE h) O).hom x) (unitOne V.toScheme _)
    erw [smul_unitOne] at e
    exact e⟩

/-- The morphism `restrict 𝒪_V ⟶ 𝒪_V'` used in (K): `restrictFunctorIsoPullback` followed by
`pullbackObjUnitToUnit`. -/
noncomputable def unitRestrictHom :
    Modules.restrict (Modules.unitModule V.toScheme) (Y.homOfLE h) ⟶ Modules.unitModule V'.toScheme :=
  haveI : (TopologicalSpace.Opens.map (Y.homOfLE h).base).Final :=
    bundleFamilyOfCocycle_opensMap_final h
  haveI : (SheafOfModules.pushforward.{u} (Y.homOfLE h).toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction (Y.homOfLE h)).isRightAdjoint
  (Modules.restrictFunctorIsoPullback (Y.homOfLE h)).hom.app _ ≫
    SheafOfModules.pullbackObjUnitToUnit (Y.homOfLE h).toRingCatSheafHom

/-- (K) -/
theorem restrictFunctor_map_ιFree_comp_restrictFreeIso_hom {r : ℕ} (i : ULift.{u} (Fin r)) :
    (Modules.restrictFunctor (Y.homOfLE h)).map
        (ιFree' (ULift.{u} (Fin r)) i) ≫
        (restrictFreeIso' (r := r) h).hom =
      unitRestrictHom h ≫
        (ιFree' (ULift.{u} (Fin r)) i) := by
  have hF : (TopologicalSpace.Opens.map (Y.homOfLE h).base).Final :=
    bundleFamilyOfCocycle_opensMap_final h
  have hR : (SheafOfModules.pushforward.{u} (Y.homOfLE h).toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction (Y.homOfLE h)).isRightAdjoint
  change (Modules.restrictFunctor (Y.homOfLE h)).map (SheafOfModules.ιFree i) ≫
      ((Modules.restrictFunctorIsoPullback (Y.homOfLE h)).hom.app _ ≫
        (SheafOfModules.pullbackObjFreeIso (Y.homOfLE h).toRingCatSheafHom (ULift.{u} (Fin r))).hom) =
    ((Modules.restrictFunctorIsoPullback (Y.homOfLE h)).hom.app _ ≫
      SheafOfModules.pullbackObjUnitToUnit (Y.homOfLE h).toRingCatSheafHom) ≫ SheafOfModules.ιFree i
  erw [← Category.assoc, NatTrans.naturality, Category.assoc]
  erw [SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom]
  rfl

/-- (K1) -/
theorem unitRestrictHom_app_one' (O : V'.toScheme.Opens) :
    (unitRestrictHom h).app O (unitOne V.toScheme ((Y.homOfLE h) ''ᵁ O)) = unitOne V'.toScheme O := by
  have hF : (TopologicalSpace.Opens.map (Y.homOfLE h).base).Final :=
    bundleFamilyOfCocycle_opensMap_final h
  have hR : (SheafOfModules.pushforward.{u} (Y.homOfLE h).toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction (Y.homOfLE h)).isRightAdjoint
  have h1 := Adjunction.unit_leftAdjointUniq_hom_app
    (F := Modules.restrictFunctor (Y.homOfLE h)) (F' := Modules.pullback (Y.homOfLE h))
    (G := Modules.pushforward (Y.homOfLE h))
    (Modules.restrictAdjunction (Y.homOfLE h))
    (Modules.pullbackPushforwardAdjunction (Y.homOfLE h)) (Modules.unitModule V.toScheme)
  have h2 : (Modules.pullbackPushforwardAdjunction (Y.homOfLE h)).unit.app (Modules.unitModule V.toScheme) ≫
      (Modules.pushforward (Y.homOfLE h)).map
        (SheafOfModules.pullbackObjUnitToUnit (Y.homOfLE h).toRingCatSheafHom) =
      SheafOfModules.unitToPushforwardObjUnit (Y.homOfLE h).toRingCatSheafHom := by
    erw [← Adjunction.homEquiv_unit]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have h3 : (Modules.restrictAdjunction (Y.homOfLE h)).unit.app (Modules.unitModule V.toScheme) ≫
      (Modules.pushforward (Y.homOfLE h)).map (unitRestrictHom h) =
      SheafOfModules.unitToPushforwardObjUnit (Y.homOfLE h).toRingCatSheafHom := by
    unfold unitRestrictHom
    erw [Functor.map_comp, ← Category.assoc]
    erw [h1]
    exact h2
  have h4 : ∀ U : V.toScheme.Opens,
      (unitRestrictHom h).app ((Y.homOfLE h) ⁻¹ᵁ U)
        (unitOne V.toScheme ((Y.homOfLE h) ''ᵁ ((Y.homOfLE h) ⁻¹ᵁ U))) =
        unitOne V'.toScheme ((Y.homOfLE h) ⁻¹ᵁ U) := by
    intro U
    have e := congrArg (fun k => Modules.Hom.app (M := Modules.unitModule V.toScheme)
      (N := (Modules.pushforward (Y.homOfLE h)).obj (Modules.unitModule V'.toScheme)) k U
      (unitOne V.toScheme U)) h3
    change (unitRestrictHom h).app ((Y.homOfLE h) ⁻¹ᵁ U)
      ((Modules.unitModule V.toScheme).presheaf.map (homOfLE ((Y.homOfLE h).image_preimage_le U)).op
        (unitOne V.toScheme U)) =
      Modules.Hom.app (M := Modules.unitModule V.toScheme)
        (N := (Modules.pushforward (Y.homOfLE h)).obj (Modules.unitModule V'.toScheme))
        (SheafOfModules.unitToPushforwardObjUnit (Y.homOfLE h).toRingCatSheafHom) U
        (unitOne V.toScheme U) at e
    have e2 : Modules.Hom.app (M := Modules.unitModule V.toScheme)
        (N := (Modules.pushforward (Y.homOfLE h)).obj (Modules.unitModule V'.toScheme))
        (SheafOfModules.unitToPushforwardObjUnit (Y.homOfLE h).toRingCatSheafHom) U
        (unitOne V.toScheme U) = unitOne V'.toScheme ((Y.homOfLE h) ⁻¹ᵁ U) :=
      map_one ((Y.homOfLE h).toRingCatSheafHom.hom.app (op U)).hom
    rw [e2] at e
    erw [unit_map_one] at e
    exact e
  have hO : O ≤ (Y.homOfLE h) ⁻¹ᵁ ((Y.homOfLE h) ''ᵁ O) :=
    le_of_eq ((Y.homOfLE h).preimage_image_eq O).symm
  have e1 := app_res (unitRestrictHom h) hO
    (unitOne V.toScheme ((Y.homOfLE h) ''ᵁ ((Y.homOfLE h) ⁻¹ᵁ ((Y.homOfLE h) ''ᵁ O))))
  rw [h4] at e1
  erw [unit_map_one, unit_map_one] at e1
  exact e1

theorem unitRestrictHom_app_one (O : V'.toScheme.Opens) :
    (unitRestrictHom h).app O (unitOne₁ h O) = unitOne V'.toScheme O :=
  unitRestrictHom_app_one' h O

/-- A morphism out of a restricted free sheaf is determined by the generators. -/
theorem restrictFree_hom_ext {I : Type u} {M : V'.toScheme.Modules}
    (f g : Modules.restrict (Modules.free (X := V.toScheme) I) (Y.homOfLE h) ⟶ M)
    (hfg : ∀ i, (Modules.restrictFunctor (Y.homOfLE h)).map
        (ιFree' I i) ≫ f =
      (Modules.restrictFunctor (Y.homOfLE h)).map
        (ιFree' I i) ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (Modules.restrictFunctor (Y.homOfLE h))
    (fun _ : I => Modules.unitModule V.toScheme) SheafOfModules.ιFree
    (SheafOfModules.isColimitFreeCofan I)) f g hfg

/-- (C6) -/
theorem restrictFreeIso_hom_app_freeSec {r : ℕ} (i : ULift.{u} (Fin r)) (O : V'.toScheme.Opens) :
    (restrictFreeIso' (r := r) h).hom.app O
      (((Modules.free (ULift.{u} (Fin r))).restrictAppIso (Y.homOfLE h) O).inv
        (freeSec (ULift.{u} (Fin r)) i ((Y.homOfLE h) ''ᵁ O))) =
      freeSec (ULift.{u} (Fin r)) i O := by
  have e := congrArg (fun k => Modules.Hom.app
    (M := Modules.restrict (Modules.unitModule V.toScheme) (Y.homOfLE h)) (N := Modules.free _) k O
    (unitOne V.toScheme ((Y.homOfLE h) ''ᵁ O))) (restrictFunctor_map_ιFree_comp_restrictFreeIso_hom h i)
  change (restrictFreeIso' h).hom.app O
      ((ιFree' (ULift.{u} (Fin r)) i).app ((Y.homOfLE h) ''ᵁ O) (unitOne V.toScheme _)) =
    (ιFree' (ULift.{u} (Fin r)) i).app O ((unitRestrictHom h).app O (unitOne V.toScheme _)) at e
  rw [ιFree_app_one, unitRestrictHom_app_one', ιFree_app_one] at e
  exact e


/-- Two restrictions along `homOfLE` combine into one. -/
theorem res_res_apply {U W Z : Y.Opens} (h₁ : W ≤ U) (h₂ : Z ≤ W) (a : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h₂).op (Y.presheaf.map (homOfLE h₁).op a) =
      Y.presheaf.map (homOfLE (h₂.trans h₁)).op a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem res_eqToHom_apply {U W : Y.Opens} (e : W = U) (a : Γ(Y, U)) :
    Y.presheaf.map (eqToHom e).op a = Y.presheaf.map (homOfLE (le_of_eq e)).op a := by
  congr 2

/-- (RI) Transport of coefficients, at the level of morphisms: `topIso.inv`, then restriction, then
`appIso`, equals restriction to `V'`, then `topIso.inv`, then restriction. -/
theorem appIso_res_topIso_hom (O : V'.toScheme.Opens) :
    V.topIso.inv ≫ V.toScheme.presheaf.map (homOfLE (le_top : (Y.homOfLE h) ''ᵁ O ≤ ⊤)).op ≫
        ((Y.homOfLE h).appIso O).hom =
      Y.presheaf.map (homOfLE h).op ≫ V'.topIso.inv ≫
        V'.toScheme.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op := by
  simp only [Scheme.Hom.appIso_hom', Scheme.homOfLE_appLE, Scheme.Opens.topIso_inv,
    Scheme.Opens.toScheme_presheaf_map, Quiver.Hom.unop_op, Scheme.Hom.opensFunctor_map_homOfLE]
  erw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- (RI) Transporting a coefficient from `Γ(Y, V)` via `topIso.inv`, restriction to `j ''ᵁ O` and
`appIso` to `Γ(V', O)` equals restricting to `V'` first, then `topIso.inv` and restriction to `O`. -/
theorem appIso_res_topIso (O : V'.toScheme.Opens) (a : Γ(Y, V)) :
    ((Y.homOfLE h).appIso O).hom
        (V.toScheme.presheaf.map (homOfLE le_top).op (V.topIso.inv a)) =
      V'.toScheme.presheaf.map (homOfLE le_top).op
        (V'.topIso.inv ((Y.presheaf.map (homOfLE h).op).hom a)) := by
  have e := congr($(appIso_res_topIso_hom h O) a)
  simp only [CommRingCat.comp_apply] at e
  exact e

/-- (R) Matrix morphisms are compatible with restriction. -/
theorem restrictFunctor_map_matrixHom_comp_restrictFreeIso_hom {r : ℕ}
    (g : Matrix (Fin r) (Fin r) Γ(Y, V)) :
    (Modules.restrictFunctor (Y.homOfLE h)).map (matrixHom' V g) ≫
        (restrictFreeIso' (r := r) h).hom =
      (restrictFreeIso' (r := r) h).hom ≫
        matrixHom' V' (g.map (Y.presheaf.map (homOfLE h).op).hom) := by
  apply restrictFree_hom_ext
  intro i
  apply hom_ext_of_gen _ (gen_restrict_unit h)
  intro O
  change (restrictFreeIso' h).hom.app O
      (Modules.Hom.app (M := Modules.free _) (N := Modules.free _)
        (bundleFamilyOfCocycle.matrixHom V g) ((Y.homOfLE h) ''ᵁ O)
        ((ιFree' (ULift.{u} (Fin r)) i).app ((Y.homOfLE h) ''ᵁ O) (unitOne V.toScheme _))) =
    Modules.Hom.app (M := Modules.free _) (N := Modules.free _)
      (bundleFamilyOfCocycle.matrixHom V' (g.map (Y.presheaf.map (homOfLE h).op).hom)) O
      ((restrictFreeIso' h).hom.app O
        ((ιFree' (ULift.{u} (Fin r)) i).app ((Y.homOfLE h) ''ᵁ O) (unitOne V.toScheme _)))
  change (restrictFreeIso' h).hom.app O
      (((Modules.free (ULift.{u} (Fin r))).restrictAppIso (Y.homOfLE h) O).inv
        ((matrixHom' V g).app ((Y.homOfLE h) ''ᵁ O)
          ((ιFree' (ULift.{u} (Fin r)) i).app ((Y.homOfLE h) ''ᵁ O) (unitOne V.toScheme _)))) =
    (matrixHom' V' (g.map (Y.presheaf.map (homOfLE h).op).hom)).app O
      ((restrictFreeIso' h).hom.app O
        (((Modules.free (ULift.{u} (Fin r))).restrictAppIso (Y.homOfLE h) O).inv
          ((ιFree' (ULift.{u} (Fin r)) i).app ((Y.homOfLE h) ''ᵁ O) (unitOne V.toScheme _))))
  rw [ιFree_app_one, matrixHom_app_freeSec, restrictFreeIso_hom_app_freeSec, matrixHom_app_freeSec,
    map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Modules.smul_restrictAppIso_inv_apply]
  erw [Modules.Hom.app_smul]
  rw [restrictFreeIso_hom_app_freeSec, appIso_res_topIso]
  rfl

/-- `restrictRestrictIso` is natural in morphisms of sheaves of modules. -/
@[reassoc]
theorem restrictRestrictIso_hom_naturality {V W Z : Y.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z)
    {F F' : Z.toScheme.Modules} (k : F ⟶ F') :
    (Modules.restrictFunctor (Y.homOfLE hVW)).map ((Modules.restrictFunctor (Y.homOfLE hWZ)).map k) ≫
        (Modules.restrictRestrictIso hVW hWZ F').hom =
      (Modules.restrictRestrictIso hVW hWZ F).hom ≫
        (Modules.restrictFunctor (Y.homOfLE (hVW.trans hWZ))).map k := by
  unfold Modules.restrictRestrictIso
  change (Modules.restrictFunctor (Y.homOfLE hWZ) ⋙ Modules.restrictFunctor (Y.homOfLE hVW)).map k ≫
      ((Modules.restrictFunctorComp (Y.homOfLE hVW) (Y.homOfLE hWZ)).inv.app F' ≫
        (Modules.restrictFunctorCongr (Y.homOfLE_homOfLE hVW hWZ)).hom.app F') =
    ((Modules.restrictFunctorComp (Y.homOfLE hVW) (Y.homOfLE hWZ)).inv.app F ≫
        (Modules.restrictFunctorCongr (Y.homOfLE_homOfLE hVW hWZ)).hom.app F) ≫
      (Modules.restrictFunctor (Y.homOfLE (hVW.trans hWZ))).map k
  rw [← Category.assoc, NatTrans.naturality, Category.assoc, NatTrans.naturality, Category.assoc]

/-- The section `1` of the twice-restricted sheaf `(𝒪_Z|_W)|_V` on `O`. -/
noncomputable abbrev unitOne₂ {V W Z : Y.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z) (O : V.toScheme.Opens) :
    Γ(((Modules.unitModule Z.toScheme).restrict (Y.homOfLE hWZ)).restrict (Y.homOfLE hVW), O) :=
  (((Modules.unitModule Z.toScheme).restrict (Y.homOfLE hWZ)).restrictAppIso (Y.homOfLE hVW) O).inv
    (unitOne₁ hWZ ((Y.homOfLE hVW) ''ᵁ O))

theorem restrictRestrictIso_hom_app_unitOne {V W Z : Y.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z)
    (O : V.toScheme.Opens) :
    (Modules.restrictRestrictIso hVW hWZ (Modules.unitModule Z.toScheme)).hom.app O (unitOne₂ hVW hWZ O) =
      unitOne₁ (hVW.trans hWZ) O := by
  have e1 : ∀ x, (Modules.restrictRestrictIso hVW hWZ (Modules.unitModule Z.toScheme)).hom.app O x =
      ((Modules.restrictFunctorCongr (Y.homOfLE_homOfLE hVW hWZ)).hom.app (Modules.unitModule Z.toScheme)).app O
        (((Modules.restrictFunctorComp (Y.homOfLE hVW) (Y.homOfLE hWZ)).inv.app
          (Modules.unitModule Z.toScheme)).app O x) := fun x => rfl
  rw [e1, Modules.restrictFunctorComp_inv_app_app, Modules.restrictFunctorCongr_hom_app_app]
  erw [unit_map_one, unit_map_one]
  rfl

/-- Twice-restricted structure sheaf: every section is a multiple of `1`. -/
theorem gen_restrict_restrict_unit {V W Z : Y.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z)
    (O : V.toScheme.Opens)
    (x : Γ(((Modules.unitModule Z.toScheme).restrict (Y.homOfLE hWZ)).restrict (Y.homOfLE hVW), O)) :
    ∃ r : Γ(V, O), x = r • unitOne₂ hVW hWZ O := by
  obtain ⟨r₁, hr₁⟩ := gen_restrict_unit hWZ ((Y.homOfLE hVW) ''ᵁ O)
    ((((Modules.unitModule Z.toScheme).restrict (Y.homOfLE hWZ)).restrictAppIso (Y.homOfLE hVW) O).hom x)
  refine ⟨((Y.homOfLE hVW).appIso O).hom r₁, ?_⟩
  have e := Modules.smul_restrictAppIso_inv_apply (Y.homOfLE hVW)
    ((Modules.unitModule Z.toScheme).restrict (Y.homOfLE hWZ)) O r₁ (unitOne₁ hWZ ((Y.homOfLE hVW) ''ᵁ O))
  rw [← hr₁] at e
  exact e

/-- A morphism out of a twice-restricted free sheaf is determined by the generators. -/
theorem restrictRestrictFree_hom_ext {I : Type u} {V W Z : Y.Opens} (hVW : V ≤ W) (hWZ : W ≤ Z)
    {M : V.toScheme.Modules}
    (f g : (Modules.restrictFunctor (Y.homOfLE hVW)).obj
      ((Modules.restrictFunctor (Y.homOfLE hWZ)).obj (Modules.free (X := Z.toScheme) I)) ⟶ M)
    (hfg : ∀ i, (Modules.restrictFunctor (Y.homOfLE hVW)).map
        ((Modules.restrictFunctor (Y.homOfLE hWZ)).map
          (ιFree' I i)) ≫ f =
      (Modules.restrictFunctor (Y.homOfLE hVW)).map
        ((Modules.restrictFunctor (Y.homOfLE hWZ)).map
          (ιFree' I i)) ≫ g) : f = g :=
  Cofan.IsColimit.hom_ext (isColimitCofanMkObjOfIsColimit (Modules.restrictFunctor (Y.homOfLE hVW))
    (fun _ : I => (Modules.unitModule Z.toScheme).restrict (Y.homOfLE hWZ)) _
    (isColimitCofanMkObjOfIsColimit (Modules.restrictFunctor (Y.homOfLE hWZ))
      (fun _ : I => Modules.unitModule Z.toScheme) SheafOfModules.ιFree
      (SheafOfModules.isColimitFreeCofan I))) f g hfg

/-- (Coh) on generators. -/
theorem restrictRestrictIso_hom_comp_restrictFreeIso_hom_gen {r : ℕ} {V W Z : Y.Opens}
    (hVW : V ≤ W) (hWZ : W ≤ Z) (i : ULift.{u} (Fin r)) :
    (Modules.restrictFunctor (Y.homOfLE hVW)).map
        ((Modules.restrictFunctor (Y.homOfLE hWZ)).map
          (ιFree' (ULift.{u} (Fin r)) i)) ≫
      (Modules.restrictRestrictIso hVW hWZ (Modules.free (X := Z.toScheme) (ULift.{u} (Fin r)))).hom ≫
        (restrictFreeIso' (r := r) (hVW.trans hWZ)).hom =
    (Modules.restrictFunctor (Y.homOfLE hVW)).map
        ((Modules.restrictFunctor (Y.homOfLE hWZ)).map
          (ιFree' (ULift.{u} (Fin r)) i)) ≫
      (Modules.restrictFunctor (Y.homOfLE hVW)).map (restrictFreeIso' (r := r) hWZ).hom ≫
        (restrictFreeIso' (r := r) hVW).hom := by
  have s1 : (Modules.restrictFunctor (Y.homOfLE hVW)).map
        ((Modules.restrictFunctor (Y.homOfLE hWZ)).map
          (ιFree' (ULift.{u} (Fin r)) i)) ≫
      (Modules.restrictRestrictIso hVW hWZ (Modules.free (X := Z.toScheme) (ULift.{u} (Fin r)))).hom ≫
        (restrictFreeIso' (r := r) (hVW.trans hWZ)).hom =
      (Modules.restrictRestrictIso hVW hWZ (Modules.unitModule Z.toScheme)).hom ≫
        unitRestrictHom (hVW.trans hWZ) ≫
          (ιFree' (ULift.{u} (Fin r)) i) := by
    rw [restrictRestrictIso_hom_naturality_assoc, restrictFunctor_map_ιFree_comp_restrictFreeIso_hom]
  have s2 : (Modules.restrictFunctor (Y.homOfLE hVW)).map
        ((Modules.restrictFunctor (Y.homOfLE hWZ)).map
          (ιFree' (ULift.{u} (Fin r)) i)) ≫
      (Modules.restrictFunctor (Y.homOfLE hVW)).map (restrictFreeIso' (r := r) hWZ).hom ≫
        (restrictFreeIso' (r := r) hVW).hom =
      (Modules.restrictFunctor (Y.homOfLE hVW)).map (unitRestrictHom hWZ) ≫
        unitRestrictHom hVW ≫
          (ιFree' (ULift.{u} (Fin r)) i) := by
    rw [← Functor.map_comp_assoc, restrictFunctor_map_ιFree_comp_restrictFreeIso_hom,
      Functor.map_comp_assoc, restrictFunctor_map_ιFree_comp_restrictFreeIso_hom]
  have s3 : (Modules.restrictRestrictIso hVW hWZ (Modules.unitModule Z.toScheme)).hom ≫
        unitRestrictHom (hVW.trans hWZ) =
      (Modules.restrictFunctor (Y.homOfLE hVW)).map (unitRestrictHom hWZ) ≫ unitRestrictHom hVW := by
    apply hom_ext_of_gen _ (gen_restrict_restrict_unit hVW hWZ)
    intro O
    change (unitRestrictHom (hVW.trans hWZ)).app O
        ((Modules.restrictRestrictIso hVW hWZ (Modules.unitModule Z.toScheme)).hom.app O (unitOne₂ hVW hWZ O)) =
      (unitRestrictHom hVW).app O
        ((unitRestrictHom hWZ).app ((Y.homOfLE hVW) ''ᵁ O) (unitOne₁ hWZ ((Y.homOfLE hVW) ''ᵁ O)))
    rw [restrictRestrictIso_hom_app_unitOne, unitRestrictHom_app_one, unitRestrictHom_app_one,
      unitRestrictHom_app_one']
  have s3' := reassoc_of% s3
  rw [s1, s2, s3']

/-- (Coh) `restrictRestrictIso` is compatible with `restrictFreeIso`. -/
theorem restrictRestrictIso_hom_comp_restrictFreeIso_hom {r : ℕ} {V W Z : Y.Opens}
    (hVW : V ≤ W) (hWZ : W ≤ Z) :
    (Modules.restrictRestrictIso hVW hWZ (Modules.free (X := Z.toScheme) (ULift.{u} (Fin r)))).hom ≫
        (restrictFreeIso' (r := r) (hVW.trans hWZ)).hom =
      (Modules.restrictFunctor (Y.homOfLE hVW)).map (restrictFreeIso' (r := r) hWZ).hom ≫
        (restrictFreeIso' (r := r) hVW).hom :=
  restrictRestrictFree_hom_ext hVW hWZ _ _
    (restrictRestrictIso_hom_comp_restrictFreeIso_hom_gen hVW hWZ)


/-- (D3) After conjugating by `restrictFreeIso'`, the restricted matrix morphism is the matrix
morphism of the restricted coefficients. -/
@[reassoc]
theorem restrictFreeIso_inv_matrixHom {r : ℕ} (g : Matrix (Fin r) (Fin r) Γ(Y, V)) :
    (restrictFreeIso' (r := r) h).inv ≫
        (Modules.restrictFunctor (Y.homOfLE h)).map (matrixHom' V g) ≫ (restrictFreeIso' (r := r) h).hom =
      matrixHom' V' (g.map (Y.presheaf.map (homOfLE h).op).hom) := by
  rw [Iso.inv_comp_eq, restrictFunctor_map_matrixHom_comp_restrictFreeIso_hom]

/-- (D1) -/
@[reassoc]
theorem restrictRestrictIso_inv_comp_map_restrictFreeIso_hom {r : ℕ} {V W Z : Y.Opens}
    (hVW : V ≤ W) (hWZ : W ≤ Z) :
    (Modules.restrictRestrictIso hVW hWZ (Modules.free (X := Z.toScheme) (ULift.{u} (Fin r)))).inv ≫
        (Modules.restrictFunctor (Y.homOfLE hVW)).map (restrictFreeIso' (r := r) hWZ).hom =
      (restrictFreeIso' (r := r) (hVW.trans hWZ)).hom ≫ (restrictFreeIso' (r := r) hVW).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact (restrictRestrictIso_hom_comp_restrictFreeIso_hom hVW hWZ).symm

/-- (D2) -/
@[reassoc]
theorem map_restrictFreeIso_inv_comp_restrictRestrictIso_hom {r : ℕ} {V W Z : Y.Opens}
    (hVW : V ≤ W) (hWZ : W ≤ Z) :
    (Modules.restrictFunctor (Y.homOfLE hVW)).map (restrictFreeIso' (r := r) hWZ).inv ≫
        (Modules.restrictRestrictIso hVW hWZ (Modules.free (X := Z.toScheme) (ULift.{u} (Fin r)))).hom =
      (restrictFreeIso' (r := r) hVW).hom ≫ (restrictFreeIso' (r := r) (hVW.trans hWZ)).inv := by
  rw [Iso.eq_comp_inv, Category.assoc, restrictRestrictIso_hom_comp_restrictFreeIso_hom,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

end bundleFamilyOfCocycle

section FromCocycle

/-- The `α`-th piece of the gluing data: `O^r` on `U_α × A¹`. -/
noncomputable def bundleFamilyOfCocycle.dataF {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens) (α : ι) :
    (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α).toScheme.Modules :=
  SheafOfModules.free
    (R := (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α).toScheme.ringCatSheaf)
    (ULift.{u} (Fin r))

/-- First of the two inverse laws of `φ_{αα'}`: `matrixHom (swap (G α' α))` and `matrixHom (G α α')`
are mutually inverse.

Proof: `matrixHom_comp` turns the composite into the matrix product `G α α' * swap (G α' α)`,
which is `1` by `IsMatrixCocycle.mul_swap_eq_one` (the cocycle relation at `(α, α', α)` restricted
to `W_α ⊓ W_α'`, together with `diag_eq_one`); conclude with `matrixHom_one`. -/
theorem bundleFamilyOfCocycle.hom_inv_id {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G)
    (α α' : ι) :
    bundleFamilyOfCocycle.matrixHom
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α')
        (bundleFamilyOfCocycle.swapMatrix _ _ (G α' α)) ≫
      bundleFamilyOfCocycle.matrixHom
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α') (G α α') =
    CategoryTheory.CategoryStruct.id _ := by
  change bundleFamilyOfCocycle.matrixHom' _ (bundleFamilyOfCocycle.swapMatrix _ _ (G α' α)) ≫
    bundleFamilyOfCocycle.matrixHom' _ (G α α') = 𝟙 _
  rw [bundleFamilyOfCocycle.matrixHom_comp]
  unfold bundleFamilyOfCocycle.swapMatrix
  rw [hG.mul_swap_eq_one, bundleFamilyOfCocycle.matrixHom_one]

/-- Second of the two inverse laws of `φ_{αα'}`; same route as `bundleFamilyOfCocycle.hom_inv_id`
with the matrix product in the other order (`IsMatrixCocycle.swap_mul_eq_one`). -/
theorem bundleFamilyOfCocycle.inv_hom_id {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G)
    (α α' : ι) :
    bundleFamilyOfCocycle.matrixHom
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α') (G α α') ≫
      bundleFamilyOfCocycle.matrixHom
        (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α')
        (bundleFamilyOfCocycle.swapMatrix _ _ (G α' α)) =
    CategoryTheory.CategoryStruct.id _ := by
  change bundleFamilyOfCocycle.matrixHom' _ (G α α') ≫
    bundleFamilyOfCocycle.matrixHom' _ (bundleFamilyOfCocycle.swapMatrix _ _ (G α' α)) = 𝟙 _
  rw [bundleFamilyOfCocycle.matrixHom_comp]
  unfold bundleFamilyOfCocycle.swapMatrix
  rw [hG.swap_mul_eq_one, bundleFamilyOfCocycle.matrixHom_one]

/-- The transition isomorphism `φ_{αα'} : O^r|_{W_αα'} ≅ O^r|_{W_αα'}` of the gluing data, given by
`G_{α'α}` with inverse given by `G_{αα'}`. -/
noncomputable def bundleFamilyOfCocycle.dataφ {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G)
    (α α' : ι) :
    (bundleFamilyOfCocycle.dataF (r := r) U α).restrict
        ((AlgebraicGeometry.Scheme.affineLineOver C.toScheme).homOfLE
          (inf_le_left :
            AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
              AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α' ≤
            AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α)) ≅
      (bundleFamilyOfCocycle.dataF (r := r) U α').restrict
        ((AlgebraicGeometry.Scheme.affineLineOver C.toScheme).homOfLE
          (inf_le_right :
            AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
              AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α' ≤
            AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α')) :=
  bundleFamilyOfCocycle.restrictFreeIso inf_le_left ≪≫
  { hom := bundleFamilyOfCocycle.matrixHom _ (bundleFamilyOfCocycle.swapMatrix _ _ (G α' α))
    inv := bundleFamilyOfCocycle.matrixHom _ (G α α')
    hom_inv_id := bundleFamilyOfCocycle.hom_inv_id U G hG α α'
    inv_hom_id := bundleFamilyOfCocycle.inv_hom_id U G hG α α' } ≪≫
  (bundleFamilyOfCocycle.restrictFreeIso inf_le_right).symm

/-- `dataF` is the free sheaf (written as `Modules.free`). -/
theorem bundleFamilyOfCocycle.dataF_eq {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens) (α : ι) :
    bundleFamilyOfCocycle.dataF (r := r) U α =
      AlgebraicGeometry.Scheme.Modules.free
        (X := (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α).toScheme)
        (ULift.{u} (Fin r)) := rfl

/-- `dataφ` unfolds to `restrictFreeIso' ≪≫ (matrix isomorphism) ≪≫ (restrictFreeIso').symm`
(a definitional equality). -/
theorem bundleFamilyOfCocycle.dataφ_eq {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G)
    (α α' : ι) :
    bundleFamilyOfCocycle.dataφ U G hG α α' =
      bundleFamilyOfCocycle.restrictFreeIso' inf_le_left ≪≫
      { hom := bundleFamilyOfCocycle.matrixHom' _ (bundleFamilyOfCocycle.swapMatrix _ _ (G α' α))
        inv := bundleFamilyOfCocycle.matrixHom' _ (G α α')
        hom_inv_id := bundleFamilyOfCocycle.hom_inv_id U G hG α α'
        inv_hom_id := bundleFamilyOfCocycle.inv_hom_id U G hG α α' } ≪≫
      (bundleFamilyOfCocycle.restrictFreeIso' inf_le_right).symm := rfl

/-- The cocycle condition of the gluing data: `φ_{αα} = 𝟙`, and `φ_{α'α''} ∘ φ_{αα'} = φ_{αα''}` on
triple overlaps.

Proof: the middle piece of `φ_{αα}` is `matrixHom (swap (G α α))`, which is `matrixHom 1 = 𝟙` by
`IsMatrixCocycle.diag_eq_one`, and the two `restrictFreeIso` at the ends are inverse to each other,
so `φ_{αα} = Iso.refl`. On triple overlaps, `restrictRestrictIso_inv_comp_map_restrictFreeIso_hom`,
`map_restrictFreeIso_inv_comp_restrictRestrictIso_hom` (compatibility of `restrictRestrictIso`
with `restrictFreeIso`) and `restrictFreeIso_inv_matrixHom` (restricted matrix morphism = matrix
morphism of restricted coefficients) reduce both sides to
`restrictFreeIso.hom ≫ matrixHom (…) ≫ restrictFreeIso.inv`; `matrixHom_comp` merges the two
matrix morphisms on the left, and the remaining matrix identity
`swap(G α'' α') · swap(G α' α) = swap(G α'' α)` (coefficients restricted to
`W_α ⊓ W_α' ⊓ W_α''`) is `IsMatrixCocycle.mul_res` at `(α'', α', α)`. -/
theorem bundleFamilyOfCocycle.cocycle {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G) :
    AlgebraicGeometry.Scheme.Modules.IsModulesGlueCocycle
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α)
      (bundleFamilyOfCocycle.dataF (r := r) U)
      (bundleFamilyOfCocycle.dataφ U G hG) := by
  refine ⟨fun α => ?_, fun α α' α'' => ?_⟩
  · apply Iso.ext
    rw [bundleFamilyOfCocycle.dataφ_eq]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom]
    have e : bundleFamilyOfCocycle.swapMatrix _ _ (G α α) = 1 := by
      unfold bundleFamilyOfCocycle.swapMatrix
      rw [hG.diag_eq_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, bundleFamilyOfCocycle.matrixHom_one, Category.id_comp, Iso.hom_inv_id]
    rfl
  · apply Iso.ext
    simp only [bundleFamilyOfCocycle.dataφ_eq, bundleFamilyOfCocycle.dataF_eq, Iso.trans_hom,
      Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    simp only [bundleFamilyOfCocycle.restrictRestrictIso_inv_comp_map_restrictFreeIso_hom_assoc,
      bundleFamilyOfCocycle.map_restrictFreeIso_inv_comp_restrictRestrictIso_hom_assoc,
      bundleFamilyOfCocycle.map_restrictFreeIso_inv_comp_restrictRestrictIso_hom,
      bundleFamilyOfCocycle.restrictFreeIso_inv_matrixHom_assoc, Iso.inv_hom_id_assoc,
      bundleFamilyOfCocycle.matrixHom_comp_assoc]
    have hBA : (bundleFamilyOfCocycle.swapMatrix _ _ (G α'' α')).map
          ((AlgebraicGeometry.Scheme.affineLineOver C.toScheme).presheaf.map
            (homOfLE (inf_le_inf_right _ inf_le_right)).op).hom *
        (bundleFamilyOfCocycle.swapMatrix _ _ (G α' α)).map
          ((AlgebraicGeometry.Scheme.affineLineOver C.toScheme).presheaf.map
            (homOfLE inf_le_left).op).hom =
        (bundleFamilyOfCocycle.swapMatrix _ _ (G α'' α)).map
          ((AlgebraicGeometry.Scheme.affineLineOver C.toScheme).presheaf.map
            (homOfLE (inf_le_inf_right _ inf_le_left)).op).hom := by
      unfold bundleFamilyOfCocycle.swapMatrix
      rw [IsMatrixCocycle.matrix_map_res_res, IsMatrixCocycle.matrix_map_res_res,
        IsMatrixCocycle.matrix_map_res_res]
      exact hG.mul_res α'' α' α _ _ _
    rw [hBA]

/-- The gluing data: `F_α = O_{W_α}^r`, `φ_{αα'} = G_{α'α}` (from the coordinates of `α` to those of
`α'`), with inverse `G_{αα'}`. -/
noncomputable def bundleFamilyOfCocycle.data {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G) :
    AlgebraicGeometry.Scheme.Modules.GlueData
      (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) :=
  { F := bundleFamilyOfCocycle.dataF (r := r) U
    φ := bundleFamilyOfCocycle.dataφ U G hG
    cocycle := bundleFamilyOfCocycle.cocycle U G hG }

end FromCocycle

/-- The sheaf of modules on `C × A¹` glued from a matrix cocycle: `O^r` on each `U_α × A¹`, glued
along `G_{αα'}` on the overlaps, using the kernel construction `GlueData.glued` of Stacks 00AL
(no choice from an existence statement). -/
noncomputable def bundleFamilyOfCocycle {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {ι : Type u} {r : ℕ} (U : ι → C.toScheme.Opens) (hU : ⨆ α, U α = ⊤)
    (G : ∀ α α' : ι, Matrix (Fin r) (Fin r)
      Γ(AlgebraicGeometry.Scheme.affineLineOver C.toScheme,
        AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α ⊓
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α'))
    (hG : IsMatrixCocycle (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ⁻¹ᵁ U α) G) :
    (AlgebraicGeometry.Scheme.affineLineOver C.toScheme).Modules :=
  (bundleFamilyOfCocycle.data U G hG).glued

end
