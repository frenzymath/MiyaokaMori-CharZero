import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexBaseChange
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.GrothendieckVanishing
import MiyaokaMori.CategoryTheory.ExtPostcompLinear
import MiyaokaMori.Algebra.Stacks01xkHomologyLocalization
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01xkSectionsLocalization

/-! # Stacks 01XK, separated case

**Stacks 01XK, separated case.** `f : X → Spec A` quasi-compact and separated, `M` quasi-coherent
on `X`, `g ∈ A`, `q ≥ 0`. Then `H^q(f⁻¹D(g), M|) ` is the localization of the `A`-module
`H^q(X, M)` at the powers of `g`: there is an `A`-linear map
`H^q(X, M) → H^q(f⁻¹D(g), M|_{f⁻¹D(g)})` which is `IsLocalizedModule (Submonoid.powers g)`.
(`Stacks01xk.lean` states the same with `f` only quasi-separated; this module proves the separated case
by a Čech argument.)

**Proof** (Stacks 01XD + 02KH's Čech argument; Hartshorne III.4.5 + III.9.3 first paragraph):
1. `X` is quasi-compact, so it has a finite affine cover `U₁, …, Uₙ`; `f` separated ⇒ all finite
   intersections `U_σ` are affine (Hartshorne II Ex. 4.3, `isAffineOpen_iInf_of_isSeparated`).
   Leray (`sheafCohomology_equiv_cechAlt_of_isSeparated`): `H^q(X, M) ≅ H^q(Č(U, M))`,
   `Γ(X, O_X)`-linearly, hence `A`-linearly (`nonempty_linearEquiv_homology_of_restrictScalars_iso`).
2. Let `Y := f⁻¹D(g) = X.basicOpen (a g)` (`a : A → Γ(X, O_X)`), `A_g := Localization.Away g`,
   `a' : A_g → Γ(Y, O_Y)` the lift of `Y.ι^♯ ∘ a` (`a g` is a unit on `Y`:
   `RingedSpace.isUnit_res_basicOpen`). The cover `Y.ι⁻¹U_i` of `Y` is affine
   (`Y.ι ''ᵁ Y.ι⁻¹U = U ∩ Y = X.basicOpen (a g |_U)`, `IsAffineOpen.basicOpen`) and `Y.ι ≫ f` is
   separated, so Leray again gives `H^q(Y, Y.ι^*M) ≅ H^q(Č(Y.ι⁻¹U, Y.ι^*M))`, `A_g`-linearly.
3. Čech base change (`cechBaseChange_complex_iso`): `Č(U, M) ⊗_A A_g ≅ Č(Y.ι⁻¹U, Y.ι^*M)` as
   complexes of `A_g`-modules, because for each affine `U_σ` the section map
   `Γ(M, U_σ) → Γ(Y.ι^*M, Y.ι⁻¹U_σ)` is the localization at `g`
   (`isLocalizedModule_pullbackSectionsLinear`: it is the restriction `Γ(M, U_σ) → Γ(M, U_σ ∩ Y)`,
   a localization by `Stacks01xkSectionsLocalization.lean`, followed by the bijection
   `restrictFunctorIsoPullback`), hence its transpose `A_g ⊗_A Γ(M, U_σ) → Γ(Y.ι^*M, Y.ι⁻¹U_σ)` is an
   isomorphism (`isIso_homEquiv_symm_of_isLocalizedModule`).
4. Localization is exact: `H^q(Č(U, M) ⊗_A A_g)` is the localization of `H^q(Č(U, M))`
   (`ExtendScalarsHomologyLocalization.lean`). Compose all `A`-linear isomorphisms; finally
   `M.restrict Y.ι ≅ Y.ι^*M` (`restrictFunctorIsoPullback`) and the transport of cohomology along a module
   isomorphism (`nonempty_sheafCohomology_linearEquiv_of_iso` below; it restates
   `sheafCohomology.mapIsoOver` because importing `SheafCohomologyLinearMap` would create the import
   cycle SheafCohomologyLinearMap → EulerCharacteristic → Stacks02o6 → Stacks01xk). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section OpenImmersion

variable {X Y : AlgebraicGeometry.Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (M : X.Modules)

/-- The section map `Γ(M, j ''ᵁ V') → Γ(j^*M, V')` of the pullback along an open immersion to
`j ⁻¹ᵁ (j ''ᵁ V') = V'` is bijective (it is the component of `restrictFunctorIsoPullback` at `V'`). -/
theorem pullbackSectionsOn_image_bijective (V' : Y.Opens) :
    Function.Bijective
      (pullbackSectionsOn j M (j ''ᵁ V') V' (le_of_eq (j.preimage_image_eq V').symm)) := by
  constructor
  · intro x y hxy
    rw [← restrictFunctorIsoPullback_hom_app_apply j M V' x,
      ← restrictFunctorIsoPullback_hom_app_apply j M V' y] at hxy
    have := congrArg (((restrictFunctorIsoPullback j).app M).inv.app V') hxy
    exact (modIso_inv_app_hom_app ((restrictFunctorIsoPullback j).app M) V' x).symm.trans
      (this.trans (modIso_inv_app_hom_app ((restrictFunctorIsoPullback j).app M) V' y))
  · intro y
    refine ⟨((restrictFunctorIsoPullback j).app M).inv.app V' y, ?_⟩
    exact (restrictFunctorIsoPullback_hom_app_apply j M V'
      (((restrictFunctorIsoPullback j).app M).inv.app V' y)).symm.trans
      (modIso_hom_app_inv_app ((restrictFunctorIsoPullback j).app M) V' y)

variable {A A' : Type u} [CommRing A] [CommRing A'] (a : A →+* Γ(X, ⊤)) (a' : A' →+* Γ(Y, ⊤))
  (φ : A →+* A') (hcomm : j.appTop.hom.comp a = a'.comp φ)

/-- Pullback of sections = restriction to `j ''ᵁ V'` followed by the bijective pullback. -/
theorem pullbackSectionsLinear_eq_comp (V : X.Opens) (V' : Y.Opens) (h : V' ≤ j ⁻¹ᵁ V) :
    (pullbackSectionsLinear j a a' φ hcomm M V V' h).hom =
      (pullbackSectionsLinear j a a' φ hcomm M (j ''ᵁ V') V'
        (le_of_eq (j.preimage_image_eq V').symm)).hom ∘ₗ
      ((ModuleCat.restrictScalars a).map
        (M.sectionsOverTopRestrict ((j.image_mono h).trans (j.image_preimage_le V)))).hom := by
  apply LinearMap.ext
  intro s
  have := pullbackSectionsOn_restrict j M h (le_of_eq (j.preimage_image_eq V').symm)
    ((j.image_mono h).trans (j.image_preimage_le V)) (le_refl V') s
  have e : ((AlgebraicGeometry.Scheme.Modules.pullback j).obj M).presheaf.map
      (homOfLE (le_refl V')).op = 𝟙 _ := by
    rw [show (homOfLE (le_refl V') : V' ⟶ V') = 𝟙 V' from rfl, op_id, CategoryTheory.Functor.map_id]
  rw [e, ConcreteCategory.id_apply] at this
  exact this

/-- For `V` affine and `j ''ᵁ V' = V ∩ D(a g)`, the pullback of sections `Γ(M, V) → Γ(j^*M, V')` is the
localization of the `A`-module at the powers of `g`. -/
theorem isLocalizedModule_pullbackSectionsLinear [M.IsQuasicoherent] (g : A) {V : X.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (V' : Y.Opens) (h : V' ≤ j ⁻¹ᵁ V)
    (hW : j ''ᵁ V' = X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a g))) :
    IsLocalizedModule (Submonoid.powers g) (pullbackSectionsLinear j a a' φ hcomm M V V' h).hom := by
  rw [pullbackSectionsLinear_eq_comp]
  haveI := isLocalizedModule_sectionsOverTopRestrict_basicOpen M a g hV hW
    ((j.image_mono h).trans (j.image_preimage_le V))
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers g) _
    (LinearEquiv.ofBijective (pullbackSectionsLinear j a a' φ hcomm M (j ''ᵁ V') V'
      (le_of_eq (j.preimage_image_eq V').symm)).hom (pullbackSectionsOn_image_bijective j M V'))

/-- Accordingly, its adjoint transpose `A' ⊗_A Γ(M, V) → Γ(j^*M, V')` is an isomorphism (`A' = A_g`). -/
theorem isIso_transpose_pullbackSectionsLinear_of_basicOpen [M.IsQuasicoherent] (g : A)
    (hloc : letI := φ.toAlgebra; IsLocalization (Submonoid.powers g) A') {V : X.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) (V' : Y.Opens) (h : V' ≤ j ⁻¹ᵁ V)
    (hW : j ''ᵁ V' = X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a g))) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv _ _).symm
      (pullbackSectionsLinear j a a' φ hcomm M V V' h)) :=
  ModuleCat.isIso_homEquiv_symm_of_isLocalizedModule φ (Submonoid.powers g) hloc _
    (isLocalizedModule_pullbackSectionsLinear j M a a' φ hcomm g hV V' h hW)

end OpenImmersion

/-- A ring section restricted to `W = D(z)` is a unit. -/
theorem isUnit_res_of_eq_basicOpen {X : AlgebraicGeometry.Scheme.{u}} (z : Γ(X, ⊤)) {W : X.Opens}
    (hW : W = X.basicOpen z) :
    IsUnit (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op z) := by
  subst hW
  exact X.toRingedSpace.isUnit_res_basicOpen z

/-- A morphism of modules commutes with `μ_r` (`O_X`-linearity). The same as
`SheafCohomologyLinearMap.smulEnd_naturality`, restated here to avoid the import cycle
SheafCohomologyLinearMap → EulerCharacteristic → Stacks02o6 → Stacks01xk. -/
theorem smulEnd_comm_toSheaf_map {Z : AlgebraicGeometry.Scheme.{u}} {M N : Z.Modules} (f : M ⟶ N)
    (r : Γ(Z, ⊤)) :
    M.smulEnd r ≫ (SheafOfModules.toSheaf Z.ringCatSheaf).map f =
      (SheafOfModules.toSheaf Z.ringCatSheaf).map f ≫ N.smulEnd r := by
  apply Sheaf.hom_ext
  ext U x
  exact ((f.val.app U).hom.map_smul _ x)

/-- Isomorphic modules have `K`-linearly isomorphic cohomology (on a `K`-scheme). Existence form (the same
fact as `sheafCohomology.mapIsoOver`, stated but not redefined; see the note on `smulEnd_comm_toSheaf_map`). -/
theorem nonempty_sheafCohomology_linearEquiv_of_iso (K : Type u) [CommRing K]
    {Z : AlgebraicGeometry.Scheme.{u}} [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    {M N : Z.Modules} (e : M ≅ N) (n : ℕ) :
    Nonempty (AlgebraicGeometry.sheafCohomology Z M n ≃ₗ[K] AlgebraicGeometry.sheafCohomology Z N n) := by
  let φ₁ : AlgebraicGeometry.sheafCohomology Z M n →ₗ[Γ(Z, ⊤)] AlgebraicGeometry.sheafCohomology Z N n :=
    Abelian.Ext.postcompLinear M.smulEnd N.smulEnd (fun _ _ => rfl) (fun _ _ => rfl)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map e.hom) (smulEnd_comm_toSheaf_map e.hom)
  let φ₂ : AlgebraicGeometry.sheafCohomology Z N n →ₗ[Γ(Z, ⊤)] AlgebraicGeometry.sheafCohomology Z M n :=
    Abelian.Ext.postcompLinear N.smulEnd M.smulEnd (fun _ _ => rfl) (fun _ _ => rfl)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map e.inv) (smulEnd_comm_toSheaf_map e.inv)
  have hc₁ : (SheafOfModules.toSheaf Z.ringCatSheaf).map e.inv ≫
      (SheafOfModules.toSheaf Z.ringCatSheaf).map e.hom = 𝟙 _ :=
    ((SheafOfModules.toSheaf Z.ringCatSheaf).map_comp e.inv e.hom).symm.trans
      ((congrArg (SheafOfModules.toSheaf Z.ringCatSheaf).map e.inv_hom_id).trans
        ((SheafOfModules.toSheaf Z.ringCatSheaf).map_id N))
  have hc₂ : (SheafOfModules.toSheaf Z.ringCatSheaf).map e.hom ≫
      (SheafOfModules.toSheaf Z.ringCatSheaf).map e.inv = 𝟙 _ :=
    ((SheafOfModules.toSheaf Z.ringCatSheaf).map_comp e.hom e.inv).symm.trans
      ((congrArg (SheafOfModules.toSheaf Z.ringCatSheaf).map e.hom_inv_id).trans
        ((SheafOfModules.toSheaf Z.ringCatSheaf).map_id M))
  have h₁ : ∀ x, φ₁ (φ₂ x) = x := fun x => by
    have h := Sheaf.H.map_comp_apply ((SheafOfModules.toSheaf Z.ringCatSheaf).map e.inv)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map e.hom) x
    rw [hc₁] at h
    exact h.symm.trans (Sheaf.H.map_id_apply x)
  have h₂ : ∀ x, φ₂ (φ₁ x) = x := fun x => by
    have h := Sheaf.H.map_comp_apply ((SheafOfModules.toSheaf Z.ringCatSheaf).map e.hom)
      ((SheafOfModules.toSheaf Z.ringCatSheaf).map e.inv) x
    rw [hc₂] at h
    exact h.symm.trans (Sheaf.H.map_id_apply x)
  let e' : AlgebraicGeometry.sheafCohomology Z M n ≃ₗ[Γ(Z, ⊤)] AlgebraicGeometry.sheafCohomology Z N n :=
    LinearEquiv.ofLinearMap φ₁ φ₂ (LinearMap.ext h₁) (LinearMap.ext h₂)
  exact ⟨{ e'.toAddEquiv with map_smul' := fun r x => e'.map_smul _ x }⟩

end AlgebraicGeometry.Scheme.Modules

/-- **Stacks 01XK, separated case** (`f` quasi-compact and separated): `H^q(f⁻¹D(g), M)` is the
localization of `H^q(X, M)` at the powers of `g`. Proof: the alternating Čech complex (Stacks 01XD), base
change of the Čech complex along `A → A_g`, and exactness of localization. -/
theorem AlgebraicGeometry.sheafCohomology_preimage_basicOpen_isLocalizedModule_of_isSeparated
    {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A))
    [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (g : A) (q : ℕ) :
    letI : X.Over (AlgebraicGeometry.Spec (CommRingCat.of A)) := ⟨f⟩
    let U : X.Opens := f ⁻¹ᵁ (AlgebraicGeometry.Spec (CommRingCat.of A)).basicOpen
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom g)
    letI : (U : AlgebraicGeometry.Scheme.{u}).Over (AlgebraicGeometry.Spec (CommRingCat.of A)) := ⟨U.ι ≫ f⟩
    ∃ φ : AlgebraicGeometry.sheafCohomology X M q →ₗ[A]
        AlgebraicGeometry.sheafCohomology U (M.restrict U.ι) q,
      IsLocalizedModule (Submonoid.powers g) φ := by
  intro Y
  letI : X.Over (AlgebraicGeometry.Spec (CommRingCat.of A)) := ⟨f⟩
  letI : (Y : AlgebraicGeometry.Scheme.{u}).Over (AlgebraicGeometry.Spec (CommRingCat.of A)) :=
    ⟨Y.ι ≫ f⟩
  set a : A →+* Γ(X, ⊤) := ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
    with ha
  have hY : Y = X.basicOpen (a g) := AlgebraicGeometry.Scheme.preimage_basicOpen_top f _
  -- the localization A_g
  let Rₛ : Type u := Localization.Away g
  let φ : A →+* Rₛ := algebraMap A Rₛ
  have hcan : IsLocalization (Submonoid.powers g) Rₛ := inferInstance
  have hloc : letI := φ.toAlgebra; IsLocalization (Submonoid.powers g) Rₛ := by
    letI := φ.toAlgebra
    exact ⟨hcan.1⟩
  -- a g is a unit on Y
  have hu : IsUnit ((Y.ι.appTop.hom.comp a) g) := by
    show IsUnit (X.presheaf.map (homOfLE (le_top : Y.ι ''ᵁ ⊤ ≤ ⊤)).op (a g))
    exact AlgebraicGeometry.Scheme.Modules.isUnit_res_of_eq_basicOpen (a g)
      (Y.ι_image_top.trans hY)
  let a' : Rₛ →+* Γ(Y, ⊤) := IsLocalization.Away.lift g hu
  have hcomm : Y.ι.appTop.hom.comp a = a'.comp φ := (IsLocalization.Away.lift_comp g hu).symm
  -- finite affine cover of X
  haveI : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨n, U, hU, hcov⟩ := AlgebraicGeometry.exists_finite_affineOpen_cover X
  have haff : ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin n), AlgebraicGeometry.IsAffineOpen (⨅ k, U (σ k)) :=
    fun p σ => AlgebraicGeometry.Scheme.Modules.isAffineOpen_iInf_of_isSeparated f
      (fun k => U (σ k)) (fun k => hU (σ k))
  -- image of the preimage under Y.ι
  have himg : ∀ V : X.Opens, Y.ι ''ᵁ (Y.ι ⁻¹ᵁ V) =
      X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (a g)) := by
    intro V
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι, hY, inf_comm, ← AlgebraicGeometry.Scheme.basicOpen_res]
  have hU' : ∀ i, AlgebraicGeometry.IsAffineOpen (Y.ι ⁻¹ᵁ U i) := fun i => by
    rw [← Y.ι.isAffineOpen_iff_of_isOpenImmersion, himg]
    exact (hU i).basicOpen _
  have hcov' : ⨆ i, Y.ι ⁻¹ᵁ U i = ⊤ := by
    rw [← AlgebraicGeometry.Scheme.Hom.preimage_iSup, hcov, AlgebraicGeometry.Scheme.Hom.preimage_top]
  -- Leray on X, as an A-linear equivalence with the homology of the A-module complex K
  obtain ⟨r₁⟩ := AlgebraicGeometry.sheafCohomology_equiv_cechAlt_of_isSeparated f U hU hcov M q
  let K := ((ModuleCat.restrictScalars a).mapHomologicalComplex _).obj
    (AlgebraicGeometry.Scheme.Modules.cechComplexAlt U M)
  obtain ⟨e₁⟩ := ModuleCat.nonempty_linearEquiv_homology_of_restrictScalars_iso a
    (AlgebraicGeometry.Scheme.Modules.cechComplexAlt U M) K (Iso.refl _) ((q : ℕ) : ℤ)
    (fun _ _ => rfl) r₁
  -- localization of the homology of K
  obtain ⟨ψ, hψ⟩ := ModuleCat.exists_isLocalizedModule_homology_extendScalars φ
    (Submonoid.powers g) hloc K ((q : ℕ) : ℤ)
  -- Čech base change: K ⊗_A A_g ≅ Č(Y.ι⁻¹U, Y.ι^*M)
  let M' := (AlgebraicGeometry.Scheme.Modules.pullback Y.ι).obj M
  obtain ⟨χ⟩ := AlgebraicGeometry.Scheme.Modules.cechBaseChange_complex_iso Y.ι a a' φ U hcomm M
    (fun p σ => AlgebraicGeometry.Scheme.Modules.isIso_transpose_pullbackSectionsLinear_of_basicOpen
      Y.ι M a a' φ hcomm g hloc (haff p σ) _ _
      (by rw [← AlgebraicGeometry.Scheme.Modules.preimage_iInf_eq]; exact himg _))
  let L := ((ModuleCat.restrictScalars a').mapHomologicalComplex _).obj
    (AlgebraicGeometry.Scheme.Modules.cechComplexAlt (fun i => Y.ι ⁻¹ᵁ U i) M')
  let e₂ : (ModuleCat.restrictScalars φ).obj
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj K).homology ((q : ℕ) : ℤ)) ≃ₗ[A]
      (ModuleCat.restrictScalars φ).obj (L.homology ((q : ℕ) : ℤ)) :=
    ((ModuleCat.restrictScalars φ).mapIso
      ((HomologicalComplex.homologyFunctor _ _ ((q : ℕ) : ℤ)).mapIso χ)).toLinearEquiv
  -- Leray on Y
  obtain ⟨r₂⟩ := AlgebraicGeometry.sheafCohomology_equiv_cechAlt_of_isSeparated (Y.ι ≫ f)
    (fun i => Y.ι ⁻¹ᵁ U i) hU' hcov' M' q
  letI : Module Rₛ (AlgebraicGeometry.sheafCohomology Y M' q) := Module.compHom _ a'
  obtain ⟨e₃⟩ := ModuleCat.nonempty_linearEquiv_homology_of_restrictScalars_iso a'
    (AlgebraicGeometry.Scheme.Modules.cechComplexAlt (fun i => Y.ι ⁻¹ᵁ U i) M') L (Iso.refl _)
    ((q : ℕ) : ℤ) (fun _ _ => rfl) r₂
  let e₃' : AlgebraicGeometry.sheafCohomology Y M' q ≃ₗ[A]
      (ModuleCat.restrictScalars φ).obj (L.homology ((q : ℕ) : ℤ)) :=
    { e₃.toAddEquiv with
      map_smul' := fun r x => by
        show e₃ (r • x) = φ r • e₃ x
        rw [← e₃.map_smul]
        congr 1
        show (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
          (Y.ι ≫ f).appTop).hom r) • x = a' (φ r) • x
        have h1 : a' (φ r) = Y.ι.appTop.hom (a r) := (RingHom.congr_fun hcomm r).symm
        rw [h1]
        rfl }
  -- M.restrict Y.ι ≅ Y.ι^* M
  obtain ⟨e₀⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_sheafCohomology_linearEquiv_of_iso A
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback Y.ι).app M) q
  let E := e₂ ≪≫ₗ e₃'.symm ≪≫ₗ e₀.symm
  refine ⟨E.toLinearMap ∘ₗ (ψ ∘ₗ e₁.toLinearMap), ?_⟩
  haveI := hψ
  haveI : IsLocalizedModule (Submonoid.powers g) (ψ ∘ₗ e₁.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right _ _ _
  exact IsLocalizedModule.of_linearEquiv _ _ E

end
