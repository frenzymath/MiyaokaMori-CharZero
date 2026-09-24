import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceRestrictToZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalZero
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.Stacks01cmTensorHom
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap

/-! # Positive-degree monomials vanish on the zero section

**Positive-degree monomials vanish on the zero section**: for a line bundle `L` on a scheme `X`, `p : Tot(L) → X`,
`σ₀ : X → Tot(L)` the zero section and `c ∈ Γ(X, M ⊗ (L^∨)^{⊗q})` with `q ≥ 1`,
`restrictToZeroSection L (totalSpace.monomial L M q c) = 0` (`restrictToZeroSection_monomial_pos`).
(In the paper: `P|_{ξ=0} = ρ^*f`, since `ξ` vanishes on the zero section.) Used for
`restrictToZeroSection_xiMonomial_pos` in `TotSectionsPolynomial`.

## Proof (all at the level of morphisms of sheaves of modules on `X`, then evaluated on global sections)
Notation: `S := Sym(L^∨)`, `σ := relativeSpec.structureHom S.total : ⊕_m S_m ⟶ p_*O_Tot`,
`θ := projectionFormulaHom p M O_Tot : M ⊗ p_*O_Tot ⟶ p_*(p^*M ⊗ O_Tot)`, `u_q := Θ_q ≫ ι_q ≫ σ : T_q ⟶ p_*O_Tot`
(`T_q = (L^∨)^{⊗q}`, `Θ_q = tensorPowerToSymPart`, `ι_q = totalIncl`), `η := unit of p^* ⊣ p_*`,
`R := (unit of σ₀^* ⊣ σ₀_*).app (p^*M) ≫ σ₀_*(E) : p^*M ⟶ σ₀_*M` where `E : σ₀^*p^*M ≅ M` is the isomorphism used in
`restrictToZeroSection` (`pullbackComp`, `pullbackCongr (σ₀ ≫ p = 𝟙)`, `pullbackId`).
1. By definition (all `rfl`), `restrictToZeroSection L (monomial L M q c)` is the global section
   `(monomialHom L M q ≫ θ ≫ p_*((ρ_ p^*M).hom ≫ R)).app ⊤ c`, and `monomialHom L M q = τ.hom ≫ (M ◁ u_q)`.
2. `(M ◁ u_q) ≫ θ ≫ p_*((ρ_ p^*M).hom ≫ R) = 0` as morphisms `M ⊗ T_q ⟶ p_*σ₀_*M`. Two morphisms out of a tensor product
   agree once they agree on all pure tensors `m ⊗ t` over all opens `U` (`Modules.tensorObj_hom_ext`). On `m ⊗ t`:
   * `(M ◁ u_q)(m ⊗ t) = m ⊗ u` with `u := u_q(t) ∈ Γ(Tot, p⁻¹U)` (`tensorHom_tensorSections`);
   * `θ(m ⊗ u) = η(m) ⊗ u` (`projectionFormulaHom_val_app_tensorSections`: unfold `θ = η ≫ p_*(δ ≫ (p^*M ◁ counit))`,
     `δ` on `η(m ⊗ u)` is `η m ⊗ η u` (`pullbackTensorObjHom_app_unit_tensorSections`), and `counit (η u) = u`
     (right triangle identity));
   * `(ρ_ p^*M).hom (η m ⊗ u) = u • η m` (`rightUnitor_app_tensorSections`);
   * `R (u • η m) = u • R(η m)` (`R` is `O_Tot`-linear), and the `O_Tot`-action on `σ₀_*M` is through `σ₀^♯`, so this
     is `σ₀^♯(u) • R(η m)`;
   * `σ₀^♯(u) = 0`: `σ₀` is the `X`-morphism corresponding, under the universal property of the relative Spec
     (`relativeSpecHomEquiv`, Stacks 01LQ), to the augmentation `ε : S.total.carrier ⟶ O_X` (`symAugmentation`,
     `zeroSection`); `relativeSpecHomEquiv.apply_symm_apply` says `toAlgebraMap S.total σ₀ = ε`, and `toAlgebraMap`
     on sections is `σ₀^♯ ∘ structureRingMap = σ₀^♯ ∘ σ` (`pullbackSections`, `structureHom_app_apply`). Hence
     `σ₀^♯(σ(s)) = ε(s)` for every section `s` of `⊕ S_m`; for `s = ι_q(Θ_q t)` with `q ≥ 1`,
     `ι_q ≫ symAugmentation = 0` (`Sigma.ι_desc`, the `_ + 1` branch of the `match`), so `ε(s) = 0`.
   * `0 • R(η m) = 0`.
3. Evaluate the zero morphism on `τ.hom c` at `⊤`.
-/
/- `sectionPullbackAlong` is by definition the adjunction unit, and `ModuleSections.pullback` is its `Γ`-typed
reducible abbreviation; the site below reaches the `Γ`-typed spelling by its `change` (the two spellings are `rfl`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {T X : AlgebraicGeometry.Scheme.{u}}

/-- Sections of a composite (definitional): `(f ≫ g).app U x = g.app U (f.app U x)`. -/
theorem app_comp_apply {A B D : X.Modules} (f : A ⟶ B) (g : B ⟶ D) (U : X.Opens) (x : Γ(A, U)) :
    (f ≫ g).app U x = g.app U (f.app U x) :=
  rfl

/-- The pushforward of a morphism, on sections over `W`, is the morphism on sections over `g⁻¹W` (definitional). -/
theorem pushforward_map_app_apply (g : T ⟶ X) {N N' : T.Modules} (φ : N ⟶ N') (W : X.Opens)
    (x : Γ((pushforward g).obj N, W)) :
    ((pushforward g).map φ).app W x = φ.app (g ⁻¹ᵁ W) (x : Γ(N, g ⁻¹ᵁ W)) :=
  rfl

/-- The `Γ(X, W)`-action on sections of a pushforward `g_*N` over `W` is the `Γ(T, g⁻¹W)`-action through `g^♯`
(definitional: `pushforward` restricts scalars along `g^♯`). -/
theorem pushforward_smul_eq (g : T ⟶ X) (N : T.Modules) (W : X.Opens) (r : Γ(X, W))
    (x : Γ((pushforward g).obj N, W)) :
    r • x = @HSMul.hSMul Γ(T, g ⁻¹ᵁ W) Γ(N, g ⁻¹ᵁ W) Γ(N, g ⁻¹ᵁ W) instHSMul ((g.app W).hom r) x :=
  rfl

/-- The zero morphism of `X.Modules` is zero on sections. -/
theorem zero_hom_app_apply (A B : X.Modules) (W : X.Opens) (x : Γ(A, W)) :
    (0 : A ⟶ B).app W x = 0 :=
  rfl

/-- The zero morphism of `X.Modules` is zero on sections (`val.app` spelling, as in `tensorObj_hom_ext`). -/
theorem zero_val_app_apply (A B : X.Modules) (W : X.Opens) (x : Γ(A, W)) :
    (0 : A ⟶ B).val.app (Opposite.op W) x = 0 :=
  rfl

/-- The counit–unit triangle on sections: `ε(η(s)) = s` for `s ∈ Γ(X, g_*N)(W) = Γ(T, N)(g⁻¹W)`. -/
theorem pushforward_counit_app_unit_app (g : T ⟶ X) (N : T.Modules) (W : X.Opens) (s : Γ((pushforward g).obj N, W)) :
    ((pullbackPushforwardAdjunction g).counit.app N).app (g ⁻¹ᵁ W)
        (((pullbackPushforwardAdjunction g).unit.app ((pushforward g).obj N)).app W s) = s :=
  congrArg (fun φ : (pushforward g).obj N ⟶ (pushforward g).obj N => φ.app W s)
    ((pullbackPushforwardAdjunction g).right_triangle_components N)

/-- Left whiskering on a pure tensor: `(M ◁ φ)(a ⊗ b) = a ⊗ φ b`. -/
theorem whiskerLeft_app_tensorSections_apply (M : X.Modules) {A B : X.Modules} (φ : A ⟶ B) (U : X.Opens)
    (a : Γ(M, U)) (b : Γ(A, U)) :
    (M ◁ φ).app U (tensorSections M A U a b) = tensorSections M B U a (φ.app U b) := by
  rw [← CategoryTheory.MonoidalCategory.id_tensorHom]
  exact tensorHom_tensorSections (𝟙 M) φ U a b

set_option backward.isDefEq.respectTransparency false in
/-- **The projection-formula comparison map on a pure tensor of sections** over any open `U`:
`θ(m ⊗ s) = η(m) ⊗ s` in `Γ(X, g_*(g^*M ⊗ N))(U) = Γ(T, g^*M ⊗ N)(g⁻¹U)`. Unfold `projectionFormulaHom`
(`homEquiv_unit`: `η ≫ g_*(δ ≫ (g^*M ◁ ε))`), evaluate `δ` on `η(m ⊗ s)` with
`pullbackTensorObjHom_app_unit_tensorSections`, the whiskering with `tensorHom_tensorSections`, and cancel
`ε ∘ η` with `pushforward_counit_app_unit_app`. (The `⊤` case is
`SubstitutedPolynomialDegreeBridge_UnitDegree.projectionFormulaHom_app_top_tensorSections`, downstream of this file.) -/
theorem projectionFormulaHom_app_tensorSections (g : T ⟶ X) (M : X.Modules) (N : T.Modules) (U : X.Opens)
    (m : Γ(M, U)) (s : Γ((pushforward g).obj N, U)) :
    (projectionFormulaHom g M N).app U (tensorSections M ((pushforward g).obj N) U m s) =
      tensorSections ((pullback g).obj M) N (g ⁻¹ᵁ U)
        (((pullbackPushforwardAdjunction g).unit.app M).app U m) s := by
  unfold projectionFormulaHom
  rw [CategoryTheory.Adjunction.homEquiv_unit]
  change ((pullback g).obj M ◁ (pullbackPushforwardAdjunction g).counit.app N).app (g ⁻¹ᵁ U)
    ((pullbackTensorObjHom g M ((pushforward g).obj N)).app (g ⁻¹ᵁ U)
      (((pullbackPushforwardAdjunction g).unit.app
          (CategoryTheory.MonoidalCategoryStruct.tensorObj M ((pushforward g).obj N))).app U
        (tensorSections M ((pushforward g).obj N) U m s))) = _
  rw [pullbackTensorObjHom_app_unit_tensorSections]
  erw [whiskerLeft_app_tensorSections_apply]
  exact congrArg (fun z => tensorSections ((pullback g).obj M) N (g ⁻¹ᵁ U)
    (((pullbackPushforwardAdjunction g).unit.app M).app U m) z) (pushforward_counit_app_unit_app g N U s)

set_option backward.isDefEq.respectTransparency false in
/-- **Pure tensors through the projection formula, the right unitor and a morphism `R : g^*M ⟶ N`**:
`(g_*((ρ_ g^*M).hom ≫ R)) (θ (m ⊗ u)) = u • R(η m)` in `Γ(T, N)(g⁻¹U)` (with its `Γ(T, g⁻¹U)`-action),
for `m ∈ Γ(M, U)`, `u ∈ Γ(T, g⁻¹U) = Γ(X, g_*O_T)(U)`. -/
theorem pushforward_rightUnitor_comp_app_projectionFormulaHom_tensorSections (g : T ⟶ X) (M : X.Modules)
    {N : T.Modules} (R : (pullback g).obj M ⟶ N) (U : X.Opens) (m : Γ(M, U))
    (u : Γ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf), U)) :
    (projectionFormulaHom g M (SheafOfModules.unit T.ringCatSheaf) ≫
        (pushforward g).map ((ρ_ ((pullback g).obj M)).hom ≫ R)).app U
        (tensorSections M ((pushforward g).obj (SheafOfModules.unit T.ringCatSheaf)) U m u) =
      @HSMul.hSMul Γ(T, g ⁻¹ᵁ U) Γ(N, g ⁻¹ᵁ U) Γ(N, g ⁻¹ᵁ U) instHSMul u
        (R.app (g ⁻¹ᵁ U) (((pullbackPushforwardAdjunction g).unit.app M).app U m)) := by
  rw [app_comp_apply, pushforward_map_app_apply, projectionFormulaHom_app_tensorSections, app_comp_apply]
  erw [rightUnitor_app_tensorSections]
  exact Hom.app_smul R _ _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **The zero section pulls the structure map back to the augmentation**: for a section `s` of
`⊕_m Sym^m(V^∨)` over `U`, `σ₀^♯(σ(s)) = ε(s)` in `Γ(X, U)` (transported along `(𝟙 X)⁻¹U = σ₀⁻¹(p⁻¹U)`).
Here `σ := relativeSpec.structureHom`, `ε := symAugmentation ≫ (pushforwardId X).inv`, and the identity is
`relativeSpecHomEquiv.apply_symm_apply` (Stacks 01LQ) read on sections: `toAlgebraMap S.total σ₀ = ε`, where
`toAlgebraMap` on `U` is `pullbackSections … U = structureRingMap.app U ≫ σ₀.app (p⁻¹U) ≫ eqToHom`
(`pullbackSections`, `structureHom_app_apply`). -/
theorem zeroSection_app_structureHom_app (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (U : X.Opens)
    (s : Γ((Modules.symGradedAlgebra (Modules.dual V)).total.carrier, U)) :
    X.presheaf.map (CategoryTheory.eqToHom
        (show (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X)).hom ⁻¹ᵁ U =
            zeroSection V ⁻¹ᵁ ((totalSpace V).hom ⁻¹ᵁ U) by
          rw [← zeroSection_comp V]; rfl)).op
      ((zeroSection V).app ((totalSpace V).hom ⁻¹ᵁ U)
        ((relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual V)).total).app U s)) =
      (Modules.symAugmentation (Modules.dual V) ≫
          (Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)).app U s := by
  have key := congrArg Subtype.val
    ((relativeSpecHomEquiv (Modules.symGradedAlgebra (Modules.dual V)).total
      (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X))).apply_symm_apply
      ⟨Modules.symAugmentation (Modules.dual V) ≫
          (Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf),
        Modules.symAugmentation_isAlgebraMap (Modules.dual V)⟩)
  have h := congrArg (fun φ => φ.app U s) key
  refine Eq.trans ?_ h
  erw [relativeSpec.structureHom_app_apply]
  rfl

/-- **Positive-degree parts are killed by the zero section**: for `q ≥ 1` and `y ∈ Γ(S_q, U)`,
`σ₀^♯(σ(ι_q y)) = 0` in `Γ(X, σ₀⁻¹(p⁻¹U))`.
From `zeroSection_app_structureHom_app` and `ι_q ≫ symAugmentation = 0` (`Sigma.ι_desc`, the `_ + 1` branch). -/
theorem zeroSection_app_structureHom_app_totalIncl_pos (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (U : X.Opens) {q : ℕ} (hq : 0 < q) (y : Γ((Modules.symGradedAlgebra (Modules.dual V)).part q, U)) :
    (zeroSection V).app ((totalSpace V).hom ⁻¹ᵁ U)
        ((relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual V)).total).app U
          (((Modules.symGradedAlgebra (Modules.dual V)).totalIncl q).app U y)) = 0 := by
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have h := zeroSection_app_structureHom_app V U
    (((Modules.symGradedAlgebra (Modules.dual V)).totalIncl (q' + 1)).app U y)
  have h0 : (Modules.symGradedAlgebra (Modules.dual V)).totalIncl (q' + 1) ≫
      (Modules.symAugmentation (Modules.dual V) ≫
        (Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)) = 0 := by
    have h00 : (Modules.symGradedAlgebra (Modules.dual V)).totalIncl (q' + 1) ≫
        Modules.symAugmentation (Modules.dual V) = 0 :=
      CategoryTheory.Limits.Sigma.ι_desc _ _
    rw [← CategoryTheory.Category.assoc, h00, CategoryTheory.Limits.zero_comp]
  have h1 : (Modules.symAugmentation (Modules.dual V) ≫
        (Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)).app U
        (((Modules.symGradedAlgebra (Modules.dual V)).totalIncl (q' + 1)).app U y) = 0 :=
    congrArg (fun φ : (Modules.symGradedAlgebra (Modules.dual V)).part (q' + 1) ⟶ _ => φ.app U y) h0
  rw [h1] at h
  have hinj : Function.Injective (X.presheaf.map (CategoryTheory.eqToHom
      (show (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X)).hom ⁻¹ᵁ U =
          zeroSection V ⁻¹ᵁ ((totalSpace V).hom ⁻¹ᵁ U) by
        rw [← zeroSection_comp V]; rfl)).op) :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj (h.trans (map_zero _).symm)

/-- **`p^*s` restricts back to `s` along the zero section** (`σ₀^*(p^*s) ↦ s` through `pullbackComp`, `pullbackCongr`,
`pullbackId`): `ModuleSections.pullback_comp`, `pullbackCongr_apply` and `conjugateEquiv_pullbackId_hom`. Placed here,
upstream of `TotSectionsPolynomial` (whose `restrictToZeroSection_sectionPullbackAlong` cites this), to keep that
module's compile time short. -/
theorem AlgebraicGeometry.Scheme.restrictToZeroSection_sectionPullbackAlong_general {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (M : X.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection V
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace V).hom s) = s := by
  unfold AlgebraicGeometry.Scheme.restrictToZeroSection
  dsimp only [CategoryTheory.Iso.trans_hom]
  -- the `change` below is the bridge to the `Γ`-typed `ModuleSections.pullback` spelling (rfl)
  change
    (((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M).val.app (Opposite.op ⊤)).hom (
      (((AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.zeroSection_comp V)).hom.app M).val.app (Opposite.op ⊤)).hom (
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp
          (AlgebraicGeometry.Scheme.zeroSection V)
          (AlgebraicGeometry.Scheme.totalSpace V).hom).hom.app M).val.app
          (Opposite.op ⊤)).hom (
          AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (AlgebraicGeometry.Scheme.zeroSection V)
            (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (AlgebraicGeometry.Scheme.totalSpace V).hom s)))) = s
  have hcomp' :
      (((AlgebraicGeometry.Scheme.Modules.pullbackComp
          (AlgebraicGeometry.Scheme.zeroSection V)
          (AlgebraicGeometry.Scheme.totalSpace V).hom).hom.app M).val.app
        (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (AlgebraicGeometry.Scheme.zeroSection V)
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (AlgebraicGeometry.Scheme.totalSpace V).hom s)) =
      AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback
        (AlgebraicGeometry.Scheme.zeroSection V ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom) s :=
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp
      (AlgebraicGeometry.Scheme.zeroSection V)
      (AlgebraicGeometry.Scheme.totalSpace V).hom s
  rw [hcomp']
  have hcongr' :
      (((AlgebraicGeometry.Scheme.Modules.pullbackCongr
          (AlgebraicGeometry.Scheme.zeroSection_comp V)).hom.app M).val.app
        (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback
          (AlgebraicGeometry.Scheme.zeroSection V ≫
            (AlgebraicGeometry.Scheme.totalSpace V).hom) s) =
      AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (CategoryTheory.CategoryStruct.id X) s :=
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply
      (AlgebraicGeometry.Scheme.zeroSection_comp V) s
  rw [hcongr']
  change (((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M).app ⊤
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (CategoryTheory.CategoryStruct.id X) s)) = s
  have h := CategoryTheory.unit_conjugateEquiv
    (CategoryTheory.Adjunction.id (C := X.Modules))
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom) M
  rw [AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  have hs := congrArg (fun φ => φ.app ⊤ s) h
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardId_inv_app_app] at hs
  change s = _ at hs
  change s = ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M).app ⊤
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (𝟙 X) s) at hs
  exact hs.symm

/-- `restrictToZeroSection` is additive (term-level: the adjunction unit and the comparison isomorphism are module maps).
Placed here, upstream of `TotSectionsPolynomial`, to keep that module's compile time short. -/
theorem restrictToZeroSection_map_add (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {M : X.Modules}
    (a b : (((Modules.pullback (totalSpace V).hom).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    restrictToZeroSection V (a + b) = restrictToZeroSection V a + restrictToZeroSection V b :=
  (congrArg (fun z => ((((Modules.pullbackComp (zeroSection V) (totalSpace V).hom).app M ≪≫
      (Modules.pullbackCongr (zeroSection_comp V)).app M ≪≫ (Modules.pullbackId X).app M).hom.val.app
        (Opposite.op ⊤)).hom z))
    (map_add (((Modules.pullbackPushforwardAdjunction (zeroSection V)).unit.app
      ((Modules.pullback (totalSpace V).hom).obj M)).val.app (Opposite.op ⊤)).hom a b)).trans
    (map_add _ _ _)

/-- `restrictToZeroSection` of a finite sum. -/
theorem restrictToZeroSection_map_sum (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {M : X.Modules}
    {ι : Type*} (s : Finset ι)
    (a : ι → (((Modules.pullback (totalSpace V).hom).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    restrictToZeroSection V (∑ i ∈ s, a i) = ∑ i ∈ s, restrictToZeroSection V (a i) :=
  map_sum (AddMonoidHom.mk' (restrictToZeroSection V (M := M)) (fun a b => restrictToZeroSection_map_add V a b)) a s

/-- `restrictToZeroSection` is the global-sections map of the morphism
`R := η_{σ₀}.app (p^*M) ≫ σ₀_*(E) : p^*M ⟶ σ₀_*M` on `Tot(V)` (definitional). -/
theorem restrictToZeroSection_eq_app (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (M : X.Modules)
    (P : (((Modules.pullback (totalSpace V).hom).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    restrictToZeroSection V P =
      ((Modules.pullbackPushforwardAdjunction (zeroSection V)).unit.app ((Modules.pullback (totalSpace V).hom).obj M) ≫
        (Modules.pushforward (zeroSection V)).map
          ((Modules.pullbackComp (zeroSection V) (totalSpace V).hom).app M ≪≫
            (Modules.pullbackCongr (zeroSection_comp V)).app M ≪≫ (Modules.pullbackId X).app M).hom).app ⊤ P :=
  rfl

/-- **Positive-degree monomials restrict to zero on the zero section, at the level of morphisms**:
`(M ◁ (Θ_q ≫ ι_q ≫ σ)) ≫ θ ≫ p_*((ρ_ p^*M).hom ≫ R) = 0 : M ⊗ T_q ⟶ p_*σ₀_*N` for `q ≥ 1` and any
`R : p^*M ⟶ σ₀_*N` of the form `η_{σ₀}.app (p^*M) ≫ σ₀_*(E)` (any `E`). Checked on pure tensors
(`tensorObj_hom_ext`): the value is `σ₀^♯(u) • R(η m)` with `u = σ(ι_q(Θ_q t))`, and `σ₀^♯(u) = 0`
(`zeroSection_app_structureHom_app_totalIncl_pos`). -/
theorem totalSpace.whiskerLeft_monomialUnit_comp_restrict_eq_zero (L M : X.Modules) [L.IsLineBundle]
    {N : X.Modules} (E : (Modules.pullback (zeroSection L)).obj ((Modules.pullback (totalSpace L).hom).obj M) ⟶ N)
    {q : ℕ} (hq : 0 < q) :
    (M ◁ (totalSpace.tensorPowerToSymPart L q ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl q ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total)) ≫
      Modules.projectionFormulaHom (totalSpace L).hom M (SheafOfModules.unit (totalSpace L).left.ringCatSheaf) ≫
      (Modules.pushforward (totalSpace L).hom).map ((ρ_ ((Modules.pullback (totalSpace L).hom).obj M)).hom ≫
        ((Modules.pullbackPushforwardAdjunction (zeroSection L)).unit.app ((Modules.pullback (totalSpace L).hom).obj M) ≫
          (Modules.pushforward (zeroSection L)).map E)) = 0 := by
  apply Modules.tensorObj_hom_ext
  intro U m t
  have h1 := Modules.whiskerLeft_app_tensorSections_apply M (totalSpace.tensorPowerToSymPart L q ≫
    (Modules.symGradedAlgebra (Modules.dual L)).totalIncl q ≫
    relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total) U m t
  have h2 := Modules.pushforward_rightUnitor_comp_app_projectionFormulaHom_tensorSections (totalSpace L).hom M
    ((Modules.pullbackPushforwardAdjunction (zeroSection L)).unit.app ((Modules.pullback (totalSpace L).hom).obj M) ≫
      (Modules.pushforward (zeroSection L)).map E) U m
    ((totalSpace.tensorPowerToSymPart L q ≫
      (Modules.symGradedAlgebra (Modules.dual L)).totalIncl q ≫
      relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total).app U t)
  have h3 : ((zeroSection L).app ((totalSpace L).hom ⁻¹ᵁ U)).hom
      ((totalSpace.tensorPowerToSymPart L q ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl q ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total).app U t) = 0 :=
    zeroSection_app_structureHom_app_totalIncl_pos L U hq ((totalSpace.tensorPowerToSymPart L q).app U t)
  have h4 := Modules.pushforward_smul_eq (zeroSection L) N ((totalSpace L).hom ⁻¹ᵁ U)
    ((totalSpace.tensorPowerToSymPart L q ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl q ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total).app U t)
    (((Modules.pullbackPushforwardAdjunction (zeroSection L)).unit.app ((Modules.pullback (totalSpace L).hom).obj M) ≫
        (Modules.pushforward (zeroSection L)).map E).app ((totalSpace L).hom ⁻¹ᵁ U)
      (((Modules.pullbackPushforwardAdjunction (totalSpace L).hom).unit.app M).app U m))
  refine Eq.trans ?_ (Modules.zero_val_app_apply _ _ U _).symm
  refine (congrArg (fun z => (Modules.projectionFormulaHom (totalSpace L).hom M
      (SheafOfModules.unit (totalSpace L).left.ringCatSheaf) ≫
    (Modules.pushforward (totalSpace L).hom).map ((ρ_ ((Modules.pullback (totalSpace L).hom).obj M)).hom ≫
      ((Modules.pullbackPushforwardAdjunction (zeroSection L)).unit.app
          ((Modules.pullback (totalSpace L).hom).obj M) ≫
        (Modules.pushforward (zeroSection L)).map E))).app U z) h1).trans ?_
  refine h2.trans (h4.trans ?_)
  rw [h3]
  exact @zero_smul Γ(X, zeroSection L ⁻¹ᵁ ((totalSpace L).hom ⁻¹ᵁ U))
    Γ(N, zeroSection L ⁻¹ᵁ ((totalSpace L).hom ⁻¹ᵁ U)) _ _ _ _

/-- **Positive-degree monomials vanish on the zero section**: `restrictToZeroSection L (monomial L M q c) = 0` for
`q ≥ 1` (proof in the module docstring). -/
theorem totalSpace.restrictToZeroSection_monomial_pos (L M : X.Modules) [L.IsLineBundle] {q : ℕ} (hq : 0 < q)
    (c : ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M L q).val.obj (Opposite.op ⊤) : Type u)) :
    restrictToZeroSection L (totalSpace.monomial L M q c) = 0 := by
  rw [restrictToZeroSection_eq_app]
  have h := congrArg (fun φ => φ.app ⊤
      ((Modules.tensorIsoTensorObj M (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (Modules.dual L) q)).hom.app ⊤ c))
    (totalSpace.whiskerLeft_monomialUnit_comp_restrict_eq_zero L M
      ((Modules.pullbackComp (zeroSection L) (totalSpace L).hom).app M ≪≫
        (Modules.pullbackCongr (zeroSection_comp L)).app M ≪≫ (Modules.pullbackId X).app M).hom hq)
  exact h

end AlgebraicGeometry.Scheme

end
