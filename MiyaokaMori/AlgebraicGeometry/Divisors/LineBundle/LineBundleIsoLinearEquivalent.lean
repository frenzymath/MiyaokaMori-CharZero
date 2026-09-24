import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPrincipal
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleHom
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheaf
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafStalk
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeilUniqueHelpers
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleGenericSection
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso

/-! # Isomorphic line bundles come from linearly equivalent divisors

`O_X(D) ≅ O_X(D')` implies that `D − D'` is a principal Cartier divisor (injectivity of
`CaCl(X) → Pic(X)` on an integral scheme; Hartshorne II.6.13(c)).

Proof (without tensor products or duals):
1. At every point take a common neighbourhood `V` and local equations `t`, `t'` of `D`, `D'`; `t^{-1}`,
   `t'^{-1}` are frames of `O(D)`, `O(D')` on `V` (`DivisorLineBundleFrame`), and the isomorphism `e`
   sends frames to frames, so `e(t^{-1}) = u • t'^{-1}` with `u ∈ O(V)^×`.
2. The constant `f·u_η/f'` (`f`, `f'` the generic values of `t`, `t'`) is independent of the chart
   (`chart_constant`: the transition between two charts on their intersection, compatibility of `e`
   with restriction and scalar multiplication, and injectivity of frames). Call it `a ∈ K(X)^×`.
3. The global equation `t_a` of `div(a)` (with value `a`) restricted to `V` satisfies
   `t/t' = t_a|_V · u^{-1}` (injectivity half of Stacks 01X5: sections with the same value agree); the
   quotient map kills units of `O^*`, so `(D − D')|_V = [t/t'] = [t_a|_V] = div(a)|_V`, and separatedness
   of the quotient sheaf gives `D − D' = div(a)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The constant of an isomorphism `O(D) ≅ O(D')` on a chart: `f·u_η/f'` is independent of the chart
(written without division). -/
theorem CartierDivisor.chart_constant {k : Type u} [Field k] {X : Variety k}
    {D D' : CartierDivisor X}
    (e : CartierDivisor.lineBundleModules D ≅ CartierDivisor.lineBundleModules D')
    {V₁ V₂ : X.toScheme.Opens} [Nonempty V₁] [Nonempty V₂]
    {t₁ t₁' : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op V₁)}
    {t₂ t₂' : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op V₂)}
    (h₁ : CartierDivisor.IsLocalEquation D V₁ t₁) (h₁' : CartierDivisor.IsLocalEquation D' V₁ t₁')
    (h₂ : CartierDivisor.IsLocalEquation D V₂ t₂) (h₂' : CartierDivisor.IsLocalEquation D' V₂ t₂')
    (u₁ : Γ(X.toScheme, V₁)) (u₂ : Γ(X.toScheme, V₂))
    (hu₁ : u₁ • h₁'.frame = e.hom.app V₁ h₁.frame) (hu₂ : u₂ • h₂'.frame = e.hom.app V₂ h₂.frame) :
    ((X.toScheme.rationalUnitsSectionToFunctionField V₁ t₁ : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) * (X.toScheme.germToFunctionField V₁).hom u₁ *
      ((X.toScheme.rationalUnitsSectionToFunctionField V₂ t₂' : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) =
    ((X.toScheme.rationalUnitsSectionToFunctionField V₂ t₂ : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) * (X.toScheme.germToFunctionField V₂).hom u₂ *
      ((X.toScheme.rationalUnitsSectionToFunctionField V₁ t₁' : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) := by
  let M := CartierDivisor.lineBundleModules D
  let M' := CartierDivisor.lineBundleModules D'
  have hη : ∀ (V : X.toScheme.Opens), Nonempty V → genericPoint X.toScheme ∈ V := fun V hV =>
    ((genericPoint_spec X.toScheme).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  let W : X.toScheme.Opens := V₁ ⊓ V₂
  have hηW : genericPoint X.toScheme ∈ W := ⟨hη V₁ inferInstance, hη V₂ inferInstance⟩
  have : Nonempty W := ⟨⟨_, hηW⟩⟩
  have hW₁ : W ≤ V₁ := inf_le_left
  have hW₂ : W ≤ V₂ := inf_le_right
  obtain ⟨c, hc, hcf⟩ := h₁.exists_transition h₂ hW₁ hW₂
  obtain ⟨c', hc', hcf'⟩ := h₁'.exists_transition h₂' hW₁ hW₂
  let F := M'.res hW₂ h₂'.frame
  have hA₁ : e.hom.app W (M.res hW₁ h₁.frame) =
      (X.toScheme.presheaf.map (homOfLE hW₁).op u₁ * c') • F := by
    rw [AlgebraicGeometry.Scheme.Modules.Hom.app_res, ← hu₁,
      AlgebraicGeometry.Scheme.Modules.res_smul, hc', smul_smul]
  have hA₂ : e.hom.app W (M.res hW₁ h₁.frame) =
      (c * X.toScheme.presheaf.map (homOfLE hW₂).op u₂) • F := by
    rw [hc]
    refine (AlgebraicGeometry.Scheme.Modules.Hom.app_smul e.hom c _).trans ?_
    rw [AlgebraicGeometry.Scheme.Modules.Hom.app_res, ← hu₂,
      AlgebraicGeometry.Scheme.Modules.res_smul, smul_smul]
  have hinj := (h₂'.isFrame W hW₂).1 (hA₁.symm.trans hA₂)
  have h3 := congrArg (X.toScheme.germToFunctionField W).hom hinj
  rw [map_mul, map_mul] at h3
  have hr₁ : (X.toScheme.germToFunctionField W).hom (X.toScheme.presheaf.map (homOfLE hW₁).op u₁) =
      (X.toScheme.germToFunctionField V₁).hom u₁ :=
    X.toScheme.presheaf.germ_res_apply (homOfLE hW₁) _ hηW u₁
  have hr₂ : (X.toScheme.germToFunctionField W).hom (X.toScheme.presheaf.map (homOfLE hW₂).op u₂) =
      (X.toScheme.germToFunctionField V₂).hom u₂ :=
    X.toScheme.presheaf.germ_res_apply (homOfLE hW₂) _ hηW u₂
  rw [hr₁, hr₂] at h3
  rw [← hcf, ← hcf']
  linear_combination
    (((X.toScheme.rationalUnitsSectionToFunctionField V₁ t₁ : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) *
      ((X.toScheme.rationalUnitsSectionToFunctionField V₁ t₁' : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField)) * h3


/-- `O_X(D) ≅ O_X(D')` implies `D − D' = div(f)` for some `f ∈ K(X)^×` (Hartshorne II.6.13(c)). -/
theorem CartierDivisor.exists_principal_of_lineBundle_iso {k : Type*} [Field k] {X : Variety k}
    {D D' : CartierDivisor X} (e : D.lineBundle.toModules ≅ D'.lineBundle.toModules) :
    ∃ f : X.toScheme.functionFieldˣ, D - D' = CartierDivisor.principal f := by
  classical
  let I := AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits X.toScheme
  let Q := TopCat.Sheaf.quotient I
  let π := TopCat.Sheaf.quotientπ I
  let e' : CartierDivisor.lineBundleModules D ≅ CartierDivisor.lineBundleModules D' := e
  have hchart : ∀ x : X.toScheme, ∃ (V : X.toScheme.Opens) (_ : x ∈ V)
      (t t' : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op V)),
      CartierDivisor.IsLocalEquation D V t ∧ CartierDivisor.IsLocalEquation D' V t' := by
    intro x
    obtain ⟨U, hxU, t, ht⟩ := CartierDivisor.exists_isLocalEquation D x
    obtain ⟨U', hxU', t', ht'⟩ := CartierDivisor.exists_isLocalEquation D' x
    exact ⟨U ⊓ U', ⟨hxU, hxU'⟩, _, _, ht.restrict inf_le_left, ht'.restrict inf_le_right⟩
  choose V hxV t t' ht ht' using hchart
  have hne : ∀ x, Nonempty (V x) := fun x => ⟨⟨x, hxV x⟩⟩
  have hu : ∀ x, ∃ u : (Γ(X.toScheme, V x))ˣ,
      (u : Γ(X.toScheme, V x)) • (ht' x).frame = e'.hom.app (V x) (ht x).frame :=
    fun x => (ht x).isFrame.exists_unit_of_iso (ht' x).isFrame e'
  choose u hu using hu
  let fu : X.toScheme → (X.toScheme.functionField)ˣ := fun x =>
    @AlgebraicGeometry.Scheme.rationalUnitsSectionToFunctionField X.toScheme _ (V x) (hne x) (t x)
  let fu' : X.toScheme → (X.toScheme.functionField)ˣ := fun x =>
    @AlgebraicGeometry.Scheme.rationalUnitsSectionToFunctionField X.toScheme _ (V x) (hne x) (t' x)
  let gu : X.toScheme → (X.toScheme.functionField)ˣ := fun x =>
    Units.map (@AlgebraicGeometry.Scheme.germToFunctionField X.toScheme _ (V x)
      (hne x)).hom.toMonoidHom (u x)
  have hconst : ∀ x y, (fu x : X.toScheme.functionField) * gu x * fu' y = fu y * gu y * fu' x := by
    intro x y
    have := hne x
    have := hne y
    exact CartierDivisor.chart_constant e' (ht x) (ht' x) (ht y) (ht' y) (u x) (u y) (hu x) (hu y)
  obtain ⟨x₀⟩ : Nonempty X.toScheme := inferInstance
  let a : (X.toScheme.functionField)ˣ := fu x₀ * gu x₀ / fu' x₀
  refine ⟨a, ?_⟩
  let P := AlgebraicGeometry.Intersection.principalCartierData a
  have hlocal : CartierDivisor.IsLocalData P.opens
      (fun i => Units.mk0 (P.equation i) (P.equation_ne_zero i)) := by
    dsimp [CartierDivisor.IsLocalData, P]
    constructor
    · ext y
      simp only [AlgebraicGeometry.Intersection.principalCartierData]
      simp
    · intro i j y hy
      constructor
      · refine ⟨1, ?_⟩
        simp [AlgebraicGeometry.Intersection.principalCartierData]
      · refine ⟨1, ?_⟩
        simp [AlgebraicGeometry.Intersection.principalCartierData]
  obtain ⟨ta, htav, htaq⟩ := CartierToWeilLocalSection.local_section_ofLocalData P.opens
    (fun i => Units.mk0 (P.equation i) (P.equation_ne_zero i)) hlocal x₀ ⟨0⟩ trivial
  have hPa : CartierDivisor.IsLocalEquation (CartierDivisor.principal a) ⊤ ta := htaq
  have hne_top : Nonempty ((⊤ : X.toScheme.Opens)) := ⟨⟨x₀, trivial⟩⟩
  have htav' : X.toScheme.rationalUnitsSectionToFunctionField ⊤ ta = a := by
    refine htav.trans ?_
    exact Units.ext rfl
  have hcover : (⊤ : X.toScheme.Opens) ≤ iSup V :=
    fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩
  have hmain : Additive.toMul (D - D') = Additive.toMul (CartierDivisor.principal a) := by
    apply Q.eq_of_locally_eq' V ⊤ (fun x => homOfLE le_top) hcover
    intro x
    have := hne x
    have hL : Q.val.map (homOfLE (show V x ≤ ⊤ from le_top)).op (Additive.toMul (D - D')) =
        π.hom.app (op (V x)) (t x / t' x) := by
      change Q.val.map (homOfLE (show V x ≤ ⊤ from le_top)).op
        (Additive.toMul D / Additive.toMul D') = _
      rw [map_div, map_div]
      exact congrArg₂ (· / ·) (ht x) (ht' x)
    have hR : Q.val.map (homOfLE (show V x ≤ ⊤ from le_top)).op
        (Additive.toMul (CartierDivisor.principal a)) =
        π.hom.app (op (V x))
          (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE (show V x ≤ ⊤ from le_top)).op ta) :=
      hPa.restrict le_top
    let uI : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (V x)) :=
      I.hom.app (op (V x)) (show X.toScheme.unitsSheaf.val.obj (op (V x)) from u x)
    have hval_uI : X.toScheme.rationalUnitsSectionToFunctionField (V x) uI = gu x :=
      Units.ext (CartierDivisor.rationalSectionToFunctionField_toRat (V x) (u x : Γ(X.toScheme, V x)))
    have hkill : π.hom.app (op (V x)) uI = 1 :=
      TopCat.Sheaf.comp_quotientπ_hom_app_apply I (op (V x)) _
    have hkey : t x / t' x =
        X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE (show V x ≤ ⊤ from le_top)).op ta *
          uI⁻¹ := by
      apply X.toScheme.rationalUnitsSectionToFunctionField_injective (V x)
      rw [map_div, map_mul, map_inv,
        X.toScheme.rationalUnitsSectionToFunctionField_res ⊤ (V x) le_top ta, htav', hval_uI]
      change fu x / fu' x = a * (gu x)⁻¹
      apply Units.ext
      have h := hconst x x₀
      simp only [a, Units.val_div_eq_div_val, Units.val_mul, Units.val_inv_eq_inv_val]
      have h1 : (fu' x : X.toScheme.functionField) ≠ 0 := Units.ne_zero _
      have h2 : (fu' x₀ : X.toScheme.functionField) ≠ 0 := Units.ne_zero _
      have h3 : (gu x : X.toScheme.functionField) ≠ 0 := Units.ne_zero _
      field_simp
      linear_combination h
    rw [hL, hR, hkey, map_mul, map_inv, hkill, inv_one, mul_one]
  exact congrArg Additive.ofMul hmain


end
