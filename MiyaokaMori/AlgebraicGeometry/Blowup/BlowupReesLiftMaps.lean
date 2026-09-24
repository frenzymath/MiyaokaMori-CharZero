import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertyMonoidalPow
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffCartier
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffCartierLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafComapIdealEqMap
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.MonoidalPowToUnit

/-! # The graded maps of the Rees lift data

The graded maps `Ψ_n : f^*(Iⁿ) ⟶ J^{⊗n}` (`J := I.comap f` invertible) that make up the
`relativeProj.LiftData` of the Rees algebra `⊕ Iⁿ` — the sheaf-theoretic half of the existence part of
Stacks 0806 (the monoidal bookkeeping `map_one` / `map_mul` is in the sibling modules
`Stacks0806_ReesLiftMapsMapOne` / `Stacks0806_ReesLiftMapsMapMul`; the assembly is `BlowupExistsLift`).

Route: `Abelian.monoLift` through the monomorphism `μ_n`, with the cokernel condition checked via the
adjunction `f^* ⊣ f_*` on good affine opens; `Ψ_1` is an epimorphism by local surjectivity on sections;
the general lemmas on `μ_n = powToUnit (idealIncl J) n` are in `MonoidalPowToUnit`.

Also the two pieces of data used to state it:
* `θ_n = I.reesPullbackToUnit f n : f^*(Iⁿ) ⟶ O_Y`, the pullback of the inclusion `Iⁿ ⊆ O_X` followed by
  `f^*O_X ≅ O_Y`;
* `μ_n = J.monoidalPowToUnit n : J^{⊗n} ⟶ O_Y`, the `n`-fold tensor power of the inclusion `J ⊆ O_Y`
  followed by the multiplication `O_Y^{⊗n} ⟶ O_Y`.

Source: Stacks 0806 (existence; proof via Stacks 01O4 / 01N8, morphisms into a relative Proj), Stacks 01HQ
(inverse image ideal sheaf `f⁻¹I·O_Y`), Stacks 01WQ (an invertible ideal sheaf is a line bundle).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- `θ_n : f^*(Iⁿ) ⟶ O_Y`: the pullback of the inclusion `powι n : Iⁿ ⟶ O_X` (the `n`-th piece of the Rees
algebra `I.reesAlgebra`), followed by `f^*O_X ≅ O_Y` (`pullbackUnitIso`). -/
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.reesPullbackToUnit
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) {Y : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj (I.reesAlgebra.part n) ⟶
      SheafOfModules.unit Y.ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.pullback f).map (I.powι n) ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom

/-- `μ_n : J^{⊗n} ⟶ O_Y`: the `n`-fold tensor power (`monoidalPowMap`) of the inclusion
`idealIncl J : J.toModules ⟶ O_Y`, followed by the `n`-fold multiplication `O_Y^{⊗n} ⟶ O_Y`
(`unitPowCollapse`, then the identification `𝟙_ Y.Modules ≅ O_Y`, `monoidalUnitIso`). On an affine open where
`J = (g)`, it sends `x^{⊗n}` (with `x ↦ g`) to `gⁿ`. -/
noncomputable def AlgebraicGeometry.Scheme.IdealSheafData.monoidalPowToUnit
    {Y : AlgebraicGeometry.Scheme.{u}} (J : Y.IdealSheafData) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.monoidalPow J.toModules n ⟶ SheafOfModules.unit Y.ringCatSheaf :=
  AlgebraicGeometry.Scheme.Modules.monoidalPowMap (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) n ≫
    AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n ≫
    (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- In degree `0`, `μ_0` is just the identification `𝟙_ Y.Modules ≅ O_Y` (both `monoidalPowMap _ 0` and
`unitPowCollapse Y 0` are identities by definition). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.monoidalPowToUnit_zero
    {Y : AlgebraicGeometry.Scheme.{u}} (J : Y.IdealSheafData) :
    J.monoidalPowToUnit 0 = (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).hom := by
  show 𝟙 _ ≫ 𝟙 _ ≫ _ = _
  simp

/-! ## Auxiliary lemmas for the proof

Notation: `J := I.comap f`, `μ_n := J.monoidalPowToUnit n = powToUnit (idealIncl J) n` (`rfl`),
`θ_n := I.reesPullbackToUnit f n`, `adj := pullbackPushforwardAdjunction f`. -/

namespace AlgebraicGeometry.Scheme.ReesLiftMapsAux

set_option backward.isDefEq.respectTransparency false

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)

/-- `μ_n` is the general `powToUnit` of the inclusion `J ⊆ O_Y` (`MonoidalPowToUnit`). -/
theorem monoidalPowToUnit_eq_powToUnit (J : Y.IdealSheafData) (n : ℕ) :
    J.monoidalPowToUnit n =
      AlgebraicGeometry.Scheme.Modules.powToUnit (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) n := rfl

/-- `μ_n` is a monomorphism for an invertible ideal sheaf `J`: `J.toModules` is a line bundle
(`EffCartier.ideal_isLineBundle`, Stacks 01WQ) and `idealIncl J = kernel.ι _` is a monomorphism, so
`powToUnit_mono` applies. -/
private theorem monoidalPowToUnit_mono_of_isInvertibleIdeal (J : Y.IdealSheafData)
    (hJ : MiyaokaMori.Statement.IsInvertibleIdeal J) (n : ℕ) : Mono (J.monoidalPowToUnit n) := by
  haveI : J.toModules.IsLineBundle :=
    AlgebraicGeometry.Scheme.EffCartier.ideal_isLineBundle (⟨J, hJ⟩ : Y.EffCartier)
  exact AlgebraicGeometry.Scheme.Modules.powToUnit_mono (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) n

/-- A monomorphism of sheaves of modules is injective on sections (`SheafOfModules.evaluation` preserves
monomorphisms; `ModuleCat.mono_iff_injective`). -/
theorem injective_app_of_mono {M N : Y.Modules} (φ : M ⟶ N) [Mono φ] (W : Y.Opens) :
    Function.Injective (φ.app W) := by
  have : Mono ((SheafOfModules.evaluation Y.ringCatSheaf (op W)).map φ) :=
    (SheafOfModules.evaluation Y.ringCatSheaf (op W)).map_mono φ
  exact (ModuleCat.mono_iff_injective _).mp this

/-- Naturality of `Hom.app` with respect to restriction. -/
theorem app_res {M N : Y.Modules} (φ : M ⟶ N) {V W : Y.Opens} (h : V ≤ W) (x : Γ(M, W)) :
    φ.app V (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op x

/-- A section of a sheaf of modules that vanishes on a neighbourhood of every point is zero. -/
theorem section_eq_zero_of_locally (N : Y.Modules) (W : Y.Opens) (s : Γ(N, W))
    (h : ∀ y ∈ W, ∃ (V : Y.Opens) (hV : V ≤ W), y ∈ V ∧ N.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 := by
  choose V hV hyV hs using h
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ (fun p : {y : Y // y ∈ W} => V p.1 p.2) W
    (fun p => homOfLE (hV p.1 p.2)) ?_ s 0 ?_
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV y hy⟩
  · intro p
    rw [hs p.1 p.2]
    exact (map_zero _).symm

/-- **Good affine opens.** Let `J := I.comap f` be invertible, `W ∋ y` open in `Y`, and `U ∋ f(y)` an affine
open of `X`. There is an affine open `V ∋ y` with `V ≤ W`, `V ≤ f⁻¹U` and `J(V) = (g)` principal: shrink the
affine open given by `hf` to a basic open inside `W ⊓ f⁻¹U` (`IsAffineOpen.exists_basicOpen_le`,
`IdealSheafData.map_ideal_basicOpen`). -/
theorem exists_good_affine {I : X.IdealSheafData} (hf : MiyaokaMori.Statement.IsInvertibleIdeal (I.comap f))
    (W : Y.Opens) (y : Y) (hy : y ∈ W) (U : X.affineOpens) (hyU : f.base y ∈ U.1) :
    ∃ (V : Y.affineOpens) (_ : y ∈ V.1) (_ : V.1 ≤ W) (_ : V.1 ≤ f ⁻¹ᵁ U.1) (g : Γ(Y, V)),
      (I.comap f).ideal V = Ideal.span {g} := by
  obtain ⟨V₀, hyV₀, a, -, hJ⟩ := hf y
  have hyO : y ∈ W ⊓ f ⁻¹ᵁ U.1 := ⟨hy, hyU⟩
  obtain ⟨h, hle, hyh⟩ := V₀.2.exists_basicOpen_le ⟨y, hyO⟩ hyV₀
  refine ⟨Y.affineBasicOpen h, hyh, hle.trans inf_le_left, hle.trans inf_le_right,
    Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op a, ?_⟩
  rw [← (I.comap f).map_ideal_basicOpen V₀ h, hJ, Ideal.map_span, Set.image_singleton]
  rfl

/-- **The pullback of a section of `Iⁿ` under `θ_n` is `f^♯` of it**: for `a ∈ Γ(U, Iⁿ)`,
`θ_n (η(a)) = f^♯(a) ∈ Γ(f⁻¹U, O_Y)`, where `η` is the unit of `f^* ⊣ f_*`. Unit naturality for
`powι n`, then `pullbackUnitIso` is the transpose of `f^♯`
(`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`). -/
theorem reesPullbackToUnit_app_unit (I : X.IdealSheafData) (n : ℕ) (U : X.Opens) (a : Γ(I.pow n, U)) :
    (I.reesPullbackToUnit f n).app (f ⁻¹ᵁ U)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (I.pow n)).app U a) =
      (f.app U).hom a.1 := by
  have h1 := congrArg (fun k => k.app U a)
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality (I.powι n))
  have h2 : ((AlgebraicGeometry.Scheme.Modules.pullback f).map (I.powι n)).app (f ⁻¹ᵁ U)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (I.pow n)).app U a) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).app U ((I.powι n).app U a) := h1.symm
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have h3 := congrArg (fun φ : @Quiver.Hom X.Modules _ (SheafOfModules.unit X.ringCatSheaf)
      ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) =>
        φ.app U ((I.powι n).app U a))
    (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom)
  rw [Adjunction.homEquiv_unit] at h3
  show (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((AlgebraicGeometry.Scheme.Modules.pullback f).map (I.powι n)).app (f ⁻¹ᵁ U)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (I.pow n)).app U a)) = _
  rw [h2]
  exact h3

/-- Restricted form of `reesPullbackToUnit_app_unit`: for `a ∈ Γ(U, Iⁿ)` and `V ≤ f⁻¹U`,
`θ_n (η(a)|_V) = f.appLE U V (a)`. -/
theorem reesPullbackToUnit_app_res_unit (I : X.IdealSheafData) (n : ℕ) (U : X.Opens) (a : Γ(I.pow n, U))
    (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    (I.reesPullbackToUnit f n).app V
        (((AlgebraicGeometry.Scheme.Modules.pullback f).obj (I.pow n)).presheaf.map (homOfLE h).op
          (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (I.pow n)).app U a)) =
      (f.appLE U V h).hom a.1 :=
  (app_res (I.reesPullbackToUnit f n) h _).trans
    (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.presheaf
      (SheafOfModules.unit Y.ringCatSheaf)).map (homOfLE h).op z) (reesPullbackToUnit_app_unit f I n U a))

/-- Transpose of `θ_n ≫ ψ` under `f^* ⊣ f_*`: `powι n ≫ (O_X → f_*O_Y) ≫ f_*ψ`. -/
theorem homEquiv_reesPullbackToUnit_comp (I : X.IdealSheafData) (n : ℕ) {N : Y.Modules}
    (ψ : @Quiver.Hom Y.Modules _ (SheafOfModules.unit Y.ringCatSheaf) N) :
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (I.reesPullbackToUnit f n ≫ ψ) =
      I.powι n ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward f).map ψ := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  unfold AlgebraicGeometry.Scheme.IdealSheafData.reesPullbackToUnit
  rw [Category.assoc, Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  congr 2
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom

/-- Sections of the transposed morphism: `(powι n ≫ u ≫ f_*ψ)(s) = ψ(f^♯ s)`. -/
theorem transpose_app (I : X.IdealSheafData) (n : ℕ) {N : Y.Modules}
    (ψ : @Quiver.Hom Y.Modules _ (SheafOfModules.unit Y.ringCatSheaf) N) (U : X.Opens) (s : Γ(I.pow n, U)) :
    (I.powι n ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward f).map ψ).app U s =
      ψ.app (f ⁻¹ᵁ U) ((f.app U).hom s.1) := rfl

/-- **`f^♯(s)` lies in `J(V)ⁿ` on a good open**: for `s ∈ Γ(U, Iⁿ)`, `U' ≤ U` affine and `V ≤ f⁻¹U'` affine,
`f^♯(s)|_V = f.appLE U' V (s|_{U'}) ∈ (I(U')ⁿ)·Γ(V) = (I(U')·Γ(V))ⁿ = J(V)ⁿ`
(`comap_ideal_eq_map_appLE`, `Ideal.map_pow`). -/
theorem res_app_mem_pow (I : X.IdealSheafData) (n : ℕ) (U : X.Opens) (s : Γ(I.pow n, U))
    (U' : X.affineOpens) (hU' : U'.1 ≤ U) (V : Y.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U'.1)
    (hV : V.1 ≤ f ⁻¹ᵁ U) :
    Y.presheaf.map (homOfLE hV).op ((f.app U).hom s.1) ∈ ((I.comap f).ideal V) ^ n := by
  have h1 : Y.presheaf.map (homOfLE hV).op ((f.app U).hom s.1) =
      (f.appLE U'.1 V.1 e).hom (X.presheaf.map (homOfLE hU').op s.1) := by
    have := congrArg (fun k => k.hom s.1) (f.map_appLE e (homOfLE hU').op)
    exact this.symm
  rw [h1, AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f U' V e, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ (s.2 U' hU')

/-- **`θ_n` kills the cokernel of `μ_n`**: `θ_n ≫ cokernel.π μ_n = 0` (so `θ_n` factors through the
monomorphism `μ_n`, `Abelian.monoLift`). Transpose under `f^* ⊣ f_*` (`homEquiv_reesPullbackToUnit_comp`):
it suffices that for every open `U ⊆ X` and `s ∈ Γ(U, Iⁿ)` the section `π(f^♯ s) ∈ Γ(f⁻¹U, coker μ_n)` vanishes;
this is local (`section_eq_zero_of_locally`), and on a good affine `V ∋ y` (`exists_good_affine`) one has
`f^♯(s)|_V ∈ J(V)ⁿ = (gⁿ)` (`res_app_mem_pow`, `Ideal.span_singleton_pow`), i.e. `f^♯(s)|_V = r·gⁿ = μ_n(r • x^{⊗n})`
for `x ∈ Γ(V, J)` with `ι(x) = g` (`exists_powToUnit_app_eq`), which `π` kills (`cokernel.condition`). -/
theorem reesPullbackToUnit_comp_cokernel_π (I : X.IdealSheafData)
    (hf : MiyaokaMori.Statement.IsInvertibleIdeal (I.comap f)) (n : ℕ) :
    I.reesPullbackToUnit f n ≫ cokernel.π ((I.comap f).monoidalPowToUnit n) = 0 := by
  set μ := (I.comap f).monoidalPowToUnit n with hμ
  refine ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective ?_
  rw [homEquiv_reesPullbackToUnit_comp f I n (cokernel.π μ), Adjunction.homEquiv_unit, Functor.map_zero,
    comp_zero]
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ (fun U => ?_)
  ext s
  rw [transpose_app f I n (cokernel.π μ) U s]
  show (cokernel.π μ).app (f ⁻¹ᵁ U) ((f.app U).hom s.1) = 0
  apply section_eq_zero_of_locally
  intro y hy
  obtain ⟨U', hU'aff, hyU', hU'U⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (X.isBasis_affineOpens))
      (show f.base y ∈ U from hy)
  obtain ⟨V, hyV, hVW, hVU', g, hJV⟩ := exists_good_affine f hf (f ⁻¹ᵁ U) y hy ⟨U', hU'aff⟩ hyU'
  refine ⟨V.1, hVW, hyV, ?_⟩
  rw [← app_res]
  have hmem := res_app_mem_pow f I n U s ⟨U', hU'aff⟩ hU'U V hVU' hVW
  rw [hJV, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hmem
  obtain ⟨r, hr⟩ := hmem
  obtain ⟨x, hx⟩ : ∃ x : Γ((I.comap f).toModules, V.1),
      (AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)).app V.1 x = g := by
    have : g ∈ Set.range ((AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)).app V.1) := by
      rw [show Set.range ((AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)).app V.1) =
          ((I.comap f).ideal V : Set Γ(Y, V)) from (I.comap f).range_toModules_ι_app V, hJV]
      exact Ideal.mem_span_singleton_self g
    exact this
  obtain ⟨t, ht⟩ := AlgebraicGeometry.Scheme.Modules.exists_powToUnit_app_eq
    (AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)) V.1 x n r
  rw [hx, hr] at ht
  have ht' : (μ.app V.1 t : Γ(Y, V)) =
      Y.presheaf.map (homOfLE hVW).op ((f.app U).hom s.1) := ht
  have key : (cokernel.π μ).app V.1 (μ.app V.1 t) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← AlgebraicGeometry.Scheme.Modules.Hom.comp_app, cokernel.condition]
    rfl
  have := congrArg ((cokernel.π μ).app V.1) ht'
  rw [key] at this
  exact this.symm

/-- **`Ψ_1` is an epimorphism.** Local surjectivity on sections (`epi_iff_locally_surjective_sections`): given
`t ∈ Γ(W, J^{⊗1})` and `y ∈ W`, take a good affine `V ∋ y`, `V ≤ W`, `V ≤ f⁻¹U'` (`U'` affine), so that
`J(V) = I(U')·Γ(V)` (`comap_ideal_eq_map_appLE`). Write `t|_V = 1 ⊗ x` with `x := (λ_ J).hom (t|_V)`
(`leftUnitor_inv_app_eq_tensorSections_one`); then `μ_1(t|_V) = ι(x) ∈ J(V)` (`powToUnit_one_app_tensorSections_one`,
`range_toModules_ι_app`). The values of `θ_1` on `Γ(V, f^*I)` form an ideal containing every `f^♯(a)`, `a ∈ I(U')`
(`reesPullbackToUnit_app_unit`), hence containing `J(V)`: `ι(x) = θ_1(s)` for some `s`. Then
`μ_1(Ψ_1(s)) = θ_1(s) = μ_1(t|_V)` and `μ_1` is injective on sections (`injective_app_of_mono`), so `Ψ_1(s) = t|_V`. -/
theorem epi_monoLift_one (I : X.IdealSheafData)
    (hf : MiyaokaMori.Statement.IsInvertibleIdeal (I.comap f)) [Mono ((I.comap f).monoidalPowToUnit 1)] :
    Epi (Abelian.monoLift ((I.comap f).monoidalPowToUnit 1) (I.reesPullbackToUnit f 1)
      (reesPullbackToUnit_comp_cokernel_π f I hf 1)) := by
  have hΨμ : Abelian.monoLift ((I.comap f).monoidalPowToUnit 1) (I.reesPullbackToUnit f 1)
      (reesPullbackToUnit_comp_cokernel_π f I hf 1) ≫ (I.comap f).monoidalPowToUnit 1 =
      I.reesPullbackToUnit f 1 := Abelian.monoLift_comp _ _ _
  rw [AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections]
  intro W t y hy
  obtain ⟨U', hU'aff, hyU', -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      (show f.base y ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V, hyV, hVW, hVU', g, hJV⟩ := exists_good_affine f hf W y hy ⟨U', hU'aff⟩ hyU'
  refine ⟨V.1, hVW, hyV, ?_⟩
  -- `t|_V = 1 ⊗ x` with `x := (λ_ J).hom (t|_V)`
  have htx : (AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules 1).presheaf.map
        (homOfLE hVW).op t =
      AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ Y.Modules) (I.comap f).toModules V.1 (1 : Γ(Y, V))
        ((λ_ (I.comap f).toModules).hom.app V.1
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules 1).presheaf.map
            (homOfLE hVW).op t)) := by
    rw [← AlgebraicGeometry.Scheme.Modules.leftUnitor_inv_app_eq_tensorSections_one,
      ← ConcreteCategory.comp_apply, ← AlgebraicGeometry.Scheme.Modules.Hom.comp_app, Iso.hom_inv_id,
      AlgebraicGeometry.Scheme.Modules.Hom.id_app]
    rfl
  -- `ι(x) ∈ J(V)`
  have hc : (AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)).app V.1
      ((λ_ (I.comap f).toModules).hom.app V.1
        ((AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules 1).presheaf.map
          (homOfLE hVW).op t)) ∈ (I.comap f).ideal V := by
    have : (AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)).app V.1
        ((λ_ (I.comap f).toModules).hom.app V.1
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules 1).presheaf.map
            (homOfLE hVW).op t)) ∈
        Set.range ((AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)).app V.1) := ⟨_, rfl⟩
    rwa [show Set.range ((AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)).app V.1) =
        ((I.comap f).ideal V : Set Γ(Y, V)) from (I.comap f).range_toModules_ι_app V] at this
  -- the values of `θ_1` on `Γ(V, f^*I)` form an ideal containing `J(V) = I(U')·Γ(V)`
  let R : Ideal Γ(Y, V) :=
    { carrier := Set.range (fun s : Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (I.pow 1), V.1) =>
        ((I.reesPullbackToUnit f 1).app V.1 s : Γ(Y, V)))
      zero_mem' := ⟨0, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨s₁, rfl⟩ ⟨s₂, rfl⟩
        exact ⟨s₁ + s₂, map_add _ _ _⟩
      smul_mem' := by
        rintro c _ ⟨s, rfl⟩
        refine ⟨c • s, ?_⟩
        show ((I.reesPullbackToUnit f 1).app V.1 (c • s) : Γ(Y, V)) =
          c • ((I.reesPullbackToUnit f 1).app V.1 s : Γ(Y, V))
        rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul] }
  have hR : (I.comap f).ideal V ≤ R := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨U', hU'aff⟩ V hVU',
      Ideal.map_le_iff_le_comap]
    intro a ha
    have ha' : a ∈ (I.powSubmodule 1).obj (op U') := by
      rw [I.mem_powSubmodule_iff_of_isAffineOpen 1 ⟨U', hU'aff⟩ a, pow_one]
      exact ha
    refine ⟨((AlgebraicGeometry.Scheme.Modules.pullback f).obj (I.pow 1)).presheaf.map (homOfLE hVU').op
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (I.pow 1)).app U'
        ⟨a, ha'⟩), ?_⟩
    exact reesPullbackToUnit_app_res_unit f I 1 U' ⟨a, ha'⟩ V.1 hVU'
  obtain ⟨s, hs⟩ := hR hc
  refine ⟨s, ?_⟩
  apply injective_app_of_mono ((I.comap f).monoidalPowToUnit 1) V.1
  have h1 : ((I.comap f).monoidalPowToUnit 1).app V.1
      ((Abelian.monoLift ((I.comap f).monoidalPowToUnit 1) (I.reesPullbackToUnit f 1)
        (reesPullbackToUnit_comp_cokernel_π f I hf 1)).app V.1 s) = (I.reesPullbackToUnit f 1).app V.1 s := by
    rw [← ConcreteCategory.comp_apply, ← AlgebraicGeometry.Scheme.Modules.Hom.comp_app, hΨμ]
  have h2 : (((I.comap f).monoidalPowToUnit 1).app V.1
      ((AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules 1).presheaf.map
        (homOfLE hVW).op t) : Γ(Y, V)) =
      (AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)).app V.1
        ((λ_ (I.comap f).toModules).hom.app V.1
          ((AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules 1).presheaf.map
            (homOfLE hVW).op t)) := by
    exact (congrArg (fun z => ((I.comap f).monoidalPowToUnit 1).app V.1 z) htx).trans
      (AlgebraicGeometry.Scheme.Modules.powToUnit_one_app_tensorSections_one
        (AlgebraicGeometry.Scheme.EffCartier.idealIncl (I.comap f)) V.1 _)
  rw [h1]
  exact hs.trans h2.symm

end AlgebraicGeometry.Scheme.ReesLiftMapsAux

/-- **The graded maps of the Rees lift data** (Stacks 0806, existence; the sheaf-theoretic content of
Stacks 01O4 for the Rees algebra). Let `J := I.comap f` be invertible. There are `O_Y`-linear maps
`Ψ_n : f^*(Iⁿ) ⟶ J^{⊗n}` with `Ψ_n ≫ μ_n = θ_n` for all `n`, and `Ψ_1 : f^*I ⟶ J^{⊗1}` an epimorphism.

Proof (`θ_n := I.reesPullbackToUnit f n`, `μ_n := J.monoidalPowToUnit n`).

1. **`μ_n` is a monomorphism** (`ReesLiftMapsAux.monoidalPowToUnit_mono_of_isInvertibleIdeal`, from the general
   `Modules.powToUnit_mono` of `MonoidalPowToUnit`): `J.toModules` is a line bundle
   (`EffCartier.ideal_isLineBundle`, Stacks 01WQ), so `- ⊗ J` is an equivalence of `Y.Modules`
   (`isEquivalence_tensorRight_of_isLineBundle`) and preserves monomorphisms; `ι = idealIncl J` is a kernel
   inclusion, hence `ι^{⊗n}` is a monomorphism by induction, and the collapse `O_Y^{⊗n} ≅ O_Y` is an isomorphism.
2. **`θ_n` factors through `μ_n`.** `Y.Modules` is abelian, so it suffices that `θ_n ≫ cokernel.π μ_n = 0`
   (`Abelian.monoLift`); then `Ψ_n := Abelian.monoLift μ_n θ_n _` satisfies `Ψ_n ≫ μ_n = θ_n`
   (`Abelian.monoLift_comp`). To see `θ_n ≫ π = 0` (`ReesLiftMapsAux.reesPullbackToUnit_comp_cokernel_π`), transpose
   under `f^* ⊣ f_*`: `θ_n = f^*(powι n) ≫ (f^*O_X ≅ O_Y)` and `pullbackUnitIso` is the transpose of `f^♯`
   (`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`), so the transpose of `θ_n ≫ π` is
   `powι n ≫ f^♯ ≫ f_*π`, and this vanishes iff `π(f^♯ s) = 0 ∈ Γ(f⁻¹U, coker μ_n)` for every open `U ⊆ X` and
   `s ∈ Γ(U, Iⁿ)`. This is local on `f⁻¹U` (`coker μ_n` is a sheaf). Near `y ∈ f⁻¹U` choose an affine `U' ∋ f(y)`,
   `U' ≤ U`, and (from `hf`, shrinking to a basic open) an affine `V ∋ y`, `V ≤ f⁻¹U'`, with `J(V) = (g)`
   (`ReesLiftMapsAux.exists_good_affine`). Then `f^♯(s)|_V = f.appLE U' V (s|_{U'}) ∈ (I(U')ⁿ)·Γ(V) = (I(U')·Γ(V))ⁿ = J(V)ⁿ`
   (`s|_{U'} ∈ I(U')ⁿ` by definition of `Iⁿ`; `comap_ideal_eq_map_appLE`, `Ideal.map_pow`), i.e. `f^♯(s)|_V = r·gⁿ`.
   Writing `g = ι(x)` (`range_toModules_ι_app`), `r·gⁿ = μ_n(r • x^{⊗n})` (`Modules.exists_powToUnit_app_eq`: on pure
   tensors `μ_n` multiplies the `ι`-images), which `π` kills (`cokernel.condition`).
3. **`Ψ_1` is an epimorphism** (`ReesLiftMapsAux.epi_monoLift_one`): epimorphisms of `O_Y`-modules are the locally
   surjective maps on sections (`epi_iff_locally_surjective_sections`). Given `t ∈ Γ(W, J^{⊗1})` and `y ∈ W`, take a
   good affine `V ∋ y`, `V ≤ W`, `V ≤ f⁻¹U'` as in step 2; `t|_V = 1 ⊗ x` with `x := (λ_ J).hom(t|_V)`, and
   `μ_1(t|_V) = ι(x) ∈ J(V) = I(U')·Γ(V)`. The values of `θ_1` on `Γ(V, f^*I)` form an ideal of `Γ(V)` containing
   every `f^♯(a)`, `a ∈ I(U')` (`θ_1(η(a)|_V) = f.appLE U' V (a)` for the unit `η` of the adjunction,
   `ReesLiftMapsAux.reesPullbackToUnit_app_res_unit`), hence containing `J(V)`: `ι(x) = θ_1(s)` for some `s`. Then
   `μ_1(Ψ_1(s)) = θ_1(s) = μ_1(t|_V)`, and `μ_1` is injective on sections (a monomorphism), so `Ψ_1(s) = t|_V`.

Edge cases. `Y = ∅`: all sheaves are zero. `I = ⊤`: `J = ⊤`, `θ_n` and `μ_n` are isomorphisms. `I = ⊥`, `Y ≠ ∅`:
`hf` cannot hold (vacuous). `n = 0`: `μ_0 = monoidalUnitIso.hom` (`monoidalPowToUnit_zero`), an isomorphism; the
general argument covers it.

Note that no gluing of locally constructed maps is needed: the factorization is obtained categorically
(`Abelian.monoLift`) once `μ_n` is known to be a monomorphism, so no section computation of `f^*(Iⁿ)` is
needed; the local computation happens on `Γ(U, Iⁿ)` via the adjunction. -/
theorem AlgebraicGeometry.Scheme.blowup_exists_reesLiftMaps {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (hf : MiyaokaMori.Statement.IsInvertibleIdeal (I.comap f)) :
    ∃ Ψ : ∀ n : ℕ, (AlgebraicGeometry.Scheme.Modules.pullback f).obj (I.reesAlgebra.part n) ⟶
        AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules n,
      (∀ n : ℕ, Ψ n ≫ (I.comap f).monoidalPowToUnit n = I.reesPullbackToUnit f n) ∧
        CategoryTheory.Epi (Ψ 1) := by
  haveI : ∀ n, Mono ((I.comap f).monoidalPowToUnit n) := fun n =>
    AlgebraicGeometry.Scheme.ReesLiftMapsAux.monoidalPowToUnit_mono_of_isInvertibleIdeal (I.comap f) hf n
  refine ⟨fun n => Abelian.monoLift ((I.comap f).monoidalPowToUnit n) (I.reesPullbackToUnit f n)
    (AlgebraicGeometry.Scheme.ReesLiftMapsAux.reesPullbackToUnit_comp_cokernel_π f I hf n),
    fun n => Abelian.monoLift_comp _ _ _, ?_⟩
  exact AlgebraicGeometry.Scheme.ReesLiftMapsAux.epi_monoLift_one f I hf

end
