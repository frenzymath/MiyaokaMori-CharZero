import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentFreeStalksLocallyFree

/-! # Flatness of a quasi-coherent module is affine-local (Stacks 01U4)

Stacks 01U4, (1)⇔(2): a quasi-coherent `O_X`-module `F` is flat over `S` (stalkwise, `FlatOver`)
iff for all affine opens `U ⊆ X`, `V ⊆ S` with `U ⊆ f⁻¹V`, the module `Γ(U, F)`, with scalars
restricted along `f.appLE V U : Γ(S, V) → Γ(X, U)`, is a flat `Γ(S, V)`-module.

## Proof outline

Write `A = Γ(X, U)`, `R = Γ(S, V)`, `φ = f.appLE V U h : R → A`, `M = Γ(F, U)` (an `A`-module, hence an
`R`-module through `φ`).

1. Algebra (Stacks 00HT(6), the direction "flat ⇒ localizations flat", for a localization on the
   `A`-side): if `M` is `R`-flat and `g : M → M'` is the localization of `M` at a submonoid `S ⊆ A`,
   then `M'` is `R`-flat (`Stacks01u4Aux.flat_of_isLocalizedModule_algebra`). Proof: for an
   `R`-submodule `N ⊆ P`, the map `N ⊗_R M' → P ⊗_R M'` is the `S`-localization of the injective map
   `N ⊗_R M → P ⊗_R M` (Mathlib `IsLocalizedModule.map_lTensor`), and localization preserves
   injectivity (`IsLocalizedModule.map_injective`).
   The converse direction "all localizations at maximal ideals of `A` flat ⇒ flat" is Mathlib's
   `Module.flat_of_isLocalized_maximal`.
2. Stalks: for `x ∈ U` with prime `p ⊆ A`, the germ map `M → F_x` is the localization at `p`
   (`CoherentFreeStalksAux.isLocalizedModule_germ`, Stacks 01I8), and `O_{S,f x}` is the localization
   of `R` at the prime of `f x` (`IsAffineOpen.isLocalization_stalk`). The two `R`-module structures on
   `F_x` — through `germ_U ∘ φ` and through `stalkMap ∘ germ_V` — coincide
   (`Stacks01u4Aux.germ_appLE_eq_stalkMap_germ`, from `Scheme.Hom.germ_stalkMap_apply`), so
   `F_x` is flat over `O_{S,f x}` iff it is flat over `R` (`Module.flat_iff_of_isLocalization`):
   `Stacks01u4Aux.flatAt_iff_flat_stalk`.
3. (⇒) `Module.flat_of_isLocalized_maximal` over the maximal ideals `P` of `A`, with the stalks at the
   points `hU.fromSpec P` as the localizations (step 2 identifies the prime of `hU.fromSpec P` with
   `P`, by injectivity of `fromSpec`).
   (⇐) Choose affine `V ∋ f x`, affine `U ∋ x` with `U ⊆ f⁻¹V` (affine opens form a basis); step 1
   gives `F_x` flat over `R`, step 2 converts to flatness over `O_{S,f x}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks01u4Aux

open AlgebraicGeometry

/-- **Localizing on the algebra side preserves flatness over the base** (Stacks 00HT(6), direction
"flat ⇒ localizations flat"): `R → A` a ring map, `M` an `A`-module that is flat over `R`,
`g : M → M'` the localization of `M` at a submonoid `S ⊆ A`; then `M'` is flat over `R`.
Proof: for an `R`-submodule `N ⊆ P`, `N ⊗_R M' → P ⊗_R M'` is the `S`-localization of
`N ⊗_R M → P ⊗_R M` (`IsLocalizedModule.map_lTensor`), which is injective by flatness of `M`, and
localization preserves injectivity (`IsLocalizedModule.map_injective`). -/
theorem flat_of_isLocalizedModule_algebra {R : Type u} {A M M' : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
    (S : Submonoid A) (g : M →ₗ[A] M') [IsLocalizedModule S g] [hM : Module.Flat R M] :
    Module.Flat R M' := by
  have hM' := Module.Flat.iff_lTensor_injectiveₛ.mp hM
  refine Module.Flat.iff_lTensor_injectiveₛ.mpr fun P _ _ N => ?_
  have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor A M N.subtype) := by
    rw [TensorProduct.AlgebraTensorModule.coe_lTensor]
    exact hM' N
  have h2 := IsLocalizedModule.map_injective S (TensorProduct.AlgebraTensorModule.rTensor R N g)
    (TensorProduct.AlgebraTensorModule.rTensor R P g) _ h1
  rw [IsLocalizedModule.map_lTensor] at h2
  rw [← TensorProduct.AlgebraTensorModule.coe_lTensor (A := A)]
  exact h2

variable {X S : Scheme.{u}}

/-- The two ways of sending a section `r ∈ Γ(S, V)` to the stalk `O_{X,x}` (for `x ∈ U ⊆ f⁻¹V`)
agree: `germ_U (f.appLE V U h r) = f.stalkMap x (germ_V r)`. -/
theorem germ_appLE_eq_stalkMap_germ (f : X ⟶ S) {U : X.Opens} {V : S.Opens} (h : U ≤ f ⁻¹ᵁ V)
    {x : X} (hx : x ∈ U) (hfx : f x ∈ V) (r : Γ(S, V)) :
    X.presheaf.germ U x hx (f.appLE V U h r) =
      f.stalkMap x (S.presheaf.germ V (f x) hfx r) := by
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.appLE, CommRingCat.comp_apply,
    TopCat.Presheaf.germ_res_apply]

/-- The `Γ(X, U)`-linear germ map `Γ(F, U) → F_x`, where the stalk carries the `Γ(X, U)`-module
structure `Module.compHom` through the germ map of the structure sheaf. -/
def germLinear (F : X.Modules) (U : X.Opens) {x : X} (hx : x ∈ U) :
    letI : Module Γ(X, U) (F.presheaf.stalk x) :=
      Module.compHom (F.presheaf.stalk x) (X.presheaf.germ U x hx).hom
    Γ(F, U) →ₗ[Γ(X, U)] F.presheaf.stalk x :=
  letI : Module Γ(X, U) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) (X.presheaf.germ U x hx).hom
  { toFun := F.presheaf.germ U x hx
    map_add' := map_add _
    map_smul' := fun r m => CoherentFreeStalksAux.germ_smul' F hx r m }

/-- **Stalk flatness over the base stalk is flatness over the affine sections** (the local content
of Stacks 01U4): for affine `x ∈ U ⊆ f⁻¹V`, `V` affine, `F_x` is flat over `O_{S,f x}` (through the
stalk map, i.e. `FlatAt f F x`) iff it is flat over `R = Γ(S, V)` through `germ_U ∘ f.appLE V U h`.
Proof: `O_{S,f x}` is the localization of `R` at the prime of `f x`
(`IsAffineOpen.isLocalization_stalk`), the two `R`-actions on `F_x` agree
(`germ_appLE_eq_stalkMap_germ`), so `Module.flat_iff_of_isLocalization` applies. -/
theorem flatAt_iff_flat_stalk (f : X ⟶ S) (F : X.Modules) {U : X.Opens} {V : S.Opens}
    (hV : IsAffineOpen V) (h : U ≤ f ⁻¹ᵁ V) {x : X} (hx : x ∈ U) :
    letI : Module Γ(S, V) (F.presheaf.stalk x) :=
      Module.compHom (F.presheaf.stalk x) ((X.presheaf.germ U x hx).hom.comp (f.appLE V U h).hom)
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatAt f F x ↔ Module.Flat Γ(S, V) (F.presheaf.stalk x) := by
  letI : Module Γ(S, V) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) ((X.presheaf.germ U x hx).hom.comp (f.appLE V U h).hom)
  have hfx : f x ∈ V := h hx
  letI := S.presheaf.algebra_section_stalk ⟨f x, hfx⟩
  haveI hloc : IsLocalization.AtPrime (S.presheaf.stalk (f x)) (hV.primeIdealOf ⟨f x, hfx⟩).asIdeal :=
    hV.isLocalization_stalk ⟨f x, hfx⟩
  letI := AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.relativeStalkModule f F x
  haveI : IsScalarTower Γ(S, V) (S.presheaf.stalk (f x)) (F.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_smul fun r m => ?_
    change f.stalkMap x (S.presheaf.germ V (f x) hfx r) • m =
      X.presheaf.germ U x hx (f.appLE V U h r) • m
    rw [germ_appLE_eq_stalkMap_germ f h hx hfx r]
  exact Module.flat_iff_of_isLocalization (S.presheaf.stalk (f x))
    (hV.primeIdealOf ⟨f x, hfx⟩).asIdeal.primeCompl (F.presheaf.stalk x)

/-- The prime ideal of the point `hU.fromSpec y` is `y` (injectivity of `fromSpec`). -/
theorem primeIdealOf_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (hy : hU.fromSpec y ∈ U) : hU.primeIdealOf ⟨hU.fromSpec y, hy⟩ = y :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨hU.fromSpec y, hy⟩)

/-- Every point of `Spec Γ(X, U)` lands in `U`. -/
theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec y ∈ U := by
  have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
  rwa [hU.range_fromSpec] at this

/-- **Sections of a quasi-coherent module on an affine open are flat over `R` if all stalks are**
(Stacks 00HT(6) "⇐", geometric form): `φ : R → Γ(X, U)`, `U` affine, `F` quasi-coherent; if every
stalk `F_x` (`x ∈ U`) is `R`-flat through `germ_U ∘ φ`, then `Γ(F, U)` is `R`-flat through `φ`.
Proof: `Module.flat_of_isLocalized_maximal` over the maximal ideals `P` of `Γ(X, U)`, using the
stalks at `hU.fromSpec P` as the localizations (`isLocalizedModule_germ`, `primeIdealOf_fromSpec`). -/
theorem flat_sections_of_flat_stalks (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {R : Type u} [CommRing R] (φ : R →+* Γ(X, U))
    (H : ∀ (x : X) (hx : x ∈ U),
      letI : Module R (F.presheaf.stalk x) :=
        Module.compHom (F.presheaf.stalk x) ((X.presheaf.germ U x hx).hom.comp φ)
      Module.Flat R (F.presheaf.stalk x)) :
    letI : Module R Γ(F, U) := Module.compHom Γ(F, U) φ
    Module.Flat R Γ(F, U) := by
  letI : Algebra R Γ(X, U) := φ.toAlgebra
  letI : Module R Γ(F, U) := Module.compHom Γ(F, U) φ
  haveI : IsScalarTower R Γ(X, U) Γ(F, U) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let pt : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal], X :=
    fun P _ => hU.fromSpec ⟨P, Ideal.IsMaximal.isPrime ‹_›⟩
  have hpt : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal], pt P ∈ U := fun P _ => fromSpec_mem hU _
  letI instA : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal], Module Γ(X, U) (F.presheaf.stalk (pt P)) :=
    fun P _ => Module.compHom (F.presheaf.stalk (pt P)) (X.presheaf.germ U (pt P) (hpt P)).hom
  letI instR : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal], Module R (F.presheaf.stalk (pt P)) :=
    fun P _ => Module.compHom (F.presheaf.stalk (pt P))
      ((X.presheaf.germ U (pt P) (hpt P)).hom.comp φ)
  haveI instT : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal],
      IsScalarTower R Γ(X, U) (F.presheaf.stalk (pt P)) :=
    fun P _ => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let g : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal], Γ(F, U) →ₗ[Γ(X, U)] F.presheaf.stalk (pt P) :=
    fun P _ => germLinear F U (hpt P)
  haveI instL : ∀ (P : Ideal Γ(X, U)) [P.IsMaximal], IsLocalizedModule.AtPrime P (g P) := by
    intro P hP
    have := CoherentFreeStalksAux.isLocalizedModule_germ F hU (hpt P) (fun _ _ => rfl) (g P)
      (fun _ => rfl)
    rwa [primeIdealOf_fromSpec hU ⟨P, hP.isPrime⟩ (hpt P)] at this
  exact @Module.flat_of_isLocalized_maximal R Γ(X, U) _ _ _ Γ(F, U) _ _ _ _
    (fun P _ => F.presheaf.stalk (pt P)) (fun P _ => inferInstance) instR instA instT g instL
    (fun P _ => H (pt P) (hpt P))

/-- **Stalks of a quasi-coherent module on an affine open are flat over `R` if the sections are**
(Stacks 00HT(6) "⇒", geometric form): `φ : R → Γ(X, U)`, `U` affine, `F` quasi-coherent,
`Γ(F, U)` flat over `R` through `φ`; then each stalk `F_x` (`x ∈ U`) is `R`-flat through
`germ_U ∘ φ`. Proof: `F_x` is the localization of `Γ(F, U)` at the prime of `x`
(`isLocalizedModule_germ`), and `flat_of_isLocalizedModule_algebra`. -/
theorem flat_stalk_of_flat_sections (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) {R : Type u} [CommRing R] (φ : R →+* Γ(X, U))
    (H : letI : Module R Γ(F, U) := Module.compHom Γ(F, U) φ
      Module.Flat R Γ(F, U)) (x : X) (hx : x ∈ U) :
    letI : Module R (F.presheaf.stalk x) :=
      Module.compHom (F.presheaf.stalk x) ((X.presheaf.germ U x hx).hom.comp φ)
    Module.Flat R (F.presheaf.stalk x) := by
  letI : Algebra R Γ(X, U) := φ.toAlgebra
  letI : Module R Γ(F, U) := Module.compHom Γ(F, U) φ
  haveI : IsScalarTower R Γ(X, U) Γ(F, U) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : Module Γ(X, U) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) (X.presheaf.germ U x hx).hom
  letI : Module R (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) ((X.presheaf.germ U x hx).hom.comp φ)
  haveI : IsScalarTower R Γ(X, U) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsLocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (germLinear F U hx) :=
    CoherentFreeStalksAux.isLocalizedModule_germ F hU hx (fun _ _ => rfl) (germLinear F U hx)
      (fun _ => rfl)
  haveI : Module.Flat R Γ(F, U) := H
  exact flat_of_isLocalizedModule_algebra (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (germLinear F U hx)

end Stacks01u4Aux

/-- Stacks 01U4 (1)⇔(2): a quasi-coherent `F` is flat over `S` (stalkwise) iff for all affine
opens `U ⊆ X`, `V ⊆ S` with `U ⊆ f⁻¹V`, `Γ(U, F)` is a flat `Γ(S, V)`-module via
`f.appLE V U`. -/
theorem AlgebraicGeometry.Scheme.Modules.isFlatOver_iff_affine {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] :
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f F ↔
      ∀ (U : X.affineOpens) (V : S.affineOpens) (h : U.1 ≤ f ⁻¹ᵁ V.1),
        letI : Module Γ(S, V.1) Γ(F, U.1) := Module.compHom _ (f.appLE V.1 U.1 h).hom
        Module.Flat Γ(S, V.1) Γ(F, U.1) := by
  constructor
  · intro hF U V h
    exact Stacks01u4Aux.flat_sections_of_flat_stalks F U.2 (f.appLE V.1 U.1 h).hom
      fun x hx => (Stacks01u4Aux.flatAt_iff_flat_stalk f F V.2 h hx).mp (hF x)
  · intro H x
    obtain ⟨V, hV, hfxV, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
      (show f x ∈ (⊤ : S.Opens) from trivial)
    obtain ⟨U, hU, hxU, hUV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ V from hfxV)
    exact (Stacks01u4Aux.flatAt_iff_flat_stalk f F hV hUV hxU).mpr
      (Stacks01u4Aux.flat_stalk_of_flat_sections F hU (f.appLE V U hUV).hom
        (H ⟨U, hU⟩ ⟨V, hV⟩ hUV) x hxU)

end
