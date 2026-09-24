import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pbAffineOpen
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyZeroEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01yi
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.SheafCohomologyFiniteTwoOutOfThree
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.ProperOverNoetherianDevissageGenerator

/-! # Finiteness of the sections of a proper pushforward on affine opens

Stacks 02O5 (coherent-proposition-proper-pushforward-coherent) in degree `p = 0`, affine-local form:
`f : X → Y` proper, `Y` locally Noetherian, `F` coherent on `X`, `V ⊆ Y` affine open ⇒ the
`Γ(Y, V)`-module `Γ(f_*F, V) = Γ(F, f⁻¹V)` is finite.

Together with quasi-coherence of `f_*F` (Stacks 01LC) and `isFiniteType_of_finite_affine_sections` this
is exactly what the coherence of the proper pushforward (`pushforward_isCoherent_of_isProper`,
Stacks 02O5) needs.

Source: Stacks 02O5, EGA III 3.2.1; the route goes through Stacks 02O6 at `i = 0` applied to
`f⁻¹V → V = Spec Γ(Y, V)`, so that the whole hard core (Chow's lemma + dévissage) lives in
`ProperOverNoetherianDevissageGenerator.lean`.

Import note: `Stacks02o5.lean` imports this module, so this module cannot import `Stacks02o6`. Instead
it imports the three building blocks of Stacks 02O6 directly (`Stacks01yi`,
`SheafCohomologyFiniteTwoOutOfThree`, `ProperOverNoetherianDevissageGenerator`) and re-assembles the
`i = 0` case of `finite_sheafCohomology_of_isProper` inline.

This module proves `Scheme.Modules.isFiniteType_restrict_of_isOpenImmersion` (finite type is preserved by
`restrict` along an open immersion, quasi-coherent case) and `finite_sections_pushforward_of_isProper`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- **Finite type is preserved by restriction along an open immersion** (Stacks 01B5/01BD, here for
quasi-coherent modules via Stacks 01PB). `j : X → Y` an open immersion, `M` a quasi-coherent
`O_Y`-module of finite type ⇒ `M.restrict j` (Mathlib `Scheme.Modules.restrict`) is of finite type.

**Proof.** By `isFiniteType_of_finite_affine_sections` (Stacks 01PB "⇐" + locality of finite type) it suffices to find, for every `x : X`, an affine open
`W ∋ x` with `Γ(M.restrict j, W)` a finite `Γ(X, W)`-module. Take any affine open `W ∋ x`
(`exists_isAffineOpen_mem_and_subset`). Then `j ''ᵁ W` is an affine open of `Y`
(`IsAffineOpen.image_of_isOpenImmersion`), so `Γ(M, j ''ᵁ W)` is a finite `Γ(Y, j ''ᵁ W)`-module by
Stacks 01PB "⇒" on an affine open (`finite_sections_of_isFiniteType`).
Finally `Γ(M.restrict j, W)` is `Γ(M, j ''ᵁ W)` with scalars restricted along the ring isomorphism
`(j.appIso W).inv : Γ(X, W) ≅ Γ(Y, j ''ᵁ W)` (Mathlib `restrictAppIso`, `smul_restrictAppIso_inv`), i.e.
the identity is a semilinear bijection over the ring isomorphism `(j.appIso W).hom`; finiteness transports
along it (`Module.Finite.of_surjective`).

Edge cases: `X = ∅` (no `x`, vacuous), `W` arbitrary affine (the zero ring if `W = ∅`), fine. -/
theorem Scheme.Modules.isFiniteType_restrict_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) [M.IsQuasicoherent] [M.IsFiniteType] :
    (M.restrict j).IsFiniteType := by
  apply Scheme.Modules.isFiniteType_of_finite_affine_sections
  intro x
  obtain ⟨W, hW, hxW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : X.Opens)) (x := x) trivial
  refine ⟨W, hW, hxW, ?_⟩
  have : Module.Finite Γ(Y, j ''ᵁ W) Γ(M, j ''ᵁ W) :=
    M.finite_sections_of_isFiniteType (hW.image_of_isOpenImmersion j)
  let e : Γ(Y, j ''ᵁ W) ≃+* Γ(X, W) := (j.appIso W).commRingCatIsoToRingEquiv
  have : RingHomSurjective (e : Γ(Y, j ''ᵁ W) →+* Γ(X, W)) := ⟨e.surjective⟩
  let φ : Γ(M, j ''ᵁ W) →ₛₗ[(e : Γ(Y, j ''ᵁ W) →+* Γ(X, W))] Γ(M.restrict j, W) :=
    { toFun := (M.restrictAppIso j W).inv
      map_add' := fun a b => by simp
      map_smul' := fun r m => by
        have := Scheme.Modules.smul_restrictAppIso_inv_apply j M W r m
        exact this }
  exact Module.Finite.of_surjective φ
    (show Function.Surjective φ from
      (ConcreteCategory.bijective_of_isIso (M.restrictAppIso j W).inv).surjective)

/-- **Finiteness of sections of a proper pushforward** (Stacks 02O5 for `R^0 f_*`, affine-local form;
EGA III 3.2.1). `Y` locally Noetherian, `f : X → Y` proper, `F` coherent, `V ⊆ Y` affine open.
Then `Γ((pushforward f).obj F, V)` — which is by definition of `Scheme.Modules.pushforward` the module
`Γ(F, f ⁻¹ᵁ V)` with `Γ(Y, V)` acting through `f.app V : Γ(Y, V) → Γ(X, f ⁻¹ᵁ V)` — is a finite
`Γ(Y, V)`-module.

**Proof as formalized below (route through Stacks 02O6 at `i = 0`).**
Write `A := Γ(Y, V)`, `U := f ⁻¹ᵁ V`, `X_V := U.toScheme`, `F_V := F.restrict U.ι`.
1. *`A` is Noetherian*: `Y` is locally Noetherian and `V` is affine open
   (Mathlib `IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`).
2. *`g : X_V → Spec A` is proper*: `g := (f ∣_ V) ≫ hV.isoSpec.hom`. `f ∣_ V` is proper because
   properness is local on the target / stable under base change along the open immersion `V.ι`
   (Stacks 01W3/01W4; Mathlib instance `IsProper (f ∣_ V)`), the isomorphism `hV.isoSpec.hom` is proper
   (Mathlib instances: an isomorphism is a closed immersion, hence finite, hence proper), and compositions
   of proper morphisms are proper (`IsProper.instCompScheme`).
3. *`F_V` is coherent*: quasi-coherence is preserved by `restrict` (Mathlib instance
   `Scheme.Modules.isQuasicoherent_restrictFunctor`); finite type is preserved by `restrict` along an open
   immersion (`Scheme.Modules.isFiniteType_restrict_of_isOpenImmersion` above, Stacks 01PB both ways).
4. *Stacks 02O6 at `i = 0`* (re-assembled inline from its building blocks because of the import
   constraint explained in the module docstring): `X_V` is Noetherian
   (`LocallyOfFiniteType.isLocallyNoetherian g`, `QuasiCompact.compactSpace_of_compactSpace g`); the
   coherent dévissage `Scheme.Modules.coherent_devissage` (Stacks 01YI) applied to
   `P(G) :⟺ ∀ j, H^j(X_V, G)` finite over `A`, with (0) zero modules (`sheafCohomology.finite_of_isZero`),
   (1) two-out-of-three along short exact sequences (`sheafCohomology.finite_X₃_of_finite_X₁_X₂` etc.),
   (2) generators (`exists_coherent_generic_finite_sheafCohomology_of_isProper g`, the Chow's-lemma
   step). This gives
   `Module.Finite A (sheafCohomology X_V F_V 0)` for the module structure `sheafCohomology.moduleOver`
   given by `letI : X_V.Over (Spec A) := ⟨g⟩` (scalars restricted along
   `ρ := (ΓSpecIso A).inv ≫ g.appTop : A → Γ(X_V, ⊤)`).
5. *`H^0 = Γ`* (`sheafCohomologyZeroEquiv F_V :
   H^0(X_V, F_V) ≃ₗ[Γ(X_V, ⊤)] Γ(F_V, ⊤)`, `A`-compatibility `sheafCohomologyZeroEquiv_smulOver`), then
   `Γ(F_V, ⊤) ≅ Γ(F, U.ι ''ᵁ ⊤)` (Mathlib `restrictAppIso`, semilinear over `(U.ι.appIso ⊤).inv` by
   `smul_restrictAppIso_hom`), then the restriction map `F.presheaf.map (eqToHom hUeq).op` along the
   equality of opens `U = U.ι ''ᵁ ⊤` (`Scheme.Opens.ι_image_top`), semilinear over
   `X.presheaf.map (eqToHom hUeq).op` (`Scheme.Modules.map_smul`). The composite
   `φ : H^0(X_V, F_V) → Γ(F, U) = Γ(f_*F, V)` is a bijection (Stacks 01XK / 01E4 in degree `0`, here the
   definition of the pushforward, `pushforward_obj_obj`).
6. *Compatibility of the two `A`-actions* (so that `φ` is `A`-linear): the ring map
   `A → Γ(X, U)` obtained from step 5, `ρ ≫ (U.ι.appIso ⊤).inv ≫ X.presheaf.map (eqToHom hUeq).op`,
   equals `f.app V`. Indeed `(U.ι.appIso ⊤).inv ≫ X.presheaf.map (eqToHom hUeq).op = U.topIso.hom`
   (`Scheme.Opens.ι_appIso`, `topIso_hom`), `hV.isoSpec.hom.appTop = (ΓSpecIso A).hom ≫ V.topIso.inv`
   (`IsAffineOpen.isoSpec_hom_appTop`), `f ∣_ V = f.resLE V U le_rfl` (`Scheme.Hom.resLE_eq_morphismRestrict`)
   and `(f.resLE V U _).app ⊤ = V.topIso.hom ≫ f.appLE V U _ ≫ U.topIso.inv` (`Scheme.Hom.resLE_app_top`);
   the isomorphisms cancel and `f.appLE V U le_rfl = f.app V` (`Scheme.Hom.appLE_eq_app`). The `A`-action on
   `Γ(f_*F, V)` is by definition `c • m = f.app V c • m`, so `φ` is `A`-linear and surjective, and
   `Module.Finite.of_surjective` finishes.

**Edge cases.** `V = ⊥`: `A` is the zero ring, every module over it is finite. `X = ∅`: `Γ(F, ∅) = 0`,
finite. `Y = Spec A`, `V = ⊤`: the statement is 02O6 at `i = 0` up to `H^0 = Γ`. `f` a closed immersion
or finite: covered by Stacks 01Y6 independently. -/
theorem finite_sections_pushforward_of_isProper {X Y : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian Y] (f : X ⟶ Y) [AlgebraicGeometry.IsProper f]
    (F : X.Modules) [F.IsCoherent] (V : Y.Opens) (hV : AlgebraicGeometry.IsAffineOpen V) :
    Module.Finite Γ(Y, V) Γ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj F, V) := by
  -- step 1
  have hA : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  -- step 2
  let g : (f ⁻¹ᵁ V).toScheme ⟶ Spec Γ(Y, V) := (f ∣_ V) ≫ hV.isoSpec.hom
  have : IsProper hV.isoSpec.hom := inferInstance
  have : IsProper g := inferInstance
  -- step 3
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.quasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.finiteType
  let FV : (f ⁻¹ᵁ V).toScheme.Modules := F.restrict (f ⁻¹ᵁ V).ι
  have : FV.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor (f ⁻¹ᵁ V).ι F
  have : FV.IsFiniteType := Scheme.Modules.isFiniteType_restrict_of_isOpenImmersion (f ⁻¹ᵁ V).ι F
  have : FV.IsCoherent := ⟨inferInstance, inferInstance⟩
  let _ : (f ⁻¹ᵁ V).toScheme.Over (Spec Γ(Y, V)) := ⟨g⟩
  -- step 4: Stacks 02O6 at i = 0, assembled from its building blocks (see the module docstring)
  have : IsLocallyNoetherian (f ⁻¹ᵁ V).toScheme := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace (f ⁻¹ᵁ V).toScheme := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian (f ⁻¹ᵁ V).toScheme := {}
  have h0 : Module.Finite Γ(Y, V) (sheafCohomology (f ⁻¹ᵁ V).toScheme FV 0) :=
    Scheme.Modules.coherent_devissage
      (fun G => ∀ j, Module.Finite Γ(Y, V) (sheafCohomology (f ⁻¹ᵁ V).toScheme G j))
      (fun G hG j => sheafCohomology.finite_of_isZero Γ(Y, V) G hG j)
      (fun S hS _ _ _ =>
        ⟨fun h₁ h₂ => sheafCohomology.finite_X₃_of_finite_X₁_X₂ Γ(Y, V) hS h₁ h₂,
         fun h₁ h₃ => sheafCohomology.finite_X₂_of_finite_X₁_X₃ Γ(Y, V) hS h₁ h₃,
         fun h₂ h₃ => sheafCohomology.finite_X₁_of_finite_X₂_X₃ Γ(Y, V) hS h₂ h₃⟩)
      (fun ξ => exists_coherent_generic_finite_sheafCohomology_of_isProper g ξ)
      FV 0
  -- steps 5-6: transport along H^0 = Γ
  have hUeq : f ⁻¹ᵁ V = (f ⁻¹ᵁ V).ι ''ᵁ ⊤ := (f ⁻¹ᵁ V).ι_image_top.symm
  have hcomp : ((f ⁻¹ᵁ V).ι.appIso ⊤).inv ≫ X.presheaf.map (eqToHom hUeq).op =
      (f ⁻¹ᵁ V).topIso.hom := by
    rw [Scheme.Opens.ι_appIso, Iso.refl_inv]
    erw [Category.id_comp]
    rfl
  have hρ : (Scheme.ΓSpecIso Γ(Y, V)).inv ≫ g.appTop ≫ ((f ⁻¹ᵁ V).ι.appIso ⊤).inv ≫
      X.presheaf.map (eqToHom hUeq).op = f.app V := by
    rw [hcomp]
    simp only [g, Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop]
    rw [← Scheme.Hom.resLE_eq_morphismRestrict]
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id, Scheme.Hom.appLE_eq_app]
  have hρ' : ∀ c : Γ(Y, V), X.presheaf.map (eqToHom hUeq).op (((f ⁻¹ᵁ V).ι.appIso ⊤).inv
      (g.appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv c))) = f.app V c := by
    intro c
    have := ConcreteCategory.congr_hom hρ c
    simpa only [CommRingCat.comp_apply] using this
  let φ : sheafCohomology (f ⁻¹ᵁ V).toScheme FV 0 →ₗ[Γ(Y, V)]
      Γ((Scheme.Modules.pushforward f).obj F, V) :=
    { toFun := fun x => F.presheaf.map (eqToHom hUeq).op
        ((F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).hom (sheafCohomologyZeroEquiv FV x))
      map_add' := fun a b => by simp only [map_add]; rfl
      map_smul' := fun c x => by
        show F.presheaf.map (eqToHom hUeq).op
            ((F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).hom (sheafCohomologyZeroEquiv FV (c • x))) =
          (f.app V c) • F.presheaf.map (eqToHom hUeq).op
            ((F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).hom (sheafCohomologyZeroEquiv FV x))
        rw [sheafCohomologyZeroEquiv_smulOver, Scheme.Modules.smul_restrictAppIso_hom_apply,
          Scheme.Modules.map_smul, ← hρ' c]
        rfl }
  exact Module.Finite.of_surjective φ
    ((ConcreteCategory.bijective_of_isIso (F.presheaf.map (eqToHom hUeq).op)).surjective.comp
      ((ConcreteCategory.bijective_of_isIso (F.restrictAppIso (f ⁻¹ᵁ V).ι ⊤).hom).surjective.comp
        (sheafCohomologyZeroEquiv FV).surjective))

end AlgebraicGeometry

end
