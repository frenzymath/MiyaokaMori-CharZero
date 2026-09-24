import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks02o4
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionFiniteOver
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PushforwardInvIsoPullback

/-! # Finiteness of cohomology for projective schemes over a Noetherian ring

**Stacks 02O4 over an affine Noetherian base, global form**: `f : X → Spec A` projective, `A` Noetherian,
`F` coherent ⇒ `H^i(X, F)` is a finite `A`-module for every `i` (module structure `sheafCohomology.moduleOver`
via `⟨f⟩`). This is `finite_sheafCohomology_restrict_of_isProjectiveMorphism` (Stacks 02O4) for the
affine open `V = ⊤` of `Spec A`, with the bookkeeping `(f ⁻¹ᵁ ⊤) = ⊤`, `F.restrict ⊤.ι ≅ F`,
`Γ(Spec A, ⊤) ≅ A` (`Scheme.ΓSpecIso`) done once and for all.

The invariance of cohomology under the scheme isomorphism `⊤.ι` is obtained from the closed-immersion
comparison (Stacks 02UV, `A`-linear form: an isomorphism is a closed immersion), followed by
`⊤.ι_* (F.restrict ⊤.ι) ≅ F` (`restrictFunctorIsoPullback`, `pushforwardInvIsoPullback`) and
`sheafCohomology.mapIsoOver`.

Source: Stacks 02O4; Hartshorne III.5.2(a) over a Noetherian ring; EGA III 2.2.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Transport of `Module.Finite` along a ring isomorphism `e : S ≅ R` (in `CommRingCat`): if `H` is a finite
`S`-module for the structure `Module.compHom H φ.hom` (`φ : S ⟶ T`, `H` a `T`-module), it is a finite `R`-module
for `Module.compHom H (e.inv ≫ φ).hom`. Proof: the identity is `e.hom`-semilinear and surjective
(`Module.Finite.of_surjective`). -/
private theorem finite_compHom_of_iso_W4 {R S T : CommRingCat.{u}} (e : S ≅ R) (φ : S ⟶ T)
    {H : Type*} [AddCommGroup H] [Module T H]
    (h : @Module.Finite S H _ _ (Module.compHom H φ.hom)) :
    @Module.Finite R H _ _ (Module.compHom H (e.inv ≫ φ).hom) := by
  let _ : Module S H := Module.compHom H φ.hom
  let _ : Module R H := Module.compHom H (e.inv ≫ φ).hom
  refine Module.Finite.of_surjective (σ := e.hom.hom) (M := H)
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => ?_ } Function.surjective_id
  show φ.hom r • x = φ.hom (e.inv.hom (e.hom.hom r)) • x
  have hr : e.inv.hom (e.hom.hom r) = r := by simp
  rw [hr]

/-- **Projective over a Noetherian ring ⇒ finite cohomology** (Stacks 02O4, `S = Spec A`, `V = ⊤`;
Hartshorne III.5.2(a) over a Noetherian ring; EGA III 2.2.1). `A` Noetherian, `f : X → Spec A` projective,
`F` coherent ⇒ `Module.Finite A (H^i(X, F))` for all `i`.

**Proof (as formalized).**
1. `Spec A` is locally Noetherian (Mathlib instance from `IsNoetherianRing A`), so Stacks 02O4
   (`finite_sheafCohomology_restrict_of_isProjectiveMorphism f F ⟨⊤, isAffineOpen_top⟩ i`) gives that
   `H^i(U, G)`, `U := f ⁻¹ᵁ ⊤`, `G := F.restrict U.ι`, is a finite `Γ(Spec A, ⊤)`-module for the structure
   `Module.compHom _ (f.app ⊤ ≫ U.topIso.inv).hom`.
2. *`U = ⊤` definitionally* (`Opens.map_top` is `rfl`), so `U.ι = X.topIso.hom` is an isomorphism, hence a
   closed immersion (Mathlib instance).
3. *Scalars.* `Γ(Spec A, ⊤) ≅ A` by `Scheme.ΓSpecIso A`; the identity of `H^i(U, G)` is semilinear along
   `(ΓSpecIso A).hom`, so `Module.Finite.of_surjective` transports finiteness to the `A`-structure
   `Module.compHom _ ((ΓSpecIso A).inv ≫ (f.app ⊤ ≫ U.topIso.inv)).hom` (`finite_compHom_of_iso_W4`), and
   `f.app ⊤ ≫ U.topIso.inv = (U.ι ≫ f).appTop` (`comp_appTop`, `topIso_inv`, `ι_appTop`, thinness of
   `X.Opensᵒᵖ`) identifies it with `sheafCohomology.moduleOver` for `U.toScheme` over `Spec A` via `U.ι ≫ f`.
4. *Closed immersion.* `U.ι` is a morphism over `Spec A` (`U.ι ≫ f = U.ι ≫ f`), so
   `finite_sheafCohomology_pushforward_of_isClosedImmersion` (Stacks 02UV) gives `Module.Finite A (H^i(X, U.ι_* G))`.
5. *`U.ι_* G ≅ F`.* `G ≅ U.ι^* F` (`restrictFunctorIsoPullback`), `U.ι_* ≅ (U.ι⁻¹)^*`
   (`pushforwardInvIsoPullback (asIso U.ι).symm`), and
   `(U.ι⁻¹)^* (U.ι^* F) ≅ F` (counit of `pullbackEquivalenceOfIso (asIso U.ι)`). Then
   `sheafCohomology.mapIsoOver A e i : H^i(X, U.ι_* G) ≃ₗ[A] H^i(X, F)` and
   `Module.Finite.equiv` conclude.

**Edge cases.** `A = 0`: `X = ∅`, all cohomology `0`, finite. `X = ∅`: same. `F = 0`: `0`. `i` larger than the
dimension: `H^i = 0`, finite. `X = Spec A` (`f = 𝟙`): `H^0 = Γ(X, F)` finite because `F` is coherent (Stacks 01XZ),
`H^i = 0` for `i > 0` (Stacks 01XB); consistent. -/
theorem AlgebraicGeometry.finite_sheafCohomology_of_isProjectiveMorphism_spec
    {A : CommRingCat.{u}} [IsNoetherianRing A] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsProjectiveMorphism f]
    (F : X.Modules) [F.IsCoherent] (i : ℕ) :
    letI : X.Over (AlgebraicGeometry.Spec A) := ⟨f⟩
    Module.Finite A (AlgebraicGeometry.sheafCohomology X F i) := by
  let _ : X.Over (AlgebraicGeometry.Spec A) := ⟨f⟩
  -- Step 1: Stacks 02O4 for the affine open `V = ⊤` of `Spec A`.
  set U : X.Opens := f ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Spec A).Opens) with hUdef
  have h02o4 := AlgebraicGeometry.finite_sheafCohomology_restrict_of_isProjectiveMorphism f F
    ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ i
  set G : U.toScheme.Modules := AlgebraicGeometry.Scheme.Modules.restrict F U.ι with hGdef
  -- Step 2: `U = ⊤`, so `U.ι` is an isomorphism (hence a closed immersion).
  have hι : IsIso U.ι := by
    show IsIso (⊤ : X.Opens).ι
    exact X.topIso.isIso_hom
  -- Step 3: scalars. The `A`-structure on `H^i(U, G)` through `U.ι ≫ f`.
  let _ : U.toScheme.Over (AlgebraicGeometry.Spec A) := ⟨U.ι ≫ f⟩
  have hscal : f.app ⊤ ≫ U.topIso.inv = (U.ι ≫ f).appTop := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Opens.topIso_inv,
      AlgebraicGeometry.Scheme.Opens.ι_appTop]
    exact congrArg (fun g => f.appTop ≫ X.presheaf.map g) (Subsingleton.elim _ _)
  have hZ : Module.Finite A (AlgebraicGeometry.sheafCohomology U.toScheme G i) := by
    have h1 := finite_compHom_of_iso_W4 (AlgebraicGeometry.Scheme.ΓSpecIso A)
      (f.app ⊤ ≫ U.topIso.inv) h02o4
    rw [hscal] at h1
    exact h1
  -- Step 4: cohomology along the closed immersion `U.ι` (Stacks 02UV, `A`-linear form).
  have : U.ι.IsOver (AlgebraicGeometry.Spec A) := ⟨rfl⟩
  have hX := AlgebraicGeometry.Scheme.Modules.finite_sheafCohomology_pushforward_of_isClosedImmersion
    (K := A) U.ι G i
  -- Step 5: `U.ι_* (F.restrict U.ι) ≅ F` for the isomorphism `U.ι`.
  let eZ : U.toScheme ≅ X := asIso U.ι
  let e : (AlgebraicGeometry.Scheme.Modules.pushforward U.ι).obj G ≅ F :=
    (AlgebraicGeometry.Scheme.Modules.pushforward U.ι).mapIso
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app F) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardInvIsoPullback eZ.symm).app
        ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj F) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackEquivalenceOfIso eZ).counitIso.app F
  exact Module.Finite.equiv (AlgebraicGeometry.sheafCohomology.mapIsoOver A e i)

end
