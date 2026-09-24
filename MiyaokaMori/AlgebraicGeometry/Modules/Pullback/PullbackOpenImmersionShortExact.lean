import MiyaokaMori.Prelude

/-! # Pullback along an open immersion preserves short exact sequences

If `g : Y ⟶ X` is an open immersion of schemes and `S` is a short exact sequence of
`O_X`-modules, then `g^*S` (termwise pullback along `g`) is a short exact sequence of
`O_Y`-modules; in particular `g^*` preserves monomorphisms.

Proof. (Monomorphisms) On sections, `Scheme.Modules.restrictFunctor g` is
`Γ(M.restrict g, U) = Γ(M, g(U))`, and the restriction of a morphism `φ` has components the
components of `φ` on `g(U)`. A monomorphism of sheaves of modules is a monomorphism of the
underlying presheaves of abelian groups (`toPresheaf` preserves limits), hence componentwise
injective (`NatTrans.mono_iff_mono_app`); so its restriction is componentwise injective, hence a
monomorphism of presheaves, hence of sheaves of modules (`toPresheaf` is faithful and reflects
monomorphisms). The natural isomorphism `restrictFunctorIsoPullback g` transfers this to `g^*φ`.
(Right exactness) `g^*` is a left adjoint (`pullbackPushforwardAdjunction`), so it preserves
cokernels and epimorphisms; hence `g^*S` is exact in the middle
(`ShortComplex.Exact.map_of_epi_of_preservesCokernel`). Combining both gives short exactness.

Reference: Stacks 01AJ (restriction to an open is exact).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- Restriction to an open subscheme preserves monomorphisms of sheaves of modules. -/
theorem AlgebraicGeometry.Scheme.Modules.mono_restrictFunctor_map {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion g] {M N : X.Modules} (φ : M ⟶ N) [Mono φ] :
    Mono ((AlgebraicGeometry.Scheme.Modules.restrictFunctor g).map φ) := by
  apply (Scheme.Modules.toPresheaf Y).mono_of_mono_map
  have h : Mono ((Scheme.Modules.toPresheaf X).map φ) := inferInstance
  rw [NatTrans.mono_iff_mono_app] at h ⊢
  intro U
  exact h (op (g ''ᵁ U.unop))

/-- Pullback along an open immersion preserves monomorphisms of sheaves of modules. -/
theorem AlgebraicGeometry.Scheme.Modules.mono_pullback_map_of_isOpenImmersion
    {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion g] {M N : X.Modules} (φ : M ⟶ N) [Mono φ] :
    Mono ((AlgebraicGeometry.Scheme.Modules.pullback g).map φ) := by
  have h1 := Scheme.Modules.mono_restrictFunctor_map g φ
  have h2 : (Scheme.Modules.pullback g).map φ =
      (Scheme.Modules.restrictFunctorIsoPullback g).inv.app M ≫
        (Scheme.Modules.restrictFunctor g).map φ ≫
        (Scheme.Modules.restrictFunctorIsoPullback g).hom.app N := by
    rw [(Scheme.Modules.restrictFunctorIsoPullback g).hom.naturality φ,
      Iso.inv_hom_id_app_assoc]
  rw [h2]
  have h3 : Mono ((Scheme.Modules.restrictFunctorIsoPullback g).hom.app N) :=
    @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_hom ((Scheme.Modules.restrictFunctorIsoPullback g).app N))
  have h4 : Mono ((Scheme.Modules.restrictFunctorIsoPullback g).inv.app M) :=
    @IsIso.mono_of_iso _ _ _ _ _ (Iso.isIso_inv ((Scheme.Modules.restrictFunctorIsoPullback g).app M))
  have h5 := @mono_comp _ _ _ _ _ _ h1 _ h3
  exact @mono_comp _ _ _ _ _ _ h4 _ h5

/-- Pullback along an open immersion preserves short exact sequences of sheaves of modules. -/
theorem AlgebraicGeometry.Scheme.Modules.shortExact_map_pullback_of_isOpenImmersion
    {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion g] {S : CategoryTheory.ShortComplex X.Modules}
    (hS : S.ShortExact) :
    (S.map (AlgebraicGeometry.Scheme.Modules.pullback g)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  have hmono : Mono ((Scheme.Modules.pullback g).map S.f) :=
    Scheme.Modules.mono_pullback_map_of_isOpenImmersion g S.f
  have hepi : Epi ((Scheme.Modules.pullback g).map S.g) :=
    (Scheme.Modules.pullback g).map_epi S.g
  have hex : (S.map (Scheme.Modules.pullback g)).Exact :=
    hS.exact.map_of_epi_of_preservesCokernel (Scheme.Modules.pullback g) hS.epi_g inferInstance
  exact { exact := hex, mono_f := hmono, epi_g := hepi }

end
