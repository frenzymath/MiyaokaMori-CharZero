import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus

/-! # The nonvanishing locus is invariant under isomorphisms

Statement: the nonvanishing locus of a line bundle depends only on the isomorphism class of the pair
"line bundle + section": if `e : L ≅ L'` is an isomorphism of `O_X`-modules and `s ∈ Γ(L, ⊤)`, then
`X_{e(s)} = X_s` (as opens of `X`).

Proof:
1. By the description `mem_nonvanishingLocus`, it suffices to show for every `x`: the germ of `e(s)` at `x`
   lies in `𝔪_x·(L'_x)` ⟺ the germ of `s` at `x` lies in `𝔪_x·(L_x)`.
2. Morphisms of modules commute with germs (`moduleStalkMap_germ`):
   `germ_x(e.hom_⊤ s) = (moduleStalkMap x e.hom)(germ_x s)`.
3. `moduleStalkMap x (-)` is the action on morphisms of the functor `moduleStalkFunctor X x`, so it sends
   the isomorphism `e` to an isomorphism `φ := (moduleStalkFunctor X x).mapIso e` of `O_{X,x}`-modules, in
   particular an `O_{X,x}`-linear bijection.
4. An `O_{X,x}`-linear bijection `φ` maps `I•⊤` onto `I•⊤` (`Submodule.map_smul''`, `Submodule.map_top`,
   `LinearMap.range_eq_top`); with injectivity, `φ v ∈ I•⊤ ⟺ v ∈ I•⊤`. Take `I = 𝔪_x`.
5. The two opens have the same underlying sets, hence are equal by `TopologicalSpace.Opens.ext`.

Reference: the definition of `X_s` in Stacks 01CY (which manifestly depends only on the isomorphism class).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A linear bijection maps `I • ⊤` onto `I • ⊤`, so membership is preserved and reflected. -/
theorem Submodule.mem_smul_top_linearEquiv_iff {R : Type*} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M ≃ₗ[R] N) (I : Ideal R) (v : M) :
    f v ∈ I • (⊤ : Submodule R N) ↔ v ∈ I • (⊤ : Submodule R M) := by
  have h : (I • (⊤ : Submodule R M)).map (f : M →ₗ[R] N) = I • (⊤ : Submodule R N) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 f.surjective]
  rw [← h, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hfy⟩
    exact f.injective hfy ▸ hy
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- The `O_{X,x}`-linear isomorphism on stalks induced by an isomorphism of modules. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') (x : X) :
    L.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] L'.presheaf.stalk x :=
  ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor X x).mapIso e).toLinearEquiv

@[simp]
theorem AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso_apply
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') (x : X)
    (v : L.presheaf.stalk x) :
    AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso e x v =
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x e.hom v :=
  rfl

theorem AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} [L.IsLineBundle] [L'.IsLineBundle]
    (e : L ≅ L') (s : Γ(L, ⊤)) (x : X) :
    x ∈ L'.nonvanishingLocus (e.hom.app ⊤ s) ↔ x ∈ L.nonvanishingLocus s := by
  rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus,
    AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
  have hg : L'.presheaf.germ ⊤ x trivial (e.hom.app ⊤ s)
      = AlgebraicGeometry.Scheme.Modules.stalkLinearEquivOfIso e x
        (L.presheaf.germ ⊤ x trivial s) :=
    (AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x e.hom ⊤ trivial s).symm
  rw [hg]
  exact not_congr (Submodule.mem_smul_top_linearEquiv_iff _ _ _)

theorem AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso
    {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules} [L.IsLineBundle] [L'.IsLineBundle]
    (e : L ≅ L') (s : Γ(L, ⊤)) :
    L'.nonvanishingLocus (e.hom.app ⊤ s) = L.nonvanishingLocus s :=
  TopologicalSpace.Opens.ext (Set.ext fun x =>
    AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso e s x)

end
