import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf

/-! # The comparison morphism `θ` of Stacks 01MX

The comparison morphism `θ` of Stacks 01MX: a graded ring homomorphism `f : 𝒜 → ℬ` with
`ℬ₊ ⊆ √(f 𝒜₊)` induces `Proj.map f hf : Proj ℬ → Proj 𝒜`, and pointwise the map
`A_(x) → B_(y)` (`x = f⁻¹y`) sends a homogeneous fraction `a/s` of degree `n` to `f(a)/f(s)`.
This gives `O_{Proj 𝒜}(n) → (Proj.map)_* O_{Proj ℬ}(n)` and, by adjunction,
`θ : (Proj.map)^* O(n) → O(n)`. It provides the data for the comparison isomorphisms of
twisting sheaves in Stacks 01N2 and 01NO.

Sources: Stacks 01MX (the `θ` of the lemma on morphisms of Proj); Mathlib's
`comapStructureSheafFun` in `AlgebraicGeometry/ProjectiveSpectrum/Functor.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The fibre map: for `y ∈ Proj ℬ` and `x = comap f y` (Mathlib's `ProjectiveSpectrum.comap`),
the map `A_{(x)} → B_{(y)}` is `Localization.localRingHom`; it sends a homogeneous fraction `a/s`
of degree `n` of `𝒜` to `f(a)/f(s)` (the same formula as Mathlib's `Proj.comapStructureSheafFun`,
with the fibres of `O(n)` in place of the structure sheaf). -/
noncomputable def AlgebraicGeometry.Proj.twistComapFun {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s : ∀ x : U, MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x.1) (y : V) :
    MiyaokaMori.WeightedJets.ProjTwisting.Fiber ℬ y.1 :=
  haveI := y.1.isPrime
  haveI := (ProjectiveSpectrum.comap f hf y.1).isPrime
  Localization.localRingHom (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
    y.1.asHomogeneousIdeal.toIdeal (f : A →+* B) rfl
    (s ⟨ProjectiveSpectrum.comap f hf y.1, hUV y.2⟩)

/-- `θ` preserves "locally a homogeneous fraction of degree `n`": if `s` is locally `a/s₀` on `U`
(`a ∈ 𝒜ᵢ`, `s₀ ∈ 𝒜ⱼ`, `i = j + n`), then the image under `twistComapFun` is locally
`f(a)/f(s₀)` on `V`; since `f` is a graded ring homomorphism, `f(a) ∈ ℬᵢ` and `f(s₀) ∈ ℬⱼ`, and
`s₀ ∉ (comap f hf y).asHomogeneousIdeal` is equivalent to `f(s₀) ∉ y.asHomogeneousIdeal`.

Proof sketch (as for Mathlib's `ProjectiveSpectrum.Proj.isLocallyFraction_comapStructureSheafFun`):
1. Unfold `hs : (locallyFraction 𝒜 n).pred s` via `PrelocalPredicate.sheafify`: for each `y ∈ V`
   take an open neighbourhood `W ⊆ U` of `x = comap f hf y` and a representation
   `(i, j, a, b, hij, hb, hrep)` of `IsFraction 𝒜 n`.
2. Take the open neighbourhood `(ProjectiveSpectrum.comap f hf) ⁻¹' W ∩ V` of `y` (`comap` is
   continuous).
3. On it give a representation of `IsFraction ℬ n`: `i`, `j` unchanged, `a' := f a` (`f a ∈ ℬ i`
   by `GradedRingHom.map_mem`), `b' := f b`; the denominator does not vanish because
   `b ∉ (comap f hf y).asHomogeneousIdeal` means `f b ∉ y.asHomogeneousIdeal` by definition of
   `ProjectiveSpectrum.comap`.
4. Pointwise, `Localization.localRingHom … (Localization.mk a ⟨b, _⟩) = Localization.mk (f a) ⟨f b, _⟩`
   is Mathlib's `Localization.localRingHom_mk`.
5. The zero-section branch of `IsFraction` (`s = 0`) is `map_zero`. -/
theorem AlgebraicGeometry.Proj.twistComapFun_isLocallyFraction {σ τ A B : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (n : ℤ) (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s : ∀ x : U, MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x.1)
    (hs : (MiyaokaMori.WeightedJets.ProjTwisting.locallyFraction 𝒜 n).pred s) :
    (MiyaokaMori.WeightedJets.ProjTwisting.locallyFraction ℬ n).pred
      (AlgebraicGeometry.Proj.twistComapFun f hf U V hUV s) := by
  intro y
  obtain ⟨W, hmW, iWU, hfrac⟩ := hs ⟨ProjectiveSpectrum.comap f hf y.1, hUV y.2⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨hmW, y.2⟩, Opens.infLERight _ _, ?_⟩
  rcases hfrac with h0 | ⟨i, j, a, b, hij, hb, hrep⟩
  · refine Or.inl (funext fun q => ?_)
    obtain ⟨q, hqW, hqV⟩ := q
    have hq : s ⟨ProjectiveSpectrum.comap f hf q, hUV hqV⟩ = 0 := congrFun h0 ⟨_, hqW⟩
    simp [AlgebraicGeometry.Proj.twistComapFun, hq]
  · refine Or.inr ⟨i, j, f.gradedAddHom i a, f.gradedAddHom j b, hij,
      fun q => hb ⟨_, q.2.1⟩, fun q => ?_⟩
    obtain ⟨q, hqW, hqV⟩ := q
    have hq : s ⟨ProjectiveSpectrum.comap f hf q, hUV hqV⟩ =
        Localization.mk a.1 ⟨b.1, hb ⟨_, hqW⟩⟩ := hrep ⟨_, hqW⟩
    simp [AlgebraicGeometry.Proj.twistComapFun, hq]

/-- `O_{Proj 𝒜}(n) → (Proj.map f hf)_* O_{Proj ℬ}(n)`: on each open set, transport the locally
fractional sections along `twistComapFun`. The image is again locally a fraction of degree `n`
(`twistComapFun_isLocallyFraction`), and the map is linear over the structure sheaf. -/
noncomputable def AlgebraicGeometry.Proj.twistToPushforward {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ) :
    AlgebraicGeometry.Proj.twist 𝒜 n ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map f hf)).obj
        (AlgebraicGeometry.Proj.twist ℬ n) where
  val :=
    { app U := ModuleCat.ofHom (X := (AlgebraicGeometry.Proj.twist 𝒜 n).val.obj U)
        (Y := ((AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Proj.map f hf)).obj
          (AlgebraicGeometry.Proj.twist ℬ n)).val.obj U)
        { toFun s := (⟨AlgebraicGeometry.Proj.twistComapFun f hf U.unop _ (fun _ h ↦ h)
              (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n U.unop from s).1,
              AlgebraicGeometry.Proj.twistComapFun_isLocallyFraction f hf n U.unop _ _ _
                (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n U.unop from s).2⟩ :
            MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ n
              ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U.unop))
          map_add' := fun a b ↦ Subtype.ext (funext fun y ↦ map_add _ _ _)
          map_smul' := fun r a ↦ Subtype.ext (funext fun y ↦ by
            have := y.1.isPrime
            have := (ProjectiveSpectrum.comap f hf y.1).isPrime
            refine (map_mul _ _ _).trans ?_
            refine congrArg₂ (· * ·) ?_ rfl
            exact (HomogeneousLocalization.val_localRingHom _).symm) }
      naturality := fun _ ↦ rfl }

/-- The comparison morphism `θ : (Proj.map f hf)^* O_{Proj 𝒜}(n) → O_{Proj ℬ}(n)` obtained by
adjunction (the `θ` of Stacks 01MX). -/
noncomputable def AlgebraicGeometry.Proj.twistPullbackHom {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ) :
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.map f hf)).obj
        (AlgebraicGeometry.Proj.twist 𝒜 n) ⟶ AlgebraicGeometry.Proj.twist ℬ n :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (AlgebraicGeometry.Proj.map f hf)).homEquiv _ _).symm
    (AlgebraicGeometry.Proj.twistToPushforward f hf n)

end
