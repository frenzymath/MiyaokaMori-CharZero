import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.VeroneseTwistPullbackTwistToPushforwardIso
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistToPushforwardApply

/-! # Pointwise formula for the inverse of the twist comparison map of a graded isomorphism

Pointwise formula for the **inverse** of the comparison morphism `θ_f = Proj.twistToPushforward f hf n :
O_{Proj 𝒜}(n) ⟶ (Proj.map f)_* O_{Proj ℬ}(n)` when the graded homomorphism `f : 𝒜 →+*ᵍ ℬ` has a graded inverse `g`
(`VeroneseTwistPullbackTwistToPushforwardIso` gives `IsIso θ_f`): for a section `σ` of `(Proj.map f)_* O_ℬ(n)` over `U`
(a function on `Proj.map f ⁻¹ U ⊆ Proj ℬ`) and `x ∈ U`,
`(θ_f⁻¹ σ)(x) = (B_{g⁻¹x} → A_x)(σ(g⁻¹ x))` — the fibre map `Localization.localRingHom` along `g`
(`b/t ↦ g(b)/g(t)`).

Proof: `r₀ := Proj.twistComapFun g hg … σ` is a section of `O_𝒜(n)` over `U` (`twistComapFun_isLocallyFraction`), and
`θ_f r₀ = σ` pointwise: `(θ_f r₀)(p) = localRingHom_f (r₀ (f⁻¹ p)) = localRingHom_f (localRingHom_g (σ (g⁻¹ f⁻¹ p)))`, and
`g⁻¹ f⁻¹ p = p` (`f ∘ g = id`, `Ideal.comap_comap`), `localRingHom_f ∘ localRingHom_g = localRingHom_{f ∘ g} = id`
(`Localization.localRingHom_comp`, `localRingHom_id`). Hence `θ_f⁻¹ σ = θ_f⁻¹ (θ_f r₀) = r₀`.

Source: Stacks 01MX (θ). Used for the naturality step of `VeroneseTwistPullback`
(`twistPushforwardOfVeroneseIso = (asIso θ_{ofVeronese}).symm`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- `f⁻¹ (g⁻¹ x) = x` on `Proj 𝒜` when `g ∘ f = id` as graded ring homomorphisms. -/
theorem comap_comap_eq_self_of_comp_eq_id (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = GradedRingHom.id 𝒜) (x : ProjectiveSpectrum 𝒜) :
    ProjectiveSpectrum.comap f hf (ProjectiveSpectrum.comap g hg x) = x := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_)
  have hcomp : (g : B →+* A).comp (f : A →+* B) = RingHom.id A := by
    rw [show (g : B →+* A).comp (f : A →+* B) = ((g.comp f : 𝒜 →+*ᵍ 𝒜) : A →+* A) from rfl, hgf]
    rfl
  show Ideal.comap (f : A →+* B) (Ideal.comap (g : B →+* A) x.asHomogeneousIdeal.toIdeal) =
    x.asHomogeneousIdeal.toIdeal
  rw [Ideal.comap_comap, hcomp, Ideal.comap_id]

/-- Membership transported along an equality of points. -/
theorem mem_opens_of_eq {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opens) {a b : X} (h : a = b) (hb : b ∈ U) :
    a ∈ U := h ▸ hb

/-- Transport lemma: `localRingHom_f (localRingHom_g z) = z` when `f ∘ g = id`, for a point-indexed family. -/
private theorem localRingHom_localRingHom_eq_self {V : Set (ProjectiveSpectrum ℬ)}
    (s : ∀ x : V, MiyaokaMori.WeightedJets.ProjTwisting.Fiber ℬ x.1)
    (p p' : ProjectiveSpectrum ℬ) (hp : p ∈ V) (hp' : p' ∈ V) (hpp' : p' = p) (q : ProjectiveSpectrum 𝒜)
    (φ : A →+* B) (ψ : B →+* A) (hφψ : φ.comp ψ = RingHom.id B)
    (hq : q.asHomogeneousIdeal.toIdeal = p.asHomogeneousIdeal.toIdeal.comap φ)
    (hp'q : p'.asHomogeneousIdeal.toIdeal = q.asHomogeneousIdeal.toIdeal.comap ψ) :
    Localization.localRingHom q.asHomogeneousIdeal.toIdeal p.asHomogeneousIdeal.toIdeal φ hq
      (Localization.localRingHom p'.asHomogeneousIdeal.toIdeal q.asHomogeneousIdeal.toIdeal ψ hp'q (s ⟨p', hp'⟩)) =
    s ⟨p, hp⟩ := by
  subst hpp'
  rw [← RingHom.comp_apply, ← Localization.localRingHom_comp (I := p'.asHomogeneousIdeal.toIdeal)
    q.asHomogeneousIdeal.toIdeal p'.asHomogeneousIdeal.toIdeal ψ hp'q φ hq]
  have hcomp : Localization.localRingHom p'.asHomogeneousIdeal.toIdeal p'.asHomogeneousIdeal.toIdeal (φ.comp ψ)
      (by rw [← Ideal.comap_comap, ← hq, ← hp'q]) = RingHom.id _ := by
    refine Localization.localRingHom_unique _ _ _ _ fun r => ?_
    rw [hφψ]
    rfl
  rw [hcomp]
  rfl

/-- **Pointwise formula for `θ_f⁻¹`** (`f` with graded inverse `g`): `(θ_f⁻¹ σ)(x) = localRingHom_g (σ (g⁻¹ x))`. -/
theorem inv_twistToPushforward_app_apply (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = GradedRingHom.id 𝒜) (hfg : f.comp g = GradedRingHom.id ℬ) (n : ℤ)
    [IsIso (AlgebraicGeometry.Proj.twistToPushforward f hf n)]
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (σ : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ n ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U))
    (x : U) :
    haveI := x.1.isPrime
    haveI := (ProjectiveSpectrum.comap g hg x.1).isPrime
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n U from
      ((inv (AlgebraicGeometry.Proj.twistToPushforward f hf n)).app U).hom σ).1 x =
      Localization.localRingHom (ProjectiveSpectrum.comap g hg x.1).asHomogeneousIdeal.toIdeal
        x.1.asHomogeneousIdeal.toIdeal (g : B →+* A) rfl
        (σ.1 ⟨ProjectiveSpectrum.comap g hg x.1,
          mem_opens_of_eq U (comap_comap_eq_self_of_comp_eq_id f g hf hg hgf x.1) x.2⟩) := by
  have hUV : U.1 ⊆ ProjectiveSpectrum.comap g hg ⁻¹' ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U).1 := by
    intro y hy
    exact mem_opens_of_eq U (comap_comap_eq_self_of_comp_eq_id f g hf hg hgf y) hy
  -- the candidate preimage
  let r₀ : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n U :=
    ⟨AlgebraicGeometry.Proj.twistComapFun g hg ((AlgebraicGeometry.Proj.map f hf) ⁻¹ᵁ U) U hUV σ.1,
      AlgebraicGeometry.Proj.twistComapFun_isLocallyFraction g hg n _ U hUV σ.1 σ.2⟩
  have hcomp : (f : A →+* B).comp (g : B →+* A) = RingHom.id B := by
    rw [show (f : A →+* B).comp (g : B →+* A) = ((f.comp g : ℬ →+*ᵍ ℬ) : B →+* B) from rfl, hfg]
    rfl
  have h1 : ((AlgebraicGeometry.Proj.twistToPushforward f hf n).app U).hom r₀ = σ := by
    refine Subtype.ext (funext fun p => ?_)
    refine (AlgebraicGeometry.Proj.twistToPushforward_app_apply f hf n U r₀ p).trans ?_
    exact localRingHom_localRingHom_eq_self σ.1 p.1
      (ProjectiveSpectrum.comap g hg (ProjectiveSpectrum.comap f hf p.1)) p.2 (hUV p.2)
      (comap_comap_eq_self_of_comp_eq_id g f hg hf hfg p.1)
      (ProjectiveSpectrum.comap f hf p.1) (f : A →+* B) (g : B →+* A) hcomp rfl rfl
  have h2 : ((inv (AlgebraicGeometry.Proj.twistToPushforward f hf n)).app U).hom σ = r₀ := by
    rw [← h1]
    change (((AlgebraicGeometry.Proj.twistToPushforward f hf n) ≫
      inv (AlgebraicGeometry.Proj.twistToPushforward f hf n)).app U).hom r₀ = r₀
    rw [IsIso.hom_inv_id]
    rfl
  exact congrArg (fun t : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n U => t.1 x) h2

end AlgebraicGeometry.Proj

end
