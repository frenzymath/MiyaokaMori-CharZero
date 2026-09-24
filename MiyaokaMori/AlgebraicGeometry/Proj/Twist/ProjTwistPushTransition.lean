import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistToPushforwardApply

/-! # Transition maps of the twisting sheaves along `Proj.map`

Let `f : 𝒜 → ℬ` be a graded ring homomorphism (with `ℬ₊ ⊆ f(𝒜₊)ℬ`), `r = Proj.map f : Proj ℬ → Proj 𝒜`, and let
`ι_A : Proj 𝒜 → Y`, `ι_B : Proj ℬ → Y` be morphisms to the same scheme `Y` with `r ≫ ι_A = ι_B`. The transition map
`T(f) : (ι_A)_* O_{Proj 𝒜}(n) → (ι_B)_* O_{Proj ℬ}(n)` is `(ι_A)_*(θ_f) ≫ pushforwardComp ≫ pushforwardCongr`, where
`θ_f = Proj.twistToPushforward`. Then
1. pointwise formula: `T(f)(s)(y) = (A_{f⁻¹y} → B_y)(s(f⁻¹y))`;
2. unit law: if `f` is the identity as a ring homomorphism, then `T(f) = 𝟙`;
3. transitivity (Stacks 01NP): if `χ = ψ ∘ φ` as ring homomorphisms, then `T(χ) = T(φ) ≫ T(ψ)`.

Proof. (1) `pushforwardComp` is the identity on sections and `pushforwardCongr` is restriction along an `eqToHom`
(Mathlib's `pushforwardComp_hom_app_app`, `pushforwardCongr_hom_app_app`, both definitional); the restriction maps
of the twisting sheaf are restrictions of functions (`presheaf_map_apply`); with the pointwise description of `θ`
(`ProjTwistToPushforwardApply`) one gets `T(f)(s)(y) = localRingHom (comap f y) y f rfl (s ⟨comap f y, _⟩)`, all by
`rfl`. (2) Compare open set by open set, section by section, point by point: by (1) the left-hand side at `y` is
`localRingHom (comap f y) y f _ (s(comap f y))`; for `f = id`, `comap f y = y` (`Ideal.comap_id`) and
`Localization.localRingHom_id` gives `s(y)`; the dependent types are handled by first substituting the equality of
points and of ring homomorphisms. (3) Pointwise, the left-hand side is `localRingHom (comap χ y) y χ (s(comap χ y))`
and the right-hand side is
`localRingHom (comap ψ y) y ψ (localRingHom (comap φ (comap ψ y)) (comap ψ y) φ (s(comap φ (comap ψ y))))`; from
`χ = ψ∘φ` one gets `comap χ y = comap φ (comap ψ y)` (`Ideal.comap_comap`), then `Localization.localRingHom_comp`.

Sources: Stacks 01NP (transitivity); Stacks 01MX (pointwise description of `θ`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The transition map `T(f) : (ι_A)_* O_{Proj 𝒜}(n) → (ι_B)_* O_{Proj ℬ}(n)`. -/
def twistPushTransition (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (w : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB) :
    (AlgebraicGeometry.Scheme.Modules.pushforward ιA).obj (AlgebraicGeometry.Proj.twist 𝒜 n) ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward ιB).obj (AlgebraicGeometry.Proj.twist ℬ n) :=
  (AlgebraicGeometry.Scheme.Modules.pushforward ιA).map (AlgebraicGeometry.Proj.twistToPushforward f hf n) ≫
  (AlgebraicGeometry.Scheme.Modules.pushforwardComp (AlgebraicGeometry.Proj.map f hf) ιA).hom.app _ ≫
  (AlgebraicGeometry.Scheme.Modules.pushforwardCongr w).hom.app _

theorem twistPushTransition_app_apply (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (w : AlgebraicGeometry.Proj.map f hf ≫ ιA = ιB)
    (U : Y.Opens)
    (s : MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule 𝒜 n (ιA ⁻¹ᵁ U))
    (y : (ιB ⁻¹ᵁ U : (AlgebraicGeometry.Proj ℬ).Opens))
    (hy : ProjectiveSpectrum.comap f hf y.1 ∈ (ιA ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒜).Opens)) :
    haveI := y.1.isPrime
    haveI := (ProjectiveSpectrum.comap f hf y.1).isPrime
    (show MiyaokaMori.WeightedJets.ProjTwisting.sectionsSubmodule ℬ n (ιB ⁻¹ᵁ U) from
      ((twistPushTransition f hf n ιA ιB w).app U).hom s).1 y =
      Localization.localRingHom (ProjectiveSpectrum.comap f hf y.1).asHomogeneousIdeal.toIdeal
        y.1.asHomogeneousIdeal.toIdeal (f : A →+* B) rfl
        (s.1 ⟨ProjectiveSpectrum.comap f hf y.1, hy⟩) := by
  subst w
  rfl

private lemma localRingHom_family_id (V : Set (ProjectiveSpectrum 𝒜))
    (s : ∀ x : V, MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x.1)
    (x y : ProjectiveSpectrum 𝒜) (hx : x ∈ V) (hy : y ∈ V) (hxy : x = y)
    (g : A →+* A) (hg : g = RingHom.id A)
    (h : x.asHomogeneousIdeal.toIdeal = y.asHomogeneousIdeal.toIdeal.comap g) :
    Localization.localRingHom x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal g h
      (s ⟨x, hx⟩) = s ⟨y, hy⟩ := by
  subst hxy; subst hg
  exact DFunLike.congr_fun (Localization.localRingHom_id x.asHomogeneousIdeal.toIdeal) (s ⟨x, hx⟩)

/-- Unit law: if `f` is the identity as a ring homomorphism, then `T(f) = 𝟙`. -/
theorem twistPushTransition_id (f : 𝒜 →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    (hid : (f : A →+* A) = RingHom.id A)
    {Y : AlgebraicGeometry.Scheme.{u}} (ι : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (w : AlgebraicGeometry.Proj.map f hf ≫ ι = ι) :
    twistPushTransition f hf n ι ι w = 𝟙 _ := by
  have hpt : ∀ y : ProjectiveSpectrum 𝒜, ProjectiveSpectrum.comap f hf y = y := fun y => by
    refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_)
    show Ideal.comap (f : A →+* A) _ = _
    rw [hid, Ideal.comap_id]
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine Subtype.ext (funext fun y => ?_)
  have hy : ProjectiveSpectrum.comap f hf y.1 ∈ (ι ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒜).Opens) := by
    have := y.2; rwa [← hpt y.1] at this
  refine (twistPushTransition_app_apply f hf n ι ι w U s y hy).trans ?_
  exact localRingHom_family_id _ _ _ _ hy y.2 (hpt y.1) _ hid _

variable {ρ C : Type u} [CommRing C] [SetLike ρ C] [AddSubgroupClass ρ C] {𝒞 : ℕ → ρ} [GradedRing 𝒞]

private lemma localRingHom_family_comp (V : Set (ProjectiveSpectrum 𝒜))
    (s : ∀ x : V, MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x.1)
    (x₁ x₂ : ProjectiveSpectrum 𝒜) (h₁ : x₁ ∈ V) (h₂ : x₂ ∈ V) (h12 : x₁ = x₂)
    (yB : ProjectiveSpectrum ℬ) (zC : ProjectiveSpectrum 𝒞)
    (φ : A →+* B) (ψ : B →+* C) (g : A →+* C) (hg : g = ψ.comp φ)
    (hx₁ : x₁.asHomogeneousIdeal.toIdeal = zC.asHomogeneousIdeal.toIdeal.comap g)
    (hx₂ : x₂.asHomogeneousIdeal.toIdeal = yB.asHomogeneousIdeal.toIdeal.comap φ) (hJ : yB.asHomogeneousIdeal.toIdeal = zC.asHomogeneousIdeal.toIdeal.comap ψ) :
    Localization.localRingHom x₁.asHomogeneousIdeal.toIdeal zC.asHomogeneousIdeal.toIdeal g hx₁ (s ⟨x₁, h₁⟩) =
      Localization.localRingHom yB.asHomogeneousIdeal.toIdeal zC.asHomogeneousIdeal.toIdeal ψ hJ
        (Localization.localRingHom x₂.asHomogeneousIdeal.toIdeal yB.asHomogeneousIdeal.toIdeal φ hx₂ (s ⟨x₂, h₂⟩)) := by
  subst h12; subst hg
  exact DFunLike.congr_fun
    (Localization.localRingHom_comp (I := x₁.asHomogeneousIdeal.toIdeal)
      yB.asHomogeneousIdeal.toIdeal zC.asHomogeneousIdeal.toIdeal φ hx₂ ψ hJ) (s ⟨x₁, h₁⟩)

/-- Transitivity (Stacks 01NP): if `χ = ψ ∘ φ` as ring homomorphisms, then `T(χ) = T(φ) ≫ T(ψ)`. -/
theorem twistPushTransition_comp (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) (χ : 𝒜 →+*ᵍ 𝒞)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hψ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map ψ)
    (hχ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map χ) (n : ℤ)
    (hcomp : (χ : A →+* C) = (ψ : B →+* C).comp (φ : A →+* B))
    {Y : AlgebraicGeometry.Scheme.{u}} (ιA : AlgebraicGeometry.Proj 𝒜 ⟶ Y)
    (ιB : AlgebraicGeometry.Proj ℬ ⟶ Y) (ιC : AlgebraicGeometry.Proj 𝒞 ⟶ Y)
    (wφ : AlgebraicGeometry.Proj.map φ hφ ≫ ιA = ιB)
    (wψ : AlgebraicGeometry.Proj.map ψ hψ ≫ ιB = ιC)
    (wχ : AlgebraicGeometry.Proj.map χ hχ ≫ ιA = ιC) :
    twistPushTransition χ hχ n ιA ιC wχ =
      twistPushTransition φ hφ n ιA ιB wφ ≫ twistPushTransition ψ hψ n ιB ιC wψ := by
  have hpt : ∀ z : ProjectiveSpectrum 𝒞, ProjectiveSpectrum.comap χ hχ z =
      ProjectiveSpectrum.comap φ hφ (ProjectiveSpectrum.comap ψ hψ z) := fun z => by
    refine ProjectiveSpectrum.ext (HomogeneousIdeal.toIdeal_injective ?_)
    show Ideal.comap (χ : A →+* C) _ = Ideal.comap (φ : A →+* B) (Ideal.comap (ψ : B →+* C) _)
    rw [hcomp, Ideal.comap_comap]
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  refine Subtype.ext (funext fun z => ?_)
  have hB : ProjectiveSpectrum.comap ψ hψ z.1 ∈ (ιB ⁻¹ᵁ U : (AlgebraicGeometry.Proj ℬ).Opens) := by
    subst wψ; exact z.2
  have hA : ProjectiveSpectrum.comap φ hφ (ProjectiveSpectrum.comap ψ hψ z.1) ∈
      (ιA ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒜).Opens) := by
    subst wφ; exact hB
  have hA' : ProjectiveSpectrum.comap χ hχ z.1 ∈ (ιA ⁻¹ᵁ U : (AlgebraicGeometry.Proj 𝒜).Opens) := by
    have := hA; rwa [← hpt z.1] at this
  refine (twistPushTransition_app_apply χ hχ n ιA ιC wχ U s z hA').trans ?_
  refine Eq.trans ?_ (twistPushTransition_app_apply ψ hψ n ιB ιC wψ U
    (((twistPushTransition φ hφ n ιA ιB wφ).app U).hom s) z hB).symm
  refine Eq.trans ?_ (congrArg _
    (twistPushTransition_app_apply φ hφ n ιA ιB wφ U s ⟨_, hB⟩ hA).symm)
  exact localRingHom_family_comp _ _ _ _ hA' hA (hpt z.1) (ProjectiveSpectrum.comap ψ hψ z.1) z.1
    _ _ _ hcomp rfl rfl rfl

/-! ### Recognition forms

Downstream (on the relative Proj), `Proj 𝒜` appears as `F.obj i`, `Proj.map f` as `F.map h`, and `θ_f` as "adjunction
unit ≫ pushforward of the comparison isomorphism"; these are only definitionally equal to the spellings used here, and
the kernel is slow at checking such definitional equalities on large terms (over 20 s). The two lemmas below restate
the unit law and transitivity for an arbitrary scheme `P`, module `M` and morphisms `r`, `t` which are (heterogeneously)
equal to `Proj 𝒜`, `O(n)`, `Proj.map f`, `θ_f`, so that the downstream goal is syntactically the conclusion of the lemma
and the kernel only checks a few small equalities. -/

/-- Recognition form of the unit law. -/
theorem twistPushTransition_id_of_heq (f : 𝒜 →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) (n : ℤ)
    (hid : (f : A →+* A) = RingHom.id A)
    {P Y : AlgebraicGeometry.Scheme.{u}} (M : P.Modules) (ι : P ⟶ Y) (r : P ⟶ P) (w : r ≫ ι = ι)
    (t : M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward r).obj M)
    (eP : P = AlgebraicGeometry.Proj 𝒜) (hM : HEq M (AlgebraicGeometry.Proj.twist 𝒜 n))
    (hr : HEq r (AlgebraicGeometry.Proj.map f hf))
    (ht : HEq t (AlgebraicGeometry.Proj.twistToPushforward f hf n)) :
    (AlgebraicGeometry.Scheme.Modules.pushforward ι).map t ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp r ι).hom.app M ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr w).hom.app M = 𝟙 _ := by
  subst eP
  obtain rfl := eq_of_heq hM
  obtain rfl := eq_of_heq hr
  obtain rfl := eq_of_heq ht
  exact twistPushTransition_id f hf n hid ι w

/-- Recognition form of transitivity. -/
theorem twistPushTransition_comp_of_heq (φ : 𝒜 →+*ᵍ ℬ) (ψ : ℬ →+*ᵍ 𝒞) (χ : 𝒜 →+*ᵍ 𝒞)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    (hψ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map ψ)
    (hχ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒜).map χ) (n : ℤ)
    (hcomp : (χ : A →+* C) = (ψ : B →+* C).comp (φ : A →+* B))
    {P Q R Y : AlgebraicGeometry.Scheme.{u}} (MP : P.Modules) (MQ : Q.Modules) (MR : R.Modules)
    (ιP : P ⟶ Y) (ιQ : Q ⟶ Y) (ιR : R ⟶ Y) (rφ : Q ⟶ P) (rψ : R ⟶ Q) (rχ : R ⟶ P)
    (wφ : rφ ≫ ιP = ιQ) (wψ : rψ ≫ ιQ = ιR) (wχ : rχ ≫ ιP = ιR)
    (tφ : MP ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward rφ).obj MQ)
    (tψ : MQ ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward rψ).obj MR)
    (tχ : MP ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward rχ).obj MR)
    (eP : P = AlgebraicGeometry.Proj 𝒜) (eQ : Q = AlgebraicGeometry.Proj ℬ)
    (eR : R = AlgebraicGeometry.Proj 𝒞)
    (hMP : HEq MP (AlgebraicGeometry.Proj.twist 𝒜 n)) (hMQ : HEq MQ (AlgebraicGeometry.Proj.twist ℬ n))
    (hMR : HEq MR (AlgebraicGeometry.Proj.twist 𝒞 n))
    (hrφ : HEq rφ (AlgebraicGeometry.Proj.map φ hφ)) (hrψ : HEq rψ (AlgebraicGeometry.Proj.map ψ hψ))
    (hrχ : HEq rχ (AlgebraicGeometry.Proj.map χ hχ))
    (htφ : HEq tφ (AlgebraicGeometry.Proj.twistToPushforward φ hφ n))
    (htψ : HEq tψ (AlgebraicGeometry.Proj.twistToPushforward ψ hψ n))
    (htχ : HEq tχ (AlgebraicGeometry.Proj.twistToPushforward χ hχ n)) :
    (AlgebraicGeometry.Scheme.Modules.pushforward ιP).map tχ ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp rχ ιP).hom.app MR ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr wχ).hom.app MR =
    ((AlgebraicGeometry.Scheme.Modules.pushforward ιP).map tφ ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp rφ ιP).hom.app MQ ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr wφ).hom.app MQ) ≫
    ((AlgebraicGeometry.Scheme.Modules.pushforward ιQ).map tψ ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp rψ ιQ).hom.app MR ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr wψ).hom.app MR) := by
  subst eP; subst eQ; subst eR
  obtain rfl := eq_of_heq hMP
  obtain rfl := eq_of_heq hMQ
  obtain rfl := eq_of_heq hMR
  obtain rfl := eq_of_heq hrφ
  obtain rfl := eq_of_heq hrψ
  obtain rfl := eq_of_heq hrχ
  obtain rfl := eq_of_heq htφ
  obtain rfl := eq_of_heq htψ
  obtain rfl := eq_of_heq htχ
  exact twistPushTransition_comp φ ψ χ hφ hψ hχ n hcomp ιP ιQ ιR wφ wψ wχ

end AlgebraicGeometry.Proj

end
