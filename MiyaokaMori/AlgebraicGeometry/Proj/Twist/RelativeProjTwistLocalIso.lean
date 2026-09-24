import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjMapTwistComparison
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.PullbackStalkOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso

/-! # The transition maps of the relative twisting sheaf are isomorphisms

Statement (Stacks 01MX / 01N2, the case of a degree-0 localization): for `U ≤ V` in the small affine
Zariski site of `X` and `S : X.GradedAffineAlgebra`, the comparison map
`θ : ρ^* O_{Proj S(V)}(m) ⟶ O_{Proj S(U)}(m)` (`Proj.twistPullbackHom`, the adjoint transpose of
`Proj.twistToPushforward`) along `ρ := Proj.map (S.restrictGraded h) : Proj S(U) ⟶ Proj S(V)` is an isomorphism.

This is the "transition maps are isomorphisms" input of the gluing of `O(m)` on the relative Proj
(Stacks 01LI); see `RelativeProjTwistPiApp`.

Proof (self-contained; this is the route actually formalized below). Write `A := S(V)`, `B := S(U)` with
restriction `r := S.restrictGraded h : A →+*ᵍ B`. `U ≤ V` means `U = D_V(f)` for some `f ∈ Γ(X, V)`;
put `f₀ := S.unitHom V f ∈ A_0` (degree 0, `S.unit_mem`). By quasi-coherence
(`AffineAlgebra.isLocalization_basicOpen`) `B = A[1/f₀]` via `r`, and `r` preserves degrees.
1. `ρ` is an open immersion: `ρ ≫ projChart V = projChart U` (`map_projChart`) and both charts are open
   immersions (`IsOpenImmersion.of_comp`). Hence every stalk map `O_{Proj A, ρ y} → O_{Proj B, y}` is an
   isomorphism, so the adjunction unit `u_y : O_A(m)_{ρ y} → (ρ^* O_A(m))_y` is bijective
   (the stalk of a pullback along an open immersion).
2. Stalk criterion: `θ` is an isomorphism iff its stalk maps are bijective
   (`moduleHom_isIso_iff_stalk_bijective`); since `u_y` is bijective it suffices that
   `Ψ_y := θ_y ∘ u_y : O_A(m)_{ρ y} → O_B(m)_y` is bijective. By the adjunction identity
   `φ = unit ≫ ρ_* θ` (`Adjunction.homEquiv_unit`), `Ψ_y` sends the germ of `s ∈ Γ(W, O_A(m))` to the
   germ of `φ_W(s) ∈ Γ(ρ⁻¹W, O_B(m))`, where `φ_W(s)(z) = (A_{(ρ z)} → B_{(z)})(s(ρ z))` is the local ring
   map `Localization.localRingHom` along `r` (`twistToPushforward_app_apply`).
3. Pointwise, `A_{ρ z} → B_z` is a ring isomorphism: `B_z = (A[1/f₀])_z` is the localization of `A` at
   `r⁻¹ z = ρ z` (`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`), so the local
   ring map is the canonical `IsLocalization.algEquiv` (`Localization.localRingHom_unique`).
4. Injectivity of `Ψ_y`: if `φ_{W₁}(s₁)` and `φ_{W₂}(s₂)` agree on a neighbourhood `W'` of `y`, then
   `s₁ = s₂` on the open neighbourhood `ρ(W')` of `ρ y` (pointwise injectivity of step 3), so the
   germs agree (`germ_ext`).
5. Surjectivity of `Ψ_y`: a section `n` of `O_B(m)` near `y` is, near `y`, either `0` or a fraction
   `b/c` with `b ∈ B_p`, `c ∈ B_q`, `p = q + m`, `c ∉ z` for `z ∈ W''`. Since `B = A[1/f₀]` and `r`
   is graded, `b · r(f₀)^k = r(a)` and `c · r(f₀)^k = r(a')` for a common `k` and homogeneous
   `a ∈ A_p`, `a' ∈ A_q` (take degree components of the numerators). Then `a' ∉ ρ z` for `z ∈ W''`
   (`r(a') = c · r(f₀)^k ∉ z`, `z` prime, `r(f₀)` a unit), so `s := a/a'` is a section of `O_A(m)` over
   `ρ(W'')`, and `φ(s)(z) = r(a)/r(a') = b/c = n(z)` on `W''` (`Localization.localRingHom_mk`), i.e.
   `Ψ_y(germ s) = germ n`.

Source: Stacks 01MX (θ), 01N2 (base change), 01NP (transition maps); Lemma 2.2 of the paper.
Edge cases: `U = ∅` (`f = 0`): `B = 0`, `Proj B = ∅`, the stalk criterion is vacuous. `f` a unit:
`ρ` is an isomorphism and `θ` is an isomorphism because the graded ring map is bijective;
the argument above covers this case uniformly.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.RelativeProjTwistLocalIso

open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of the adjoint transpose `θ` of `φ : M ⟶ ρ_* N`, composed with the pullback stalk
unit, sends the germ of `s ∈ Γ(W, M)` to the germ of `φ_W s ∈ Γ(ρ⁻¹W, N)`
(`Adjunction.homEquiv_unit`: `φ = unit ≫ ρ_* θ`). -/
theorem moduleStalkMap_transpose_unit_germ {X Y : Scheme.{u}} (ρ : X ⟶ Y) (M : Y.Modules)
    (N : X.Modules) (φ : M ⟶ (Scheme.Modules.pushforward ρ).obj N) (y : X) (W : Y.Opens)
    (hy : ρ.base y ∈ W) (s : M.val.obj (op W)) :
    AlgebraicGeometry.Scheme.Modules.moduleStalkMap X y
        (((Scheme.Modules.pullbackPushforwardAdjunction ρ).homEquiv M N).symm φ)
        (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ρ M y (M.presheaf.germ W (ρ.base y) hy s)) =
      N.presheaf.germ (ρ ⁻¹ᵁ W) y hy (φ.app W s) := by
  have h1 : AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ρ M y (M.presheaf.germ W (ρ.base y) hy s) =
      ((Scheme.Modules.pullback ρ).obj M).presheaf.germ (ρ ⁻¹ᵁ W) y hy
        (((Scheme.Modules.pullbackPushforwardAdjunction ρ).unit.app M).app W s) :=
    AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ ρ M y W hy s
  rw [h1]
  change (TopCat.Presheaf.stalkFunctor Ab y).map _ _ = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  have h2 := (Scheme.Modules.pullbackPushforwardAdjunction ρ).homEquiv_unit (X := M) (Y := N)
    (f := ((Scheme.Modules.pullbackPushforwardAdjunction ρ).homEquiv M N).symm φ)
  rw [Equiv.apply_symm_apply] at h2
  have h3 := congrArg (fun ψ : M ⟶ (Scheme.Modules.pushforward ρ).obj N => ψ.app W s) h2
  exact congrArg _ h3.symm

/-- `B = A[1/f]` via `φ`, `J` a prime of `B`: the local ring map `A_{φ⁻¹J} → B_J` is a bijection
(`B_J` is the localization of `A` at `φ⁻¹J`, Mathlib
`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`). -/
theorem localRingHom_bijective_of_isLocalizationAway {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) {f : A} (hloc : letI := φ.toAlgebra; IsLocalization.Away f B)
    (J : Ideal B) [J.IsPrime] :
    Function.Bijective (Localization.localRingHom (J.comap φ) J φ rfl) := by
  let _ := φ.toAlgebra
  have : IsLocalization.AtPrime (Localization.AtPrime J) (J.comap (algebraMap A B)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers f)
      (Localization.AtPrime J) J
  let e := IsLocalization.algEquiv (J.comap (algebraMap A B)).primeCompl
    (Localization.AtPrime (J.comap (algebraMap A B))) (Localization.AtPrime J)
  have he : Localization.localRingHom (J.comap φ) J φ rfl = e.toRingEquiv.toRingHom := by
    apply Localization.localRingHom_unique
    intro a
    exact (e.commutes a).trans (IsScalarTower.algebraMap_apply A B (Localization.AtPrime J) a)
  rw [he]
  exact e.toRingEquiv.bijective

section Graded

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) {f : A} (hf : f ∈ 𝒜 0)
  (hloc : letI := φ.toRingHom.toAlgebra; IsLocalization.Away f B)

include hf hloc in
/-- `B = A[1/f]` via the graded `φ`, `f ∈ 𝒜 0`: every homogeneous `b ∈ ℬ i` is `φ a / φ f ^ k` with
`a ∈ 𝒜 i` (take the degree-`i` component of a numerator). -/
theorem exists_map_eq_mul_pow {i : ℕ} {b : B} (hb : b ∈ ℬ i) :
    ∃ (k : ℕ) (a : A), a ∈ 𝒜 i ∧ φ a = b * φ f ^ k := by
  let _ := φ.toRingHom.toAlgebra
  have hφf : φ f ∈ ℬ 0 := φ.map_mem hf
  obtain ⟨m, a', ha'⟩ := IsLocalization.Away.surj (S := B) f b
  have hmem : b * φ f ^ m ∈ ℬ i := by
    have := SetLike.mul_mem_graded hb (SetLike.pow_mem_graded m hφf)
    simpa using this
  refine ⟨m, DirectSum.decompose 𝒜 a' i, SetLike.coe_mem _, ?_⟩
  rw [GradedRingHom.map_directSumDecompose]
  change (DirectSum.decompose ℬ (algebraMap A B a') i : B) = _
  rw [← ha']
  exact DirectSum.decompose_of_mem_same ℬ hmem

include hf hloc in
/-- Common-denominator form of `exists_map_eq_mul_pow` for two homogeneous elements. -/
theorem exists_map_eq_mul_pow₂ {i j : ℕ} {b c : B} (hb : b ∈ ℬ i) (hc : c ∈ ℬ j) :
    ∃ (k : ℕ) (a a' : A), a ∈ 𝒜 i ∧ a' ∈ 𝒜 j ∧ φ a = b * φ f ^ k ∧ φ a' = c * φ f ^ k := by
  obtain ⟨k₁, a₁, ha₁, e₁⟩ := exists_map_eq_mul_pow φ hf hloc hb
  obtain ⟨k₂, a₂, ha₂, e₂⟩ := exists_map_eq_mul_pow φ hf hloc hc
  refine ⟨k₁ + k₂, a₁ * f ^ k₂, a₂ * f ^ k₁, ?_, ?_, ?_, ?_⟩
  · simpa using SetLike.mul_mem_graded ha₁ (SetLike.pow_mem_graded k₂ hf)
  · simpa using SetLike.mul_mem_graded ha₂ (SetLike.pow_mem_graded k₁ hf)
  · rw [map_mul, map_pow, e₁, pow_add, mul_assoc]
  · rw [map_mul, map_pow, e₂, pow_add, mul_assoc, mul_comm (φ f ^ k₁)]

end Graded

section Proj

variable {σ τ A B : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)

/-- `B = A[1/f]` via the graded `φ`: at every point `z` of `Proj ℬ` the local ring map
`A_{(φ⁻¹z)} → B_{(z)}` (the pointwise map of `Proj.twistComapFun`) is a bijection. -/
theorem localRingHom_comap_bijective {f : A}
    (hloc : letI := φ.toRingHom.toAlgebra; IsLocalization.Away f B) (z : ProjectiveSpectrum ℬ) :
    haveI := z.isPrime
    haveI := (ProjectiveSpectrum.comap φ hφ z).isPrime
    Function.Bijective (Localization.localRingHom
      (ProjectiveSpectrum.comap φ hφ z).asHomogeneousIdeal.toIdeal
      z.asHomogeneousIdeal.toIdeal (φ : A →+* B) rfl) :=
  haveI := z.isPrime
  localRingHom_bijective_of_isLocalizationAway (φ : A →+* B) hloc z.asHomogeneousIdeal.toIdeal

set_option backward.isDefEq.respectTransparency false in
open MiyaokaMori.WeightedJets.ProjTwisting in
/-- **Stacks 01MX for a degree-0 localization.** If `B = A[1/f]` via the graded `φ : 𝒜 →+*ᵍ ℬ` with
`f ∈ 𝒜 0`, and `ρ = Proj.map φ : Proj ℬ ⟶ Proj 𝒜` is an open immersion, then the comparison map
`θ : ρ^* O_{Proj 𝒜}(n) ⟶ O_{Proj ℬ}(n)` is an isomorphism. Proof: stalk criterion; the unit
`O_𝒜(n)_{ρ y} → (ρ^* O_𝒜(n))_y` is bijective (open immersion), and `θ_y ∘ unit` sends germs of
sections `s` to germs of `φ_W(s)(z) = (A_{(ρ z)} → B_{(z)})(s(ρ z))`; injectivity from the pointwise
bijectivity of the local ring maps (`localRingHom_comap_bijective`), surjectivity by lifting a local
fraction `b/c` of `B` to `a/a'` with `φ a = b φ f ^ k`, `φ a' = c φ f ^ k` (`exists_map_eq_mul_pow₂`). -/
theorem isIso_twistPullbackHom_of_isLocalizationAway {f : A} (hf : f ∈ 𝒜 0)
    (hloc : letI := φ.toRingHom.toAlgebra; IsLocalization.Away f B)
    [IsOpenImmersion (Proj.map φ hφ)] (n : ℤ) :
    IsIso (Proj.twistPullbackHom φ hφ n) := by
  set ρ := Proj.map φ hφ with hρ
  set M := Proj.twist 𝒜 n with hM
  set N := Proj.twist ℬ n with hN
  set ψ := Proj.twistToPushforward φ hφ n with hψ
  have hpt := localRingHom_comap_bijective φ hφ hloc
  -- the germ formula for θ_y ∘ u_y
  have key : ∀ (y : Proj ℬ) (W : (Proj 𝒜).Opens) (hy : ρ.base y ∈ W) (s : M.val.obj (op W)),
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap _ y (Proj.twistPullbackHom φ hφ n)
        (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ρ M y (M.presheaf.germ W (ρ.base y) hy s)) =
      N.presheaf.germ (ρ ⁻¹ᵁ W) y hy (ψ.app W s) := fun y W hy s =>
    moduleStalkMap_transpose_unit_germ ρ M N ψ y W hy s
  rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
  intro y
  have hu := MiyaokaMori.PullbackStalkOpenImmersion.modulePullbackStalkUnit_bijective ρ M y
  rw [← Function.Bijective.of_comp_iff _ hu]
  constructor
  · intro t₁ t₂ ht
    obtain ⟨W₁, hy₁, s₁, rfl⟩ := M.presheaf.exists_germ_eq t₁
    obtain ⟨W₂, hy₂, s₂, rfl⟩ := M.presheaf.exists_germ_eq t₂
    have ht' : N.presheaf.germ (ρ ⁻¹ᵁ W₁) y hy₁ (ψ.app W₁ s₁) =
        N.presheaf.germ (ρ ⁻¹ᵁ W₂) y hy₂ (ψ.app W₂ s₂) :=
      (key y W₁ hy₁ s₁).symm.trans (ht.trans (key y W₂ hy₂ s₂))
    obtain ⟨W', hyW', i₁, i₂, heq⟩ := N.presheaf.germ_eq y hy₁ hy₂ _ _ ht'
    have hW₁ : ρ ''ᵁ W' ≤ W₁ := by
      rintro x ⟨z, hz, rfl⟩
      exact leOfHom i₁ hz
    have hW₂ : ρ ''ᵁ W' ≤ W₂ := by
      rintro x ⟨z, hz, rfl⟩
      exact leOfHom i₂ hz
    refine M.presheaf.germ_ext (ρ ''ᵁ W') (Set.mem_image_of_mem ρ.base hyW') (homOfLE hW₁)
      (homOfLE hW₂) ?_
    apply Subtype.ext
    funext x
    obtain ⟨x, hx⟩ := x
    obtain ⟨z, hz, rfl⟩ := hx
    have hz' := congrArg (fun m : sectionsSubmodule ℬ n W' => m.1 ⟨z, hz⟩) heq
    exact (hpt z).injective hz'
  · intro t
    obtain ⟨W', hyW', m, rfl⟩ := N.presheaf.exists_germ_eq t
    obtain ⟨W'', hyW'', i, hfrac⟩ := (show sectionsSubmodule ℬ n W' from m).2 ⟨y, hyW'⟩
    rcases hfrac with h0 | ⟨p, q, b, c, hpq, hc, hrep⟩
    · refine ⟨0, ?_⟩
      have h1 : N.presheaf.map i.op m = 0 := Subtype.ext (funext fun z => congrFun h0 z)
      have h2 : N.presheaf.germ W' y hyW' m =
          N.presheaf.germ W'' y hyW'' (N.presheaf.map i.op m) :=
        (N.presheaf.germ_res_apply i y hyW'' m).symm
      show AlgebraicGeometry.Scheme.Modules.moduleStalkMap _ y _ (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ρ M y 0) = _
      rw [map_zero, map_zero, h2, h1]
      exact (map_zero _).symm
    · obtain ⟨k, a, a', ha, ha', ea, ea'⟩ := exists_map_eq_mul_pow₂ φ hf hloc b.2 c.2
      have hunit : IsUnit (φ f) :=
        letI := φ.toRingHom.toAlgebra
        IsLocalization.Away.algebraMap_isUnit (S := B) f
      have hden : ∀ x : (ρ ''ᵁ W'' : (Proj 𝒜).Opens), a' ∉ x.1.asHomogeneousIdeal := by
        rintro ⟨x, z, hz, rfl⟩ hmem
        have hmem' : φ a' ∈ z.asHomogeneousIdeal.toIdeal := hmem
        rw [ea'] at hmem'
        rcases z.isPrime.mem_or_mem hmem' with h1 | h1
        · exact hc ⟨z, hz⟩ h1
        · exact z.isPrime.ne_top
            (z.asHomogeneousIdeal.toIdeal.eq_top_of_isUnit_mem h1 (hunit.pow k))
      have hs : (locallyFraction 𝒜 n).pred
          (fun x : (ρ ''ᵁ W'' : (Proj 𝒜).Opens) => (Localization.mk a ⟨a', hden x⟩ : Fiber 𝒜 x.1)) :=
        TopCat.PrelocalPredicate.sheafifyOf (P := fractionPrelocal 𝒜 n)
          (Or.inr ⟨p, q, ⟨a, ha⟩, ⟨a', ha'⟩, hpq, hden, fun _ => rfl⟩)
      let s : sectionsSubmodule 𝒜 n (ρ ''ᵁ W'') :=
        ⟨fun x => (Localization.mk a ⟨a', hden x⟩ : Fiber 𝒜 x.1), hs⟩
      refine ⟨M.presheaf.germ (ρ ''ᵁ W'') (ρ.base y) (Set.mem_image_of_mem ρ.base hyW'') s,
        (key y _ _ s).trans ?_⟩
      have hle : W'' ≤ ρ ⁻¹ᵁ (ρ ''ᵁ W'') := fun z hz => Set.mem_image_of_mem ρ.base hz
      refine N.presheaf.germ_ext W'' hyW'' (homOfLE hle) i ?_
      apply Subtype.ext
      funext z
      have hz := z.2
      have := z.1.isPrime
      have := (ProjectiveSpectrum.comap φ hφ z.1).isPrime
      have e1 : (show sectionsSubmodule ℬ n W'' from
            N.presheaf.map (homOfLE hle).op (ψ.app (ρ ''ᵁ W'') s)).1 z =
          Localization.localRingHom (ProjectiveSpectrum.comap φ hφ z.1).asHomogeneousIdeal.toIdeal
            z.1.asHomogeneousIdeal.toIdeal (φ : A →+* B) rfl
            (Localization.mk a ⟨a', hden ⟨ρ.base z.1, Set.mem_image_of_mem ρ.base hz⟩⟩) := rfl
      have e2 : (show sectionsSubmodule ℬ n W'' from N.presheaf.map i.op m).1 z = m.1 (i z) := rfl
      refine e1.trans (Eq.trans ?_ e2.symm)
      rw [Localization.localRingHom_mk, show m.1 (i z) = Localization.mk b.1 ⟨c.1, hc z⟩ from hrep z,
        Localization.mk_eq_mk_iff]
      apply Localization.r_of_eq
      change c.1 * φ a = φ a' * b.1
      rw [ea, ea']
      ring

end Proj

end MiyaokaMori.RelativeProjTwistLocalIso

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

open MiyaokaMori.RelativeProjTwistLocalIso

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- The chart transition `ρ = Proj.map (S.restrictGraded h) : Proj S(U) ⟶ Proj S(V)` (`U ≤ V`) is an
open immersion: `ρ ≫ projChart V = projChart U` with both charts open immersions. Stated as a
`theorem` (not a global instance); supply it locally with `haveI`. -/
theorem isOpenImmersion_projMap_restrictGraded {U V : X.AffineZariskiSite} (h : U ≤ V) :
    IsOpenImmersion (Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h)) := by
  have e : Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) ≫ S.projChart V =
      S.projChart U := S.map_projChart h
  have : IsOpenImmersion (Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) ≫
      S.projChart V) := by
    rw [e]; infer_instance
  exact IsOpenImmersion.of_comp _ (S.projChart V)

/-- Stacks 01MX for a degree-0 localization: the comparison `ρ^* O_{Proj S(V)}(m) ⟶ O_{Proj S(U)}(m)`
along the chart transition `ρ = Proj.map (S.restrictGraded h)`, `U ≤ V`, is an isomorphism.
Natural-language proof in the module docstring. -/
theorem isIso_twistPullbackHom_restrictGraded (m : ℤ) {U V : X.AffineZariskiSite} (h : U ≤ V) :
    IsIso (Proj.twistPullbackHom (S.restrictGraded h) (S.restrict_irrelevant_le h) m) := by
  have hex : ∃ f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens := h
  obtain ⟨f, hf⟩ := hex
  obtain rfl : V.basicOpen f = U := Subtype.ext hf
  have := S.isOpenImmersion_projMap_restrictGraded h
  exact isIso_twistPullbackHom_of_isLocalizationAway (S.restrictGraded h)
    (S.restrict_irrelevant_le h) (S.unit_mem V f)
    (S.toAffineAlgebra.isLocalization_basicOpen V f) m

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
