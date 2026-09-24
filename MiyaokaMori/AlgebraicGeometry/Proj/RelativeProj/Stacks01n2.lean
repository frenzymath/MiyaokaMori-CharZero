import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjMapTwistComparison
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01n2AwayBaseChange
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01n2TwistStalk

/-! # Proj commutes with base change (Stacks 01N2)

Stacks 01N2: for `R → A_0` and `R → R'`, one has `Proj(R' ⊗_R A) = Spec R' ×_{Spec R} Proj A`
(base change commutes with Proj). Also used in the proof of Stacks 0AGQ (Rees algebra `⊗ κ`).

Route for `isPullback_of_isBaseChange`: check the square on the affine open cover `D₊(s)` of
`Proj 𝒜` (`Scheme.isPullback_of_openCover`, Mathlib `Proj.affineOpenCover`); the chart
`D₊(f s) → D₊(s)` is the pullback of `D₊(s) → Proj 𝒜` along `Proj.map f hf`
(`Proj.isPullback_awayι_map`, `RelativeProj.lean`); on the chart the square is `Spec` of the pushout
square of rings `R → 𝒜_(s)`, `R → R'`, `𝒜_(s) → ℬ_(f s)`, `R' → ℬ_(f s)`
(`Stacks01n2AwayBaseChange.isPushout_away`: the degree-zero localization commutes with base change;
`isPullback_SpecMap_of_isPushout`), and `awayι_toSpecZero` identifies `D₊(s) → Proj 𝒜 → Spec 𝒜_0`
with `Spec (𝒜_0 → 𝒜_(s))`. Then paste (`IsPullback.paste_vert`) as in `projNatTrans_equifibered`.
`isIso_twistPullbackHom` is assembled from the stalk criterion
(`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`), the bijectivity of the pullback-stalk tensor map
and the stalk-level bijectivity `Proj.twistPullbackHom_stalkMap_comp_tensorMap_bijective`
(`Stacks01n2TwistStalk.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped HomogeneousIdeal

theorem AlgebraicGeometry.Proj.isPullback_of_isBaseChange {R R' A B : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Algebra R' B]
    [IsScalarTower R R' B] (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (fR : A →ₐ[R] B) (hfR : ∀ a, fR a = f a) (hbc : IsBaseChange R' fR.toLinearMap) :
    CategoryTheory.IsPullback (AlgebraicGeometry.Proj.map f hf)
      (AlgebraicGeometry.Proj.toSpecZero ℬ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R' (ℬ 0))))
      (AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  refine AlgebraicGeometry.Scheme.isPullback_of_openCover _ _ _ _
    (AlgebraicGeometry.Proj.affineOpenCover 𝒜).openCover ?_
  rintro ⟨n, s, hs⟩
  have hd : 0 < (n : ℕ) := n.pos
  have hch := AlgebraicGeometry.Proj.isPullback_awayι_map f hf hd s hs
  -- the chart square is `Spec` of the pushout square of rings (Stacks01n2AwayBaseChange)
  have hbig : IsPullback (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s)))
      (AlgebraicGeometry.Proj.awayι ℬ (f s) (f.2 hs) hd ≫ AlgebraicGeometry.Proj.toSpecZero ℬ ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R' (ℬ 0))))
      (AlgebraicGeometry.Proj.awayι 𝒜 s hs hd ≫ AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
    rw [AlgebraicGeometry.Proj.awayι_toSpecZero_assoc, AlgebraicGeometry.Proj.awayι_toSpecZero_assoc,
      ← AlgebraicGeometry.Spec.map_comp, ← AlgebraicGeometry.Spec.map_comp]
    apply AlgebraicGeometry.isPullback_SpecMap_of_isPushout
    exact MiyaokaMori.Stacks01n2.isPushout_away 𝒜 ℬ f fR hfR hbc hs
  have hiso : IsPullback (pullback.snd (AlgebraicGeometry.Proj.map f hf)
      (AlgebraicGeometry.Proj.awayι 𝒜 s hs hd)) hch.flip.isoPullback.inv (𝟙 _)
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map f s))) :=
    IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hch.flip.isoPullback_inv_snd]⟩
  have := hiso.paste_vert hbig
  rw [Category.id_comp, IsPullback.isoPullback_inv_fst_assoc] at this
  exact this

/- `twistComapFun` is induced pointwise by a localization ring homomorphism, so it
   preserves the multiplication used by the local descriptions of twist sheaves. -/
theorem AlgebraicGeometry.Proj.twistComapFun_mul
    {σ τ A B : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (V : Opens (ProjectiveSpectrum.top ℬ))
    (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)
    (s t : ∀ x : U, MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 x.1) (y : V) :
    AlgebraicGeometry.Proj.twistComapFun f hf U V hUV (fun x ↦ s x * t x) y =
      AlgebraicGeometry.Proj.twistComapFun f hf U V hUV s y *
        AlgebraicGeometry.Proj.twistComapFun f hf U V hUV t y := by
  simp [AlgebraicGeometry.Proj.twistComapFun]

/-- The comparison map `θ` of twisting sheaves along base change (last sentence of Stacks 01N2, via
01MX) is an isomorphism: for `B = R' ⊗_R A`, on each `D_+(a)` the map `θ` is the canonical
isomorphism `(B_{f a})_n = R' ⊗_R (A_a)_n`.

Proof: by the stalk criterion `AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`, the bijectivity of the
pullback-stalk tensor map, and the stalk-level bijectivity
`Proj.twistPullbackHom_stalkMap_comp_tensorMap_bijective` (`Stacks01n2TwistStalk.lean`). -/
theorem AlgebraicGeometry.Proj.isIso_twistPullbackHom {R R' A B : Type u} [CommRing R] [CommRing R']
    [Algebra R R'] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Algebra R' B]
    [IsScalarTower R R' B] (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f)
    (fR : A →ₐ[R] B) (hfR : ∀ a, fR a = f a) (hbc : IsBaseChange R' fR.toLinearMap) (n : ℤ) :
    CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistPullbackHom f hf n) := by
  rw [AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective]
  intro y
  exact (Function.Bijective.of_comp_iff _
    (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective
      (AlgebraicGeometry.Proj.map f hf) (AlgebraicGeometry.Proj.twist 𝒜 n) y)).mp
    (AlgebraicGeometry.Proj.twistPullbackHom_stalkMap_comp_tensorMap_bijective 𝒜 ℬ f hf fR hfR hbc n y)
end
