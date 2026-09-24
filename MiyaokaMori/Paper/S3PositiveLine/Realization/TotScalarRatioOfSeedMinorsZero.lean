import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.SeedBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceRestrictToZeroSection
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackTransport
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892_PullbackNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualPowerContraction
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheafMul

/-! # The scalar ratio on the total space when the seed minors vanish

Steps 1–4 of `exists_scalar_ratio_of_seed_minors_eq_zero`, carried out on the total space `Tot(L)` (before
restricting to the jet neighbourhood): if the affine tuple `P` restricts to the seed tuple along the zero
section and all `2×2` minors with the seed tuple vanish, then on `p⁻¹V` for a nonempty open `V ⊆ C̃` the
tuple `P` is `λ` times the pulled-back seed tuple, with `λ = 1` along the zero section.

Source: proof of Theorem 4.2 of the paper ("the affine tuple would therefore be a scalar multiple of
the seed tuple, with scalar value one at zero").

## Structure

Everything is proved at the **variable level** (`p : T ⟶ Y`, a section `σ` of `p`, a line bundle `A` on `Y`),
in `exists_scalar_ratio_of_minors_eq_zero_general`; the concrete theorem is that lemma instantiated with
`p = Tot(L) → C̃`, `σ = σ₀`, `A = A_ρ` (`restrictToZeroSection` unfolds to the comparison used there).
The variable-level ingredients:
* `pullbackId_hom_app_pullback` — `(pullbackId X).hom` inverts the adjunction unit on global sections
  (mate calculus: Mathlib `conjugateEquiv_pullbackId_hom` + `unit_conjugateEquiv`);
* `zeroSectionComparison_hom_app_pullback_pullback` — ingredient (ii): `Φ(σ^* p^* a) = a` for
  `Φ = pullbackComp ≪≫ pullbackCongr (σ ≫ p = 𝟙) ≪≫ pullbackId`;
* `sectionPullbackAlong_eq_smul_of_res_eq_smul` / `res_eq_smul_of_sectionPullbackAlong_eq_smul` — ingredient (iii):
  the bridge `Γ(M, f ''ᵁ ⊤) ↔ Γ(f^*M, ⊤)` for an open immersion `f`, with scalars transported by `f.appIso ⊤`
  (`restrictIso_inv_pullback`, `restrictIso_hom_restrict`, `restrictIso_inv_smul`);
* `IsFrame.eq_of_smul_moduleTensorSection_eq` — ingredient (i): the tensor `e ⊗ f` of two frames is torsion-free
  (`c • (e ⊗ f) = c' • (e ⊗ f) ⇒ c = c'`), via the stalk isomorphism `IsFrame.tensorStalkEquivOfFrames`
  (Stacks 01CB) and `TopCat.Presheaf.section_ext`;
* `sectionTensor_eq_of_hom_app` — the minors condition transported along a module morphism in the second factor.
-/
/- `sectionPullbackAlong` is the one definition (its body is the adjunction unit) and `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback`
its `Γ`-typed reducible abbrev: `unfold sectionPullbackAlong` does not produce the `Γ`-typed spelling; the proofs below
bridge to it with `rw [sectionPullbackAlong_eq_pullback <g> <s>]` (explicit arguments: the arguments are `Γ`-typed, so
a generic `rw`/`simp only` cannot abstract these occurrences at reducible transparency) or by a `change`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Step 1 (proved): some pulled-back seed coordinate is nonzero somewhere -/

/-- The comparison isomorphism `ρ^*(seedLineBundle X.embedding f) ≅ (seedBundlePullback f ρ).toModules`
whose `hom` is the transport used in `seedCoordPullback`. -/
noncomputable def seedCoordPullbackIso {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) (ρ : FiniteCover k C) :
    (AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj (seedLineBundle X.embedding f) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj (seedBundle f).toModules :=
  (AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).mapIso
    ((AlgebraicGeometry.Scheme.Modules.pullback f).mapIso
      (CategoryTheory.eqToIso (X.OX_toModules 1).symm))

theorem seedCoordPullback_eq_iso_hom {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) (ρ : FiniteCover k C)
    (s : ((seedLineBundle X.embedding f).val.obj (Opposite.op ⊤) : Type u)) :
    seedCoordPullback f ρ s
      = ((seedCoordPullbackIso f ρ).hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong ρ.hom s) := rfl

/-- **Step 1 of **: some pulled-back seed coordinate
`a_j = seedCoordPullback f ρ (D.coord j)` is nonzero at some point of `C̃`.
Proof: `C̃` is integral, hence nonempty; pick `x`. `D.hcoord.1` gives `j` with `D.coord j` not zero at
`ρ(x)`; `not_isZeroAt_sectionPullbackAlong ρ.hom` lifts this to `ρ^*(D.coord j)` at `x`; `a_j` is the
image under the module isomorphism `seedCoordPullbackIso`, and `IsZeroAt` (= complement of the
nonvanishing locus) is invariant under module isomorphisms (`mem_nonvanishingLocus_iso`). -/
theorem exists_seedCoordPullback_not_isZeroAt {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] (ρ : FiniteCover k C) :
    ∃ j : Fin (X.embDim + 1), ∃ x : ρ.source.toScheme,
      ¬ IsZeroAt (seedCoordPullback f ρ (D.coord j)) x := by
  have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  obtain ⟨x⟩ : Nonempty ρ.source.toScheme := inferInstance
  obtain ⟨hc, -⟩ := D.hcoord
  obtain ⟨j, hj⟩ := hc (ρ.hom.base x)
  refine ⟨j, x, ?_⟩
  have h1 : ¬ IsZeroAt (sectionPullbackAlong ρ.hom (D.coord j)) x :=
    not_isZeroAt_sectionPullbackAlong ρ.hom _ (D.coord j) x hj
  rw [seedCoordPullback_eq_iso_hom]
  intro h2
  exact (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso (seedCoordPullbackIso f ρ)
    (sectionPullbackAlong ρ.hom (D.coord j)) x).mpr h1 h2

/-! ## Variable-level ingredients -/

namespace TotScalarRatio

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules

/-- `(pullbackId X).hom` inverts the adjunction unit on global sections:
`(pullbackId X).hom.app M (η_{𝟙} s) = s`. Proof: `pullbackId` is the left-adjoint mate of `pushforwardId`
(Mathlib `conjugateEquiv_pullbackId_hom`), so `unit_conjugateEquiv` gives
`η_{𝟙} ≫ (𝟙 X)_*((pullbackId X).hom.app M) = (pushforwardId X).inv.app M`, whose components are identities. -/
theorem pullbackId_hom_app_pullback {X : Scheme.{u}} (M : X.Modules) (s : Γ(M, ⊤)) :
    ((pullbackId X).app M).hom.app ⊤ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (𝟙 X) s) = s := by
  have hu := unit_conjugateEquiv Adjunction.id (pullbackPushforwardAdjunction (𝟙 X))
    (pullbackId X).hom M
  rw [conjugateEquiv_pullbackId_hom] at hu
  have hs := congrArg (fun φ : M ⟶ (pushforward (𝟙 X)).obj M ↦ φ.app ⊤ s) hu
  exact hs.symm

/-- The comparison `σ^* p^* A ≅ A` for a section `σ` of `p` (`σ ≫ p = 𝟙`); `restrictToZeroSection` is this
comparison for `σ = σ₀`, `p = Tot(V) → X`. -/
noncomputable def zeroSectionComparison {Y T : Scheme.{u}} (p : T ⟶ Y) (σ : Y ⟶ T) (hσ : σ ≫ p = 𝟙 Y)
    (A : Y.Modules) :
    (pullback σ).obj ((pullback p).obj A) ≅ A :=
  (pullbackComp σ p).app A ≪≫ (pullbackCongr hσ).app A ≪≫ (pullbackId Y).app A

/-- Ingredient (ii): `Φ(σ^* p^* a) = a` — pseudofunctoriality of the pullback of sections
(`pullback_comp`, `pullbackCongr_apply`, `pullbackId_hom_app_pullback`). -/
theorem zeroSectionComparison_hom_app_pullback_pullback {Y T : Scheme.{u}} (p : T ⟶ Y) (σ : Y ⟶ T)
    (hσ : σ ≫ p = 𝟙 Y) (A : Y.Modules) (a : Γ(A, ⊤)) :
    (zeroSectionComparison p σ hσ A).hom.app ⊤ (sectionPullbackAlong σ (sectionPullbackAlong p a)) = a := by
  change ((pullbackId Y).app A).hom.app ⊤ (((pullbackCongr hσ).app A).hom.app ⊤
    (((pullbackComp σ p).app A).hom.app ⊤
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback σ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback p a)))) = a
  rw [AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp, AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply]
  exact pullbackId_hom_app_pullback A a

/-- Ingredient (iii), forward direction. For an open immersion `f : X ⟶ Y`: if `s|_{f(X)} = c • s'|_{f(X)}` in
`Γ(M, f ''ᵁ ⊤)`, then `f^*s = (f^♯ c) • f^*s'` in `Γ(f^*M, ⊤)`, where `f^♯ = (f.appIso ⊤).hom : Γ(Y, f ''ᵁ ⊤) ≅ Γ(X, ⊤)`.
Proof: apply the authors' comparison `Ψ⁻¹ := (restrictFunctorIsoPullback f).hom ∘ (restrictAppIso f ⊤).inv`,
which sends `s|_{f(X)}` to `f^*s` (`restrictIso_hom_restrict`) and is `f^♯`-semilinear (`smul_restrictAppIso_inv`,
`Hom.app_smul`). -/
theorem sectionPullbackAlong_eq_smul_of_res_eq_smul {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (s s' : Γ(M, ⊤)) (c : Γ(Y, f ''ᵁ ⊤))
    (h : M.presheaf.map (homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s
      = c • M.presheaf.map (homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s') :
    sectionPullbackAlong f s
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from (f.appIso ⊤).hom c) • sectionPullbackAlong f s' := by
  have h1 := AlgebraicGeometry.Scheme.Modules.ModuleSections.restrictIso_hom_restrict f s
  have h2 := AlgebraicGeometry.Scheme.Modules.ModuleSections.restrictIso_hom_restrict f s'
  have h3 : (M.restrictAppIso f ⊤).inv
      (c • M.presheaf.map (homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s')
      = ((f.appIso ⊤).hom c) • (M.restrictAppIso f ⊤).inv
          (M.presheaf.map (homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s') :=
    CategoryTheory.congr_fun (smul_restrictAppIso_inv f M ⊤ c) _
  -- bridge to the `Γ`-typed spelling with explicit arguments (`s s' : Γ(M, ⊤)`, so a generic rewrite cannot abstract
  -- these occurrences at reducible transparency; T18b)
  rw [sectionPullbackAlong_eq_pullback f s, sectionPullbackAlong_eq_pullback f s']
  rw [← h1, ← h2, h, h3, Hom.app_smul]
  rfl

/-- Ingredient (iii), backward direction. For an open immersion `f : X ⟶ Y`: if `f^*s = μ • f^*s'` in
`Γ(f^*M, ⊤)`, then `s|_{f(X)} = ((f.appIso ⊤).inv μ) • s'|_{f(X)}` in `Γ(M, f ''ᵁ ⊤)`
(the authors' `restrictIso_inv_pullback` and `restrictIso_inv_smul`). -/
theorem res_eq_smul_of_sectionPullbackAlong_eq_smul {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (s s' : Γ(M, ⊤)) (μ : Γ(X, ⊤))
    (h : sectionPullbackAlong f s
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from μ) • sectionPullbackAlong f s') :
    M.presheaf.map (homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s
      = ((f.appIso ⊤).inv μ) • M.presheaf.map (homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s' := by
  rw [← AlgebraicGeometry.Scheme.Modules.ModuleSections.restrictIso_inv_pullback f s,
    ← AlgebraicGeometry.Scheme.Modules.ModuleSections.restrictIso_inv_pullback f s',
    ← AlgebraicGeometry.Scheme.Modules.ModuleSections.restrictIso_inv_smul]
  rw [sectionPullbackAlong_eq_pullback f s, sectionPullbackAlong_eq_pullback f s'] at h
  rw [h]
  rfl

/-- Ingredient (i): the tensor of two frames is torsion-free. If `e` is a frame of `L` and `f` a frame of `N` on `W`,
and `c • (e ⊗ f) = c' • (e ⊗ f)` in `Γ(L ⊗ N, W)`, then `c = c'`. Proof: sections of `𝒪_X` are determined by
their germs (`TopCat.Presheaf.section_ext`); at `y ∈ W` the stalk isomorphism
`Θ : (L ⊗ N)_y ≃ 𝒪_y` of `IsFrame.tensorStalkEquivOfFrames` (Stacks 01CB) sends `(e ⊗ f)_y` to `1`, so
`Θ((c • (e ⊗ f))_y) = c_y`, and likewise for `c'`. -/
theorem IsFrame.eq_of_smul_moduleTensorSection_eq {X : Scheme.{u}} {L N : X.Modules} {W : X.Opens}
    {e : Γ(L, W)} {f : Γ(N, W)} (he : IsFrame L W e) (hf : IsFrame N W f) (c c' : Γ(X, W))
    (h : (c • AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f : Γ(tensor L N, W))
      = c' • AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f) : c = c' := by
  apply TopCat.Presheaf.section_ext X.sheaf W
  intro y hy
  have h1 := congrArg ((tensor L N).presheaf.germ W y hy) h
  have hg : ∀ r : Γ(X, W), (tensor L N).presheaf.germ W y hy
      (r • AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f : Γ(tensor L N, W))
      = X.presheaf.germ W y hy r • (tensor L N).presheaf.germ W y hy (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f) :=
    fun r ↦ germ_smul' (tensor L N) hy r _
  rw [hg, hg] at h1
  have h2 := congrArg (he.tensorStalkEquivOfFrames hf hy) h1
  rw [LinearEquiv.map_smul, LinearEquiv.map_smul, he.tensorStalkEquivOfFrames_germ_frame hf hy] at h2
  simp only [smul_eq_mul, mul_one] at h2
  exact h2

/-- `moduleTensorSection (a • s) t = a • moduleTensorSection s t` (the `b = 1` case of `moduleTensorSection_smul`). -/
theorem moduleTensorSection_smul_left {X : Scheme.{u}} {M N : X.Modules} {U : X.Opens} (a : Γ(X, U))
    (s : Γ(M, U)) (t : Γ(N, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection (a • s) t = a • AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t := by
  have h := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul a (1 : Γ(X, U)) s t
  rwa [one_smul, mul_one] at h

/-- The minors condition is transported along a module morphism `φ : N ⟶ A` in the second factor:
if `P_i ⊗ p^*s_j = P_j ⊗ p^*s_i` and `a_ℓ = φ(s_ℓ)`, then `P_i ⊗ p^*a_j = P_j ⊗ p^*a_i`
(`sectionPullbackAlong_naturality`, the authors' `tensorMap_section`). -/
theorem sectionTensor_eq_of_hom_app {Y T : Scheme.{u}} (p : T ⟶ Y) {N A : Y.Modules} (φ : N ⟶ A)
    {ι : Type v} (P : ι → (((pullback p).obj A).val.obj (Opposite.op ⊤) : Type u))
    (s : ι → (N.val.obj (Opposite.op ⊤) : Type u)) (a : ι → (A.val.obj (Opposite.op ⊤) : Type u))
    (ha : ∀ ℓ, a ℓ = (φ.val.app (Opposite.op ⊤)).hom (s ℓ))
    (hminor : ∀ i j, sectionTensor (P i) (sectionPullbackAlong p (s j))
      = sectionTensor (P j) (sectionPullbackAlong p (s i))) (i j : ι) :
    sectionTensor (P i) (sectionPullbackAlong p (a j)) = sectionTensor (P j) (sectionPullbackAlong p (a i)) := by
  rw [ha, ha, sectionPullbackAlong_naturality, sectionPullbackAlong_naturality]
  have h1 := AlgebraicGeometry.Scheme.Modules.ModuleDualPowerContraction.tensorMap_section (𝟙 ((pullback p).obj A))
    ((pullback p).map φ) (U := ⊤) (P i) (sectionPullbackAlong p (s j))
  have h2 := AlgebraicGeometry.Scheme.Modules.ModuleDualPowerContraction.tensorMap_section (𝟙 ((pullback p).obj A))
    ((pullback p).map φ) (U := ⊤) (P j) (sectionPullbackAlong p (s i))
  change (AlgebraicGeometry.Scheme.Modules.tensorMap (𝟙 ((pullback p).obj A)) ((pullback p).map φ)).app ⊤
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P i) (sectionPullbackAlong p (s j)))
    = AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P i) (((pullback p).map φ).app ⊤ (sectionPullbackAlong p (s j))) at h1
  change (AlgebraicGeometry.Scheme.Modules.tensorMap (𝟙 ((pullback p).obj A)) ((pullback p).map φ)).app ⊤
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P j) (sectionPullbackAlong p (s i)))
    = AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P j) (((pullback p).map φ).app ⊤ (sectionPullbackAlong p (s i))) at h2
  change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P i) (((pullback p).map φ).app ⊤ (sectionPullbackAlong p (s j)))
    = AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P j) (((pullback p).map φ).app ⊤ (sectionPullbackAlong p (s i)))
  rw [← h1, ← h2]
  exact congrArg _ (hminor i j)

/-- Transport of a scalar relation across a commutative square (same statement as
`sectionPullbackAlong_square_smul` in `ScalarRatioOfSeedMinorsZero`, which imports this module). -/
private theorem square_smul {X Y Y' Z : Scheme.{u}}
    (g : X ⟶ Y) (ι' : Y ⟶ Z) (g' : X ⟶ Y') (ι'' : Y' ⟶ Z) (h : g ≫ ι' = g' ≫ ι'')
    {M : Z.Modules} (P Q : (M.val.obj (Opposite.op ⊤) : Type u)) (c : Γ(Y, ⊤))
    (hPQ : sectionPullbackAlong ι' P
      = (show Y.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) • sectionPullbackAlong ι' Q) :
    sectionPullbackAlong g' (sectionPullbackAlong ι'' P)
      = (show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from g.appTop c) •
          sectionPullbackAlong g' (sectionPullbackAlong ι'' Q) := by
  have h1 := congrArg (sectionPullbackAlong g) hPQ
  rw [sectionPullbackAlong_smul] at h1
  have h2 := congrArg (fun y =>
    (((pullbackComp g' ι'').app M).inv.val.app (Opposite.op ⊤)).hom
      ((((pullbackCongr h).app M).hom.val.app (Opposite.op ⊤)).hom
        ((((pullbackComp g ι').app M).hom.val.app (Opposite.op ⊤)).hom y))) h1
  beta_reduce at h2
  rw [sectionPullbackAlong_comp_congr g ι' g' ι'' h, modules_hom_app_top_smul, modules_hom_app_top_smul,
    modules_hom_app_top_smul, sectionPullbackAlong_comp_congr g ι' g' ι'' h] at h2
  exact h2

/-- **Steps 1–4 at the variable level.** `p : T ⟶ Y` with a section `σ` (`σ ≫ p = 𝟙`), `A` a line bundle on `Y`,
`P_ℓ ∈ Γ(T, p^*A)` with `Φ(σ^*P_ℓ) = a_ℓ` (`Φ = zeroSectionComparison`) and `P_i ⊗ p^*a_j = P_j ⊗ p^*a_i`, and
`a_j` not zero at `x`. Then with `V := Y_{a_j}` (∋ `x`) there is `λ ∈ Γ(p⁻¹V, 𝒪)` with `σ|_V^*λ = 1` and
`P_ℓ|_{p⁻¹V} = λ • (p^*a_ℓ)|_{p⁻¹V}` for all `ℓ` (restriction = pullback along `(p⁻¹V).ι`).

Proof. Put `W := p⁻¹V`, `M := p^*A`, `t_ℓ := p^*a_ℓ`, `W' := W.ι ''ᵁ ⊤ (= W)`.
2. `t_j` is nowhere zero on `W` (`not_isZeroAt_sectionPullbackAlong`), so `e := t_j|_{W'}` is a frame of `M` on `W'`
   (`isFrame_res_nonvanishingLocus`, `IsFrame.restrict`). Let `c_ℓ, d_ℓ` be the coordinates of `P_ℓ|, t_ℓ|` (`d_j = 1`).
3. Restricting the minors to `W'` gives `c_i • (e ⊗ e) = (c_j d_i) • (e ⊗ e)`, so `c_i = c_j d_i`
   (`IsFrame.eq_of_smul_moduleTensorSection_eq`), i.e. `P_i| = c_j • t_i|` in `Γ(M, W')`; transport to `W.toScheme`
   (`sectionPullbackAlong_eq_smul_of_res_eq_smul`) with `λ := (W.ι.appIso ⊤).hom c_j`.
4. Pull `W.ι^*P_j = λ • W.ι^*t_j` back along `σ|_V : V → W` and across the square `σ|_V ≫ W.ι = V.ι ≫ σ`
   (`square_smul`); apply `V.ι^*Φ` (`sectionPullbackAlong_naturality`) and use `hzero j`, ingredient (ii):
   `V.ι^*a_j = μ • V.ι^*a_j` with `μ = σ|_V^♯ λ`. Transport back (`res_eq_smul_of_sectionPullbackAlong_eq_smul`):
   `a_j| = ν • a_j|` on `V.ι ''ᵁ ⊤` with `ν = (V.ι.appIso ⊤).inv μ`; `a_j` is a frame there, so `ν = 1`, `μ = 1`. -/
theorem exists_scalar_ratio_of_minors_eq_zero_general {Y T : Scheme.{u}} (p : T ⟶ Y) (σ : Y ⟶ T)
    (hσ : σ ≫ p = 𝟙 Y) (A : Y.Modules) [A.IsLineBundle] {ι : Type v}
    (P : ι → Γ((Modules.pullback p).obj A, ⊤)) (a : ι → Γ(A, ⊤))
    (hzero : ∀ ℓ, (zeroSectionComparison p σ hσ A).hom.app ⊤ (sectionPullbackAlong σ (P ℓ)) = a ℓ)
    (hminor : ∀ i j, sectionTensor (P i) (sectionPullbackAlong p (a j))
      = sectionTensor (P j) (sectionPullbackAlong p (a i)))
    (j : ι) (x : Y) (hx : ¬ IsZeroAt (a j) x) :
    ∃ V : Y.Opens, x ∈ V ∧
      ∃ lam : Γ((p ⁻¹ᵁ V).toScheme, ⊤),
        (σ.resLE (p ⁻¹ᵁ V) V
          (le_of_eq (by rw [← Scheme.Hom.comp_preimage, hσ]; rfl))).appTop lam = 1 ∧
        ∀ ℓ, sectionPullbackAlong (p ⁻¹ᵁ V).ι (P ℓ)
          = (show (p ⁻¹ᵁ V).toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from lam) •
              sectionPullbackAlong (p ⁻¹ᵁ V).ι (sectionPullbackAlong p (a ℓ)) := by
  -- Step 1: V := nonvanishing locus of a_j
  have hxV : x ∈ A.nonvanishingLocus (a j) := (mem_nonvanishingLocus_iff_not_isZeroAt A (a j) x).mpr hx
  refine ⟨A.nonvanishingLocus (a j), hxV, ?_⟩
  -- notation: M := p^*A, t_ℓ := p^*a_ℓ (as sections in the `Γ` spelling), W := p⁻¹V, W' := W.ι ''ᵁ ⊤
  let M : T.Modules := (Modules.pullback p).obj A
  let t : ι → Γ(M, ⊤) := fun ℓ ↦ sectionPullbackAlong p (a ℓ)
  let W : T.Opens := p ⁻¹ᵁ A.nonvanishingLocus (a j)
  -- Step 2: the frame e := t_j on W'
  have hWle : W.ι ''ᵁ ⊤ ≤ M.nonvanishingLocus (t j) := by
    rw [Scheme.Opens.ι_image_top]
    intro y hy
    exact (mem_nonvanishingLocus_iff_not_isZeroAt M (t j) y).mpr
      (not_isZeroAt_sectionPullbackAlong p A (a j) y
        ((mem_nonvanishingLocus_iff_not_isZeroAt A (a j) _).mp hy))
  have he : IsFrame M (W.ι ''ᵁ ⊤) (M.res hWle (M.res le_top (t j))) :=
    (isFrame_res_nonvanishingLocus M (t j)).restrict hWle
  -- coordinates c_ℓ, d_ℓ of P_ℓ|, t_ℓ|
  have hc : ∀ ℓ, M.res le_top (P ℓ)
      = he.coord le_rfl (M.res le_top (P ℓ)) • M.res hWle (M.res le_top (t j)) := fun ℓ ↦ by
    have := he.coord_smul_frame le_rfl (M.res le_top (P ℓ))
    rw [res_self] at this
    exact this.symm
  have hd : ∀ ℓ, M.res le_top (t ℓ)
      = he.coord le_rfl (M.res le_top (t ℓ)) • M.res hWle (M.res le_top (t j)) := fun ℓ ↦ by
    have := he.coord_smul_frame le_rfl (M.res le_top (t ℓ))
    rw [res_self] at this
    exact this.symm
  have hdj : he.coord le_rfl (M.res le_top (t j)) = 1 := by
    apply he.coord_unique
    rw [one_smul, res_self, res_res]
  -- Step 3: cancel the frame in the minors
  have hmin : ∀ i, he.coord le_rfl (M.res le_top (P i))
      = he.coord le_rfl (M.res le_top (P j)) * he.coord le_rfl (M.res le_top (t i)) := fun i ↦ by
    have h0 : (tensor M M).res (le_top : W.ι ''ᵁ ⊤ ≤ ⊤) (sectionTensor (P i) (t j))
        = (tensor M M).res (le_top : W.ι ''ᵁ ⊤ ≤ ⊤) (sectionTensor (P j) (t i)) :=
      congrArg _ (hminor i j)
    change (AlgebraicGeometry.Scheme.Modules.moduleTensor M M).presheaf.map (homOfLE le_top).op
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P i) (t j))
      = (AlgebraicGeometry.Scheme.Modules.moduleTensor M M).presheaf.map (homOfLE le_top).op
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (P j) (t i)) at h0
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict] at h0
    change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M.res le_top (P i)) (M.res le_top (t j))
      = AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M.res le_top (P j)) (M.res le_top (t i)) at h0
    rw [hc i, hc j, hd i, hd j, hdj, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul,
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul, mul_one] at h0
    exact IsFrame.eq_of_smul_moduleTensorSection_eq he he _ _ h0
  have hres : ∀ i, M.res le_top (P i)
      = he.coord le_rfl (M.res le_top (P j)) • M.res le_top (t i) := fun i ↦ by
    rw [hc i, hmin i, mul_smul, ← hd i]
  -- transport to W.toScheme
  have hℓ : ∀ ℓ, sectionPullbackAlong W.ι (P ℓ)
      = (show W.toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from
          (W.ι.appIso ⊤).hom (he.coord le_rfl (M.res le_top (P j)))) •
          sectionPullbackAlong W.ι (t ℓ) := fun ℓ ↦
    sectionPullbackAlong_eq_smul_of_res_eq_smul W.ι M (P ℓ) (t ℓ) _ (hres ℓ)
  refine ⟨(W.ι.appIso ⊤).hom (he.coord le_rfl (M.res le_top (P j))), ?_, hℓ⟩
  -- Step 4: value along the zero section
  have hle : A.nonvanishingLocus (a j) ≤ σ ⁻¹ᵁ W := by
    show A.nonvanishingLocus (a j) ≤ σ ⁻¹ᵁ (p ⁻¹ᵁ A.nonvanishingLocus (a j))
    exact le_of_eq (by rw [← Scheme.Hom.comp_preimage, hσ]; rfl)
  have hsq : σ.resLE W (A.nonvanishingLocus (a j)) hle ≫ W.ι = (A.nonvanishingLocus (a j)).ι ≫ σ :=
    Scheme.Hom.resLE_comp_ι σ hle
  have key := square_smul _ _ _ _ hsq (P j) (t j) _ (hℓ j)
  have key2 := congrArg (fun y ↦
    ((((Modules.pullback (A.nonvanishingLocus (a j)).ι).map (zeroSectionComparison p σ hσ A).hom).val.app
      (Opposite.op ⊤)).hom y)) key
  beta_reduce at key2
  rw [modules_hom_app_top_smul, ← sectionPullbackAlong_naturality, ← sectionPullbackAlong_naturality] at key2
  change sectionPullbackAlong (A.nonvanishingLocus (a j)).ι
      ((zeroSectionComparison p σ hσ A).hom.app ⊤ (sectionPullbackAlong σ (P j)))
    = (show (A.nonvanishingLocus (a j)).toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from
        (σ.resLE W (A.nonvanishingLocus (a j)) hle).appTop
          ((W.ι.appIso ⊤).hom (he.coord le_rfl (M.res le_top (P j))))) •
      sectionPullbackAlong (A.nonvanishingLocus (a j)).ι
        ((zeroSectionComparison p σ hσ A).hom.app ⊤
          (sectionPullbackAlong σ (sectionPullbackAlong p (a j)))) at key2
  rw [hzero j, zeroSectionComparison_hom_app_pullback_pullback] at key2
  have hres2 := res_eq_smul_of_sectionPullbackAlong_eq_smul (A.nonvanishingLocus (a j)).ι A (a j) (a j) _ key2
  have hfa : IsFrame A ((A.nonvanishingLocus (a j)).ι ''ᵁ ⊤)
      (A.res (le_of_eq (Scheme.Opens.ι_image_top (A.nonvanishingLocus (a j)))) (A.res le_top (a j))) :=
    (isFrame_res_nonvanishingLocus A (a j)).restrict _
  have hν : ((A.nonvanishingLocus (a j)).ι.appIso ⊤).inv
      ((σ.resLE W (A.nonvanishingLocus (a j)) hle).appTop
        ((W.ι.appIso ⊤).hom (he.coord le_rfl (M.res le_top (P j))))) = 1 := by
    apply (hfa _ le_rfl).1
    show _ • A.res le_rfl (A.res _ (A.res le_top (a j))) = (1 : Γ(Y, _)) • A.res le_rfl (A.res _ (A.res le_top (a j)))
    rw [res_self, one_smul,
      res_res A (le_of_eq (Scheme.Opens.ι_image_top (A.nonvanishingLocus (a j)))) le_top (a j)]
    exact hres2.symm
  have h1 := congrArg ((A.nonvanishingLocus (a j)).ι.appIso ⊤).hom hν
  rw [map_one, Iso.inv_hom_id_apply] at h1
  exact h1

end TotScalarRatio

/-! ## The lemma -/

/-- **Steps 1–4 on `Tot(L)`: the affine tuple is a scalar multiple of the seed tuple, with scalar `1`
along the zero section.**

Notation: `p : Tot(L) → C̃`, `A_ρ = seedBundlePullback f ρ` (a line bundle on `C̃`),
`a_ℓ := seedCoordPullback f ρ (D.coord ℓ) ∈ Γ(C̃, A_ρ)`, `t_ℓ := p^*a_ℓ`, `σ₀ : C̃ → Tot(L)` the zero section.

Statement: there are a nonempty open `V ⊆ C̃` and `λ ∈ Γ(p⁻¹V, O)` with `σ₀|_V^*λ = 1` and
`P_ℓ|_{p⁻¹V} = λ • t_ℓ|_{p⁻¹V}` for all `ℓ` (restriction written as pullback along `(p⁻¹V).ι`).

Proof (source Theorem 4.2 of the paper, the sentence "The affine tuple would therefore be a scalar multiple of
the seed tuple, with scalar value one at zero"): step 1 is `exists_seedCoordPullback_not_isZeroAt` (some `a_j` is
nonzero at some `x ∈ C̃`); the minors condition is rewritten with the seed tuple `a_ℓ` in place of
`p^*ρ^*(D.coord ℓ)` via the comparison `seedCoordPullbackIso` (`TotScalarRatio.sectionTensor_eq_of_hom_app`);
steps 2–4 are `TotScalarRatio.exists_scalar_ratio_of_minors_eq_zero_general` applied to `p`, `σ₀`, `A_ρ`
(`restrictToZeroSection` is definitionally `TotScalarRatio.zeroSectionComparison` applied to `σ₀^*P`). -/
theorem exists_tot_scalar_ratio_of_seed_minors_eq_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety}
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ)
      = seedCoordPullback f ρ (D.coord ℓ))
    (hminor : ∀ i j,
      sectionTensor (P i)
          (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
            (sectionPullbackAlong ρ.hom (D.coord j)))
        = sectionTensor (P j)
          (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
            (sectionPullbackAlong ρ.hom (D.coord i)))) :
    ∃ V : ρ.source.toScheme.Opens, (V : Set ρ.source.toScheme).Nonempty ∧
      ∃ lam : Γ(((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).toScheme, ⊤),
        ((AlgebraicGeometry.Scheme.zeroSection L.toModules).resLE
            ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) V
            (by
              change V ≤ (AlgebraicGeometry.Scheme.zeroSection L.toModules ≫
                (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) ⁻¹ᵁ V
              rw [AlgebraicGeometry.Scheme.zeroSection_comp]
              exact le_rfl)).appTop lam = 1 ∧
        ∀ ℓ,
          sectionPullbackAlong ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).ι (P ℓ)
            = (show ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).toScheme.ringCatSheaf.obj.obj
                  (Opposite.op ⊤) from lam) •
              sectionPullbackAlong ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).ι
                (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
                  (seedCoordPullback f ρ (D.coord ℓ))) := by
  obtain ⟨j, x, hx⟩ := exists_seedCoordPullback_not_isZeroAt (f := f) ρ
  have hminor' := TotScalarRatio.sectionTensor_eq_of_hom_app
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (seedCoordPullbackIso f ρ).hom P
    (fun ℓ => sectionPullbackAlong ρ.hom (D.coord ℓ)) (fun ℓ => seedCoordPullback f ρ (D.coord ℓ))
    (fun ℓ => seedCoordPullback_eq_iso_hom f ρ (D.coord ℓ)) hminor
  obtain ⟨V, hxV, lam, h1, h2⟩ := TotScalarRatio.exists_scalar_ratio_of_minors_eq_zero_general
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (AlgebraicGeometry.Scheme.zeroSection L.toModules)
    (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules) (seedBundlePullback f ρ).toModules P
    (fun ℓ => seedCoordPullback f ρ (D.coord ℓ)) hzero hminor' j x hx
  exact ⟨V, ⟨x, hxV⟩, lam, h1, h2⟩

end
