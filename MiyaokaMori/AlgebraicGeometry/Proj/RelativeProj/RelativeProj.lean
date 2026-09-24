import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedAffineAlgebra
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjMapToSpecZero

/-! # The relative Proj of a graded affine algebra

The **relative Proj** `S.relativeProj : Over X` of a graded quasi-coherent algebra `S` (`GradedAffineAlgebra`):
on the small affine Zariski site take the functor `U ↦ Proj S(U)` (Mathlib's `Proj` and `Proj.map`) together
with the natural transformation `Proj S(U) → U` (`Proj.toSpecZero` followed by `Spec(Γ(X,U) → S(U)_0)` and
`U ≅ Spec Γ(X,U)`), and glue with Mathlib's `RelativeGluingData`. The chart `S.projChart U : Proj S(U) ⟶ Proj_X S`
is an open immersion, `π⁻¹U` is the image of the chart, and the chart square is a pullback (Stacks 01NQ) — these
three facts come directly from Mathlib's gluing API.

Design:
* Mathlib's affine site only has the basic-open arrows `D(f) ⊆ U`, where `S(D(f)) = S(U)_f` (`f` of degree `0`),
  so functoriality, naturality and the equifibered condition all reduce to the single algebraic fact "Proj
  commutes with localization at a degree-`0` element" (Stacks 01MX / 01N2). The relative Spec uses the same index
  category, so the charts of `Spec_X S` and `Proj_X S` are aligned.
* Functoriality `map_id` / `map_comp` follows from Mathlib's `Proj.map_id` / `Proj.map_comp` and
  `restrictGraded_refl/trans`.
* The irrelevant-ideal condition `restrict_irrelevant_le` follows from quasi-coherence and the graded
  decomposition. Naturality `projToOpen_naturality` uses `AlgebraicGeometry.Proj.proj_map_toSpecZero`. The equifibered
  condition `projNatTrans_equifibered` is checked on the affine charts `D₊(s)` of `Proj S(V)` (Mathlib's
  `Scheme.isPullback_of_openCover`), where it becomes the pushout of rings `(S(U)_{(s)})₀ = (S(V)_{(s)})₀[1/f]`
  (`HomogeneousLocalization.Away.isLocalization_of_isLocalizationAway`, in this file).

Source: Stacks 01NM–01NS (constructions.tex, relative Proj via glueing); the construction `Y_k^GG = Proj_C 𝒮` of
§2 of the paper.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ)

theorem val_fromZeroRingHom' (x : Submonoid A) (a : 𝒜 0) :
    (fromZeroRingHom 𝒜 x a).val = Localization.mk (a : A) 1 := rfl

/-- `Away.map φ s` sends `a/1` to `φ a / 1`. -/
theorem Away.map_fromZeroRingHom (s : A) (a : 𝒜 0) :
    Away.map φ s (fromZeroRingHom 𝒜 _ a) = fromZeroRingHom ℬ _ (φ.gradedZeroRingHom a) := by
  apply val_injective
  change val (HomogeneousLocalization.map φ _ (HomogeneousLocalization.mk ⟨0, a, 1, one_mem _⟩)) =
    val (HomogeneousLocalization.mk ⟨0, φ.gradedAddHom 0 a, 1, one_mem _⟩)
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk]
  simp

variable {f : A} (hf : f ∈ 𝒜 0)

/-- **The algebraic core of "Proj commutes with localization at a degree-`0` element"** (the affine-chart version of
Stacks 01MX / 01N2): let `φ : A → B` be a graded homomorphism, `f ∈ A₀`, `B = A[1/f]` (along `φ`), and `s ∈ A_d`.
Then `(B_{(φ s)})₀ = (A_{(s)})₀[1/(f/1)]`, i.e. `Away.map φ s` is the localization at `f/1`.

Proof (verifying the three conditions of `IsLocalization`):
* the image `φ f/1` of `f/1` is invertible: `φ f` is invertible in `B`, and the degree-`0` component `u₀` of its
  inverse `u` satisfies `φ f · u₀ = (φ f · u)₀ = 1₀ = 1`;
* surjectivity: for `z = b/(φ s)^n` (`b ∈ B_{nd}`), `b·(φ f)^m = φ a'`; put `a := a'_{nd}`, then
  `φ a = (φ a')_{nd} = b (φ f)^m`, so `z·(f/1)^m = φ a/(φ s)^n = Away.map (a/s^n)`;
* kernel: if `a/s^n` and `b/s^m` have the same image, then `∃ k, (φ s)^k((φ s)^m φ a − (φ s)^n φ b) = 0`, i.e.
  `φ(s^k(s^m a − s^n b)) = 0`, hence `∃ N, f^N s^k(s^m a − s^n b) = 0`, and so
  `(f/1)^N·a/s^n = (f/1)^N·b/s^m`. -/
theorem Away.isLocalization_of_isLocalizationAway
    (hloc : letI := φ.toRingHom.toAlgebra; IsLocalization.Away f B)
    {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    letI := (Away.map φ s).toAlgebra
    IsLocalization.Away (fromZeroRingHom 𝒜 (Submonoid.powers s) ⟨f, hf⟩) (Away ℬ (φ s)) := by
  let _ := φ.toRingHom.toAlgebra
  let _ := (Away.map φ s).toAlgebra
  have hφf : φ f ∈ ℬ 0 := φ.map_mem hf
  have hs' : φ s ∈ ℬ d := φ.map_mem hs
  constructor; constructor
  · rintro ⟨r, n, rfl⟩
    rw [map_pow, RingHom.algebraMap_toAlgebra, Away.map_fromZeroRingHom]
    refine IsUnit.pow _ ?_
    obtain ⟨u, hu⟩ := IsLocalization.Away.algebraMap_isUnit (S := B) f
    have hfu : φ f * (DirectSum.decompose ℬ (↑u⁻¹ : B) 0 : B) = 1 := by
      rw [← DirectSum.coe_decompose_mul_of_left_mem_zero ℬ hφf]
      have h2 : φ f * (↑u⁻¹ : B) = 1 := by
        rw [show φ f = (u : B) from hu.symm]; exact Units.mul_inv u
      rw [h2, DirectSum.decompose_of_mem_same ℬ SetLike.GradedOne.one_mem]
    refine isUnit_iff_exists_inv.mpr
      ⟨fromZeroRingHom ℬ _ ⟨_, SetLike.coe_mem (DirectSum.decompose ℬ (↑u⁻¹ : B) 0)⟩, ?_⟩
    rw [← map_mul, ← map_one (fromZeroRingHom ℬ _)]
    congr 1
    exact Subtype.ext hfu
  · intro z
    obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ hs' z
    obtain ⟨m, a', ha'⟩ := IsLocalization.Away.surj (S := B) f b
    have hmem : b * φ f ^ m ∈ ℬ (n • d) := by
      have := SetLike.mul_mem_graded hb (SetLike.pow_mem_graded m hφf)
      simpa using this
    have ha : (DirectSum.decompose 𝒜 a' (n • d) : A) ∈ 𝒜 (n • d) := SetLike.coe_mem _
    have key : φ (DirectSum.decompose 𝒜 a' (n • d) : A) = b * φ f ^ m := by
      rw [GradedRingHom.map_directSumDecompose]
      change (DirectSum.decompose ℬ (algebraMap A B a') (n • d) : B) = _
      rw [← ha']
      exact DirectSum.decompose_of_mem_same ℬ hmem
    refine ⟨⟨Away.mk 𝒜 hs n _ ha, ⟨_, ⟨m, rfl⟩⟩⟩, ?_⟩
    apply val_injective
    simp only [RingHom.algebraMap_toAlgebra, map_pow, Away.map_fromZeroRingHom, Away.map_mk,
      val_mul, val_pow, Away.val_mk, val_fromZeroRingHom', Localization.mk_pow, Localization.mk_mul,
      key]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp
  · intro x y hxy
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs x
    obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hs y
    replace hxy := congr_arg val hxy
    simp only [RingHom.algebraMap_toAlgebra, Away.map_mk, Away.val_mk, Localization.mk_eq_mk_iff,
      Localization.r_iff_exists] at hxy
    obtain ⟨⟨_, k, rfl⟩, hc⟩ := hxy
    have h0 : algebraMap A B (s ^ k * (s ^ m * a) - s ^ k * (s ^ n * b)) = 0 := by
      rw [map_sub, sub_eq_zero]
      change φ _ = φ _
      simpa [map_mul, map_pow] using hc
    obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) B _).mp h0
    refine ⟨⟨_, N, rfl⟩, ?_⟩
    apply val_injective
    simp only [val_mul, val_pow, Away.val_mk, val_fromZeroRingHom', Localization.mk_pow,
      Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨⟨s ^ k, k, rfl⟩, ?_⟩
    simp only [one_pow, one_mul]
    linear_combination hN

end HomogeneousLocalization

namespace AlgebraicGeometry.Proj

open HomogeneousLocalization in
/-- The square of Mathlib's `awayι_comp_map` is a pullback: `D₊(φ s) ⊆ Proj ℬ` is the preimage of `D₊(s) ⊆ Proj 𝒜`
along `Proj.map φ` (`map_preimage_basicOpen`), and both vertical edges are open immersions
(`IsOpenImmersion.isPullback`). -/
theorem isPullback_awayι_map {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜]
    [GradedRing ℬ] (φ : 𝒜 →+*ᵍ ℬ)
    (hφ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map φ)
    {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map φ s))) (awayι ℬ (φ s) (φ.2 hs) hi)
      (awayι 𝒜 s hs hi) (map φ hφ) :=
  IsOpenImmersion.isPullback _ _ _ _ (awayι_comp_map φ hφ hi s hs)
    (by rw [opensRange_awayι, opensRange_awayι, map_preimage_basicOpen])

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- The restriction map satisfies the hypothesis of `Proj.map`: `S(U)_+ ⊆ S(V)_+ · S(U)` (`U = D(f) ⊆ V`).

Proof: choose `f` with `U = D_V(f)`. By `AffineAlgebra.isLocalization_basicOpen`, `S(U) = S(V)[1/f]`; for
`x ∈ S(U)_d` (`d > 0`) take `n` and `y ∈ S(V)` with `f^n·x = res y`; `res` preserves the grading, so
`res(y_d) = (f^n x)_d = f^n x` (`y_d` the degree-`d` component of `y`); `f` is invertible in `S(U)`, so
`x = f^{-n}·res(y_d)` lies in the ideal generated by `res(S(V)_+)`. -/
theorem restrict_irrelevant_le {U V : X.AffineZariskiSite} (h : U ≤ V) :
    HomogeneousIdeal.irrelevant (S.grading U) ≤
      (HomogeneousIdeal.irrelevant (S.grading V)).map (S.restrictGraded h) := by
  have hex : ∃ f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens := h
  obtain ⟨f, hf⟩ := hex
  obtain rfl : V.basicOpen f = U := Subtype.ext hf
  rw [HomogeneousIdeal.irrelevant_le]
  intro d hd x hx
  have hx' : x ∈ S.grading (V.basicOpen f) d := hx
  show x ∈ Ideal.map (S.restrictGraded h) (HomogeneousIdeal.irrelevant (S.grading V)).toIdeal
  let _ := (S.toAffineAlgebra.restrict (V.basicOpen_le f)).toAlgebra
  have hloc : IsLocalization.Away (S.toAffineAlgebra.unitHom V f)
      (S.toAffineAlgebra.sections (V.basicOpen f)) :=
    S.toAffineAlgebra.isLocalization_basicOpen V f
  obtain ⟨n, y, hy⟩ := IsLocalization.Away.surj (S.toAffineAlgebra.unitHom V f) x
  have hy' : x * S.restrictGraded h (S.toAffineAlgebra.unitHom V f) ^ n = S.restrictGraded h y := hy
  have hu : S.restrictGraded h (S.toAffineAlgebra.unitHom V f) ∈ S.grading (V.basicOpen f) 0 :=
    (S.restrictGraded h).map_mem (S.unit_mem V f)
  have hunit : IsUnit (S.restrictGraded h (S.toAffineAlgebra.unitHom V f)) :=
    IsLocalization.Away.algebraMap_isUnit (S.toAffineAlgebra.unitHom V f)
  have hmem : x * S.restrictGraded h (S.toAffineAlgebra.unitHom V f) ^ n ∈
      S.grading (V.basicOpen f) d := by
    have h1 := SetLike.pow_mem_graded n hu
    have h2 := SetLike.mul_mem_graded hx' h1
    simpa using h2
  have key : S.restrictGraded h ((DirectSum.decompose (S.grading V) y d : _)) =
      x * S.restrictGraded h (S.toAffineAlgebra.unitHom V f) ^ n := by
    rw [GradedRingHom.map_directSumDecompose, ← hy', DirectSum.decompose_of_mem_same _ hmem]
  have hyd : S.restrictGraded h ((DirectSum.decompose (S.grading V) y d : _)) ∈
      Ideal.map (S.restrictGraded h) (HomogeneousIdeal.irrelevant (S.grading V)).toIdeal :=
    Ideal.mem_map_of_mem _
      (HomogeneousIdeal.mem_irrelevant_of_mem _ hd (SetLike.coe_mem _))
  rw [key] at hyd
  have hfin := Ideal.mul_mem_right (↑(hunit.pow n).unit⁻¹ : S.toAffineAlgebra.sections (V.basicOpen f))
    _ hyd
  rwa [mul_assoc, IsUnit.mul_val_inv, mul_one] at hfin

private theorem proj_map_congr {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
    {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst e; rfl

/-- The functor `U ↦ Proj S(U)`. -/
def projFunctor : X.AffineZariskiSite ⥤ Scheme.{u} where
  obj U := Proj (S.grading U)
  map {U V} f := Proj.map (S.restrictGraded (leOfHom f)) (S.restrict_irrelevant_le (leOfHom f))
  map_id U := by
    rw [proj_map_congr (S.restrictGraded_refl U) _ (by simp)]
    exact Proj.map_id
  map_comp {U V W} f g := by
    have h := Proj.map_comp (S.restrictGraded (leOfHom g)) (S.restrictGraded (leOfHom f))
      (S.restrict_irrelevant_le (leOfHom g)) (S.restrict_irrelevant_le (leOfHom f))
    rw [← h]
    exact proj_map_congr (S.restrictGraded_trans (leOfHom f) (leOfHom g)) _ _

/-- The structure morphism `Proj S(U) → U` of a chart. -/
def projToOpen (U : X.AffineZariskiSite) : Proj (S.grading U) ⟶ U.toOpens.toScheme :=
  Proj.toSpecZero (S.grading U) ≫ Spec.map (CommRingCat.ofHom (S.unitZero U)) ≫ U.2.isoSpec.inv

/-- Naturality: `Proj.map` is compatible with the structure morphisms to the base.
Proof: both sides pass through `Spec Γ(X,U) → Spec Γ(X,V)`; use the compatibility of `Proj.map` with `toSpecZero`
(`MiyaokaMori.WeightedJets.proj_map_toSpecZero`) and `AffineAlgebra.restrict_unitHom`. -/
theorem projToOpen_naturality {U V : X.AffineZariskiSite} (h : U ≤ V) :
    S.projFunctor.map (homOfLE h) ≫ S.projToOpen V =
      S.projToOpen U ≫ X.homOfLE (AffineZariskiSite.toOpens_mono h) := by
  have h1 := AlgebraicGeometry.Proj.proj_map_toSpecZero (S.restrictGraded h) (S.restrict_irrelevant_le h)
  have h2 : Spec.map (CommRingCat.ofHom (S.restrictGraded h).gradedZeroRingHom) ≫
        Spec.map (CommRingCat.ofHom (S.unitZero V)) =
      Spec.map (CommRingCat.ofHom (S.unitZero U)) ≫
        Spec.map (X.presheaf.map (homOfLE (AffineZariskiSite.toOpens_mono h)).op) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact S.toAffineAlgebra.restrict_unitHom h r
  have h3 : Spec.map (X.presheaf.map (homOfLE (AffineZariskiSite.toOpens_mono h)).op) ≫
        V.2.isoSpec.inv = U.2.isoSpec.inv ≫ X.homOfLE (AffineZariskiSite.toOpens_mono h) :=
    (AffineZariskiSite.restrictIsoSpec X).inv.naturality (homOfLE h)
  show Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) ≫
      (Proj.toSpecZero (S.grading V) ≫ Spec.map (CommRingCat.ofHom (S.unitZero V)) ≫
        V.2.isoSpec.inv) =
    (Proj.toSpecZero (S.grading U) ≫ Spec.map (CommRingCat.ofHom (S.unitZero U)) ≫
        U.2.isoSpec.inv) ≫ X.homOfLE (AffineZariskiSite.toOpens_mono h)
  rw [reassoc_of% h1, reassoc_of% h2, h3]
  simp only [Category.assoc]

/-- The natural transformation `Proj S(U) → U`. -/
def projNatTrans :
    S.projFunctor ⟶ (AffineZariskiSite.directedCover X).functorOfLocallyDirected where
  app U := S.projToOpen U
  naturality _ _ f := S.projToOpen_naturality (leOfHom f)

/-- Equifibered (the basic-open case of Stacks 01NO / 01N2): for `U = D_V(f)`, `Proj S(U) = Proj S(V) ×_V U`.

Proof: paste the square vertically into a square over `Spec Γ(U) → Spec Γ(V)` (the layer `U ≅ Spec Γ(U)` is a
square of isomorphisms), then check on the affine charts `D₊(s)` of `Proj S(V)` (`Scheme.isPullback_of_openCover`):
on a chart the square is `Spec (S(U)_{(s)}) → Spec (S(V)_{(s)})` over `Spec Γ(U) → Spec Γ(V)`, which is `Spec` of a
pushout of rings (`isPullback_SpecMap_of_isPushout` + `CommRingCat.isPushout_of_isLocalization`), with algebraic core
`HomogeneousLocalization.Away.isLocalization_of_isLocalizationAway`: `(S(U)_{(s)})₀ = (S(V)_{(s)})₀[1/f]`. The
correspondence between charts and preimages is `Proj.isPullback_awayι_map`. -/
theorem projNatTrans_equifibered : S.projNatTrans.Equifibered := by
  intro U V g
  have h : U ≤ V := leOfHom g
  change IsPullback (Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h)) (S.projToOpen U)
    (S.projToOpen V) (X.homOfLE (AffineZariskiSite.toOpens_mono h))
  have hex : ∃ f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens := h
  obtain ⟨f, hf⟩ := hex
  obtain rfl : V.basicOpen f = U := Subtype.ext hf
  set res := X.presheaf.map (homOfLE (AffineZariskiSite.toOpens_mono h)).op with hres
  have hbot : IsPullback (Spec.map res) (V.basicOpen f).2.isoSpec.inv V.2.isoSpec.inv
      (X.homOfLE (AffineZariskiSite.toOpens_mono h)) :=
    IsPullback.of_vert_isIso ⟨(AffineZariskiSite.restrictIsoSpec X).inv.naturality (homOfLE h)⟩
  have htop : IsPullback (Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h))
      (Proj.toSpecZero (S.grading (V.basicOpen f)) ≫
        Spec.map (CommRingCat.ofHom (S.unitZero (V.basicOpen f))))
      (Proj.toSpecZero (S.grading V) ≫ Spec.map (CommRingCat.ofHom (S.unitZero V)))
      (Spec.map res) := by
    refine Scheme.isPullback_of_openCover _ _ _ _ (Proj.affineOpenCover (S.grading V)).openCover ?_
    rintro ⟨n, s, hs⟩
    have hd : 0 < (n : ℕ) := n.pos
    have hch := Proj.isPullback_awayι_map (S.restrictGraded h) (S.restrict_irrelevant_le h) hd s hs
    -- the big square: Spec of a pushout
    have hbig : IsPullback (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
          (S.restrictGraded h) s)))
        (Proj.awayι (S.grading (V.basicOpen f)) (S.restrictGraded h s) ((S.restrictGraded h).2 hs) hd ≫
          Proj.toSpecZero (S.grading (V.basicOpen f)) ≫
            Spec.map (CommRingCat.ofHom (S.unitZero (V.basicOpen f))))
        (Proj.awayι (S.grading V) s hs hd ≫ Proj.toSpecZero (S.grading V) ≫
          Spec.map (CommRingCat.ofHom (S.unitZero V)))
        (Spec.map res) := by
      rw [Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
      apply isPullback_SpecMap_of_isPushout
      let _ : Algebra Γ(X, V.toOpens) Γ(X, (V.basicOpen f).toOpens) := res.hom.toAlgebra
      let _ : Algebra (HomogeneousLocalization.Away (S.grading V) s)
          (HomogeneousLocalization.Away (S.grading (V.basicOpen f)) (S.restrictGraded h s)) :=
        (HomogeneousLocalization.Away.map (S.restrictGraded h) s).toAlgebra
      have hloc1 : IsLocalization.Away f Γ(X, (V.basicOpen f).toOpens) :=
        V.2.isLocalization_of_eq_basicOpen f (homOfLE (AffineZariskiSite.toOpens_mono h)) rfl
      let fR : Γ(X, V.toOpens) →+* HomogeneousLocalization.Away (S.grading V) s :=
        (HomogeneousLocalization.fromZeroRingHom (S.grading V) _).comp (S.unitZero V)
      let fₘ : Γ(X, (V.basicOpen f).toOpens) →+*
          HomogeneousLocalization.Away (S.grading (V.basicOpen f)) (S.restrictGraded h s) :=
        (HomogeneousLocalization.fromZeroRingHom (S.grading (V.basicOpen f)) _).comp
          (S.unitZero (V.basicOpen f))
      have hloc2 : IsLocalization ((Submonoid.powers f).map fR)
          (HomogeneousLocalization.Away (S.grading (V.basicOpen f)) (S.restrictGraded h s)) := by
        rw [Submonoid.map_powers]
        exact HomogeneousLocalization.Away.isLocalization_of_isLocalizationAway (S.restrictGraded h)
          (S.unit_mem V f) (S.toAffineAlgebra.isLocalization_basicOpen V f) hs
      have H : fₘ.comp (algebraMap _ _) = (algebraMap _ _).comp fR := by
        refine RingHom.ext fun r => ?_
        change HomogeneousLocalization.fromZeroRingHom _ _ (S.unitZero (V.basicOpen f) (res r)) =
          HomogeneousLocalization.Away.map (S.restrictGraded h) s
            (HomogeneousLocalization.fromZeroRingHom _ _ (S.unitZero V r))
        rw [HomogeneousLocalization.Away.map_fromZeroRingHom]
        congr 1
        exact Subtype.ext (S.toAffineAlgebra.restrict_unitHom h r).symm
      exact CommRingCat.isPushout_of_isLocalization fR fₘ H (Submonoid.powers f)
    have hiso : IsPullback (pullback.snd (Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h))
        (Proj.awayι (S.grading V) s hs hd)) hch.flip.isoPullback.inv (𝟙 _)
        (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map (S.restrictGraded h) s))) :=
      IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, hch.flip.isoPullback_inv_snd]⟩
    have := hiso.paste_vert hbig
    rw [Category.id_comp, IsPullback.isoPullback_inv_fst_assoc] at this
    exact this
  have := htop.paste_vert hbot
  simpa only [projToOpen, Category.assoc] using this

/-- The gluing data. -/
def projGluingData : (AffineZariskiSite.directedCover X).RelativeGluingData where
  functor := S.projFunctor
  natTrans := S.projNatTrans
  equifibered := S.projNatTrans_equifibered

instance projGluingData_isLocallyDirected :
    (S.projGluingData.functor ⋙ Scheme.forget).IsLocallyDirected :=
  Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..

/-- **The relative Proj** `Proj_X S → X`. -/
def relativeProj : Over X := Over.mk S.projGluingData.toBase

/-- The chart `Proj S(U) → Proj_X S`. -/
def projChart (U : X.AffineZariskiSite) : Proj (S.grading U) ⟶ S.relativeProj.left :=
  colimit.ι S.projGluingData.functor U

instance projChart_isOpenImmersion (U : X.AffineZariskiSite) :
    IsOpenImmersion (S.projChart U) := by
  change IsOpenImmersion (colimit.ι S.projGluingData.functor U)
  infer_instance

@[reassoc (attr := simp)]
theorem projChart_hom (U : X.AffineZariskiSite) :
    S.projChart U ≫ S.relativeProj.hom = S.projToOpen U ≫ U.toOpens.ι := by
  change colimit.ι S.projGluingData.functor U ≫ S.projGluingData.toBase = _
  rw [S.projGluingData.ι_toBase U]
  rfl

@[reassoc]
theorem map_projChart {U V : X.AffineZariskiSite} (h : U ≤ V) :
    S.projFunctor.map (homOfLE h) ≫ S.projChart V = S.projChart U :=
  colimit.w S.projGluingData.functor (homOfLE h)

/-- `π⁻¹(U)` is the image of the chart (the set-theoretic level of Stacks 01NQ). -/
theorem proj_preimage_eq_opensRange (U : X.AffineZariskiSite) :
    S.relativeProj.hom ⁻¹ᵁ U.toOpens = (S.projChart U).opensRange := by
  have h := S.projGluingData.toBase_preimage_eq_opensRange_ι U
  rw [← show S.projGluingData.toBase ⁻¹ᵁ ((AffineZariskiSite.directedCover X).f U).opensRange =
    S.relativeProj.hom ⁻¹ᵁ U.toOpens from by
      congr 1
      exact Scheme.Opens.opensRange_ι U.toOpens]
  exact h

/-- The chart square is a pullback: the restriction of `Proj_X S` to `U` is `Proj S(U)` (Stacks 01NQ). -/
theorem projChart_isPullback (U : X.AffineZariskiSite) :
    IsPullback (S.projToOpen U) (S.projChart U) U.toOpens.ι S.relativeProj.hom :=
  S.projGluingData.isPullback_natTrans_ι_toBase U

/-- The charts jointly cover. -/
theorem exists_projChart_mem (x : S.relativeProj.left) :
    ∃ (U : X.AffineZariskiSite) (y : Proj (S.grading U)), S.projChart U y = x :=
  Scheme.IsLocallyDirected.ι_jointly_surjective S.projGluingData.functor x

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
