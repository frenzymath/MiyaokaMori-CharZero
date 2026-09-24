import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ProjectiveLinePrincipalDivisorDegreeZero
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SchemeImageIntegral
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineStdChartRange

/-! # A proper birational model of a curve dominating `P¹`

A one-dimensional proper variety `X` over a field `K` admits a one-dimensional `K`-variety `Y`
with a proper birational `K`-morphism `p : Y → X` and a proper dominant `K`-morphism
`q : Y → P¹_K`. Instead of constructing `U → A¹ → P¹` and taking the closure of its graph, the
proof spreads out `Spec K(X) → P¹` (given by a transcendental element `f`) to a rational map `g`
with Mathlib's `PartialMap.ofFromSpecStalk` (Stacks 0BX6) and lets `Y` be the scheme-theoretic
image of `(ι_U, g) : U → X ×_K P¹`; dominance of `q` follows because `Spec.map ψ` sends the point
of `Spec K(X)` to the generic point `(0)` of `Spec K[t]` (`ψ` is injective), which replaces the
dichotomy of the original argument.

Sources: Stacks 02RQ (1)(2) and its proof (closure of the graph), 01W6 (2), 0A21 (6), and the
dichotomy "`q(Y)` is a closed point or `q` is dominant" in the proof of Stacks 02RU;
Mathlib `Scheme.PartialMap.ofFromSpecStalk` (Stacks 0BX6) and `Scheme.Hom.image`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

/- The standard chart of P¹ uses the standard grading of k[x₀, x₁] (given by `letI` inside the
definition of `ProjectiveSpace`); make it a local instance as in `ProjectiveLineStandardChart`. -/
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K]

/-- `X.fromSpecStalk x ≫ f = Spec.map (ΓSpecIso.inv ≫ f.appTop ≫ germ ⊤ x)` for `f : X ⟶ Spec R`. -/
theorem AlgebraicGeometry.Scheme.fromSpecStalk_comp_toSpec {X : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) (x : X) :
    X.fromSpecStalk x ≫ f =
      Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial) := by
  calc X.fromSpecStalk x ≫ f
      = X.fromSpecStalk x ≫ (f ≫ (Spec R).toSpecΓ) ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
        rw [Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
    _ = (X.fromSpecStalk x ≫ X.toSpecΓ) ≫ Spec.map f.appTop ≫ Spec.map (Scheme.ΓSpecIso R).inv := by
        rw [Scheme.toSpecΓ_naturality]; simp only [Category.assoc]
    _ = _ := by
        rw [Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp, Category.assoc]

/-- The standard chart `Spec K[t] ⟶ P¹_K` (`t ↦ x₁/x₀`), as a morphism out of `Spec` of the polynomial
ring `MvPolynomial (ULift (Fin 1)) K`: `Spec ψ ≫ Proj.awayι` with `ψ = stdChartRingHom`
(`ProjectiveLineStandardChart`). This is `stdChart` precomposed with `AffineSpace.SpecIso.inv`. -/
def ProjectiveLine.specChart (K : Type u) [Field K] :
    Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) K)) ⟶ ProjectiveLine K :=
  Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom K)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X K 0)) Nat.one_pos

/-- The chart ring map `ψ : k[x₀,x₁]_(x₀) → k[t]` is an isomorphism (`stdChartRingHom_eq`). Not a global
instance; use `haveI`. -/
theorem ProjectiveLine.isIso_ofHom_stdChartRingHom :
    IsIso (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom K)) := by
  rw [ProjectiveLine.stdChartRingHom_eq]
  exact (ProjectiveLine.stdChartRingEquiv K).toCommRingCatIso.isIso_hom

/-- `specChart` is an open immersion: `Spec` of a ring isomorphism followed by `Proj.awayι`
(the open immersion `D₊(x₀) ⊆ P¹`). Not registered as a global instance; use `haveI`. -/
theorem ProjectiveLine.specChart_isOpenImmersion : IsOpenImmersion (ProjectiveLine.specChart K) := by
  haveI := ProjectiveLine.isIso_ofHom_stdChartRingHom (K := K)
  haveI : IsIso (Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom K))) := inferInstance
  have h1 : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom K)) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (1 + 1)) K) (MvPolynomial.X 0)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X K 0)) Nat.one_pos) :=
    inferInstance
  exact h1

theorem ProjectiveLine.specChart_comp_toSpecBase :
    ProjectiveLine.specChart K ≫ ProjectiveSpace.toSpecBase 1 K =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin 1)) (R := K))) :=
  (Category.assoc _ _ _).trans (ProjectiveLine.specMap_stdChartRingHom_comp_awayι_comp_toSpecBase K)

/-- The chart `Spec K[t] → P¹` sends the generic point `(0)` to the generic point of `P¹`
(open immersions of irreducible schemes preserve generic points). -/
theorem ProjectiveLine.specChart_genericPoint :
    ProjectiveLine.specChart K (genericPoint _) = genericPoint (ProjectiveLine.variety K).toScheme := by
  haveI : IrreducibleSpace (ProjectiveLine K) :=
    irreducibleSpace_of_isIntegral (ProjectiveLine.variety K).toScheme
  haveI := ProjectiveLine.specChart_isOpenImmersion (K := K)
  exact genericPoint_eq_of_isOpenImmersion _

/-- A dominant morphism between irreducible schemes sends the generic point to the generic point. -/
theorem AlgebraicGeometry.Scheme.Hom.genericPoint_eq_of_isDominant {W W' : Scheme.{u}}
    [IrreducibleSpace W] [IrreducibleSpace W'] (q : W ⟶ W') [IsDominant q] :
    q (genericPoint W) = genericPoint W' := by
  have h1 := (genericPoint_spec W).image q.continuous
  rw [Set.image_univ, q.denseRange.closure_range] at h1
  exact h1.eq (genericPoint_spec _)

/-- A ring homomorphism out of a local ring whose maximal ideal is zero (i.e. a field) into a
nontrivial ring is injective. -/
theorem RingHom.injective_of_maximalIdeal_eq_bot {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [Nontrivial B] (f : A →+* B) (h : IsLocalRing.maximalIdeal A = ⊥) :
    Function.Injective f := by
  refine (RingHom.injective_iff_ker_eq_bot f).mpr (le_bot_iff.mp fun a ha => ?_)
  rw [← h, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have : IsUnit (f a) := hu.map f
  rw [RingHom.mem_ker.mp ha] at this
  exact not_isUnit_zero this

/-- If `j ≫ p` induces an isomorphism on the stalks at `u` and the stalks of `X` at `x` and of `Y`
at `y` have zero maximal ideal (they are fields), then the stalk map of `p` at `y`, transported
along `p y = x`, is bijective. -/
theorem AlgebraicGeometry.Scheme.Hom.stalkMap_bijective_of_comp_isIso {U Y X : Scheme.{u}}
    (j : U ⟶ Y) (p : Y ⟶ X) (u : U) (y : Y) (x : X) (hy : j u = y) (hx : p y = x)
    (hX : IsLocalRing.maximalIdeal (X.presheaf.stalk x) = ⊥)
    (hY : IsLocalRing.maximalIdeal (Y.presheaf.stalk y) = ⊥)
    [hiso : IsIso ((j ≫ p).stalkMap u)] :
    Function.Bijective
      ((X.presheaf.stalkCongr (Inseparable.of_eq hx.symm)).hom ≫ p.stalkMap y).hom := by
  subst hy hx
  have hiso' : IsIso (p.stalkMap (j u) ≫ j.stalkMap u) := by
    rw [← Scheme.Hom.stalkMap_comp]; exact hiso
  have hbij : Function.Bijective (p.stalkMap (j u) ≫ j.stalkMap u).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [CommRingCat.hom_comp, RingHom.coe_comp] at hbij
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  refine ⟨(p.stalkMap (j u)).hom.injective_of_maximalIdeal_eq_bot hX, fun b => ?_⟩
  obtain ⟨a, ha⟩ := hbij.2 ((j.stalkMap u).hom b)
  exact ⟨a, (j.stalkMap u).hom.injective_of_maximalIdeal_eq_bot hY ha⟩


/-- A one-dimensional proper variety has a proper birational model `p : Y → X` together with a
proper dominant morphism `q : Y → P¹`.

Proof (Stacks 02RQ (1)(2) with the graph closure taken as a scheme-theoretic image):
1. `dim X = trdeg_K K(X)` (Stacks 0A21(6), `Variety.topologicalKrullDim_eq_trdeg`), so `trdeg = 1 ≠ 0`
   and there is `f ∈ K(X)` transcendental over `K`.
2. `ψ := aeval f : K[t] → K(X)` is injective; `φ := Spec ψ ≫ specChart : Spec K(X) → P¹` is a
   `K`-morphism (`specChart_comp_toSpecBase`, `fromSpecStalk_comp_toSpec`).
3. `φ` spreads out to a partial map `g : X ⇢ P¹` defined on a dense open `U ∋ η_X`
   (Mathlib `PartialMap.ofFromSpecStalk`, Stacks 0BX6), with `g.fromSpecStalkOfMem = φ`.
4. `Y :=` scheme-theoretic image of `ℓ = (ι_U, g.hom) : U → X ×_K P¹`; `Y` is integral
   (`isIntegral_image`; `ℓ` is quasi-compact since `X` is noetherian), `ι : Y → X ×_K P¹` is a closed
   immersion, `p := ι ≫ fst`, `q := ι ≫ snd`, and `j := ℓ.toImage : U → Y` is dominant with
   `j ≫ p = ι_U`, `j ≫ q = g.hom`.
5. `p` is proper (closed immersion ≫ base change of the proper `P¹ → Spec K`), hence `Y` is proper over
   `K`, hence `q` is proper (`IsProper.of_comp`, `P¹ → Spec K` separated; Stacks 01W6(2)). `Y` is
   separated and of finite type over `K` as a closed subscheme of `X ×_K P¹`.
6. Generic points: `j η_U = η_Y` (`j` dominant), `ι_U η_U = η_X`, so `p η_Y = η_X`.
   `q η_Y = g.hom η_U = φ(closed point) = specChart (Spec ψ (pt))`; `Spec ψ (pt)` is the prime
   `ψ⁻¹(0) = (0)`, the generic point of `Spec K[t]`, and open immersions preserve generic points, so
   `q η_Y = η_{P¹}` (this replaces the "closed point or dominant" dichotomy of the 02RU proof).
7. `K(X) → K(Y) → K(U)` composes to the stalk map of the open immersion `ι_U`, an isomorphism; both maps
   are injective (field homomorphisms), so `K(X) → K(Y)` is bijective and `[K(Y):K(X)] = 1`.
8. `dim Y = trdeg_K K(Y) = trdeg_K K(X) = 1` (0A21(6) again; `K(X) ≅ K(Y)` is a `K`-algebra
   isomorphism because `p` is a `K`-morphism). -/
theorem Variety.exists_proper_birational_dominant_projectiveLine (X : Variety K)
    [IsProper (X.toScheme ↘ Spec (CommRingCat.of K))] (hX : X.toScheme.dimension = 1) :
    ∃ (Y : Variety K) (_ : Y.toScheme.dimension = 1)
      (p : Y.toScheme ⟶ X.toScheme) (_ : p.IsOver (Spec (CommRingCat.of K))) (_ : IsProper p)
      (hp : p.base (genericPoint Y.toScheme) = genericPoint X.toScheme)
      (_ : letI : Algebra X.toScheme.functionField Y.toScheme.functionField :=
          ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
            p.stalkMap (genericPoint Y.toScheme)).hom.toAlgebra
        Module.finrank X.toScheme.functionField Y.toScheme.functionField = 1)
      (q : Y.toScheme ⟶ (ProjectiveLine.variety K).toScheme)
      (_ : q.IsOver (Spec (CommRingCat.of K))) (_ : IsProper q),
      q.base (genericPoint Y.toScheme) = genericPoint (ProjectiveLine.variety K).toScheme := by
  classical
  -- Step 1: `K(X)` is transcendental over `K` since `dim X = trdeg_K K(X) = 1` (Stacks 0A21(6)).
  letI algK : Algebra K X.toScheme.functionField :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (X.toScheme ↘ Spec (CommRingCat.of K)).appTop ≫
      X.toScheme.presheaf.germ ⊤ (genericPoint X.toScheme) (by simp)).hom.toAlgebra
  have hdimX : (Algebra.trdeg K X.toScheme.functionField).toNat = 1 := by
    obtain ⟨h1, -⟩ := Variety.topologicalKrullDim_eq_trdeg X
    unfold Scheme.dimension at hX
    rw [h1] at hX
    simpa using hX
  have htr : Algebra.Transcendental K X.toScheme.functionField := by
    rw [← trdeg_ne_zero_iff]
    intro h0
    rw [h0] at hdimX
    simp at hdimX
  obtain ⟨f, hf⟩ := Algebra.transcendental_def.mp htr
  -- Step 2: `ψ : K[t] → K(X)`, `t ↦ f`, is injective.
  let ψ : MvPolynomial (ULift.{u} (Fin 1)) K →ₐ[K] X.toScheme.functionField :=
    MvPolynomial.aeval (fun _ => f)
  have hψ : Function.Injective ψ := by
    rw [← algebraicIndependent_iff_injective_aeval]
    exact algebraicIndependent_unique_type_iff.mpr hf
  -- Step 3: the `K`-morphism `φ : Spec K(X) ⟶ P¹` given by `f`.
  let φ : Spec X.toScheme.functionField ⟶ (ProjectiveLine.variety K).toScheme :=
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ProjectiveLine.specChart K
  have hφ : φ ≫ ((ProjectiveLine.variety K).toScheme ↘ Spec (CommRingCat.of K)) =
      X.toScheme.fromSpecStalk (genericPoint X.toScheme) ≫ (X.toScheme ↘ Spec (CommRingCat.of K)) := by
    rw [Scheme.fromSpecStalk_comp_toSpec]
    show Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ ProjectiveLine.specChart K ≫
      ProjectiveSpace.toSpecBase 1 K = _
    rw [ProjectiveLine.specChart_comp_toSpecBase, ← Spec.map_comp]
    congr 1
    ext c
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ψ, MvPolynomial.aeval_C]
    rfl
  -- Step 4: spread `φ` out to a partial map `g : X ⇢ P¹` (Mathlib, Stacks 0BX6).
  let g : X.toScheme.PartialMap (ProjectiveLine.variety K).toScheme :=
    Scheme.PartialMap.ofFromSpecStalk (X.toScheme ↘ Spec (CommRingCat.of K))
      ((ProjectiveLine.variety K).toScheme ↘ Spec (CommRingCat.of K)) φ hφ
  have hηU : genericPoint X.toScheme ∈ g.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ φ hφ
  have hgφ : g.fromSpecStalkOfMem hηU = φ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ φ hφ
  have hgover : g.hom ≫ ((ProjectiveLine.variety K).toScheme ↘ Spec (CommRingCat.of K)) =
      g.domain.ι ≫ (X.toScheme ↘ Spec (CommRingCat.of K)) :=
    Scheme.PartialMap.ofFromSpecStalk_comp _ _ φ hφ
  -- Step 5: the graph `ℓ = (ι_U, g) : U ⟶ X ×_K P¹` and its scheme-theoretic image `Y`.
  let ℓ : (g.domain : Scheme.{u}) ⟶
      pullback (X.toScheme ↘ Spec (CommRingCat.of K))
        ((ProjectiveLine.variety K).toScheme ↘ Spec (CommRingCat.of K)) :=
    pullback.lift g.domain.ι g.hom hgover.symm
  haveI : IsNoetherian X.toScheme := by
    have : CompactSpace X.toScheme :=
      QuasiCompact.compactSpace_of_compactSpace (X.toScheme ↘ Spec (CommRingCat.of K))
    exact {}
  haveI : TopologicalSpace.NoetherianSpace g.domain :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace (g.domain : Set X.toScheme))
  haveI : QuasiCompact ℓ := inferInstance
  haveI : Nonempty g.domain := ⟨⟨_, hηU⟩⟩
  haveI : IsIntegral g.domain := isIntegral_of_isOpenImmersion g.domain.ι
  haveI : IsIntegral ℓ.image := ℓ.isIntegral_image
  let j : (g.domain : Scheme.{u}) ⟶ ℓ.image := ℓ.toImage
  let p : ℓ.image ⟶ X.toScheme := ℓ.imageι ≫ pullback.fst _ _
  let q : ℓ.image ⟶ (ProjectiveLine.variety K).toScheme := ℓ.imageι ≫ pullback.snd _ _
  have hjp : j ≫ p = g.domain.ι := by
    simp only [p, j, ← Category.assoc, ℓ.toImage_imageι, ℓ, pullback.lift_fst]
  have hjq : j ≫ q = g.hom := by
    simp only [q, j, ← Category.assoc, ℓ.toImage_imageι, ℓ, pullback.lift_snd]
  -- `K`-structure on `Y`; `p` and `q` are `K`-morphisms.
  letI : ℓ.image.Over (Spec (CommRingCat.of K)) := ⟨p ≫ (X.toScheme ↘ Spec (CommRingCat.of K))⟩
  haveI hpover : p.IsOver (Spec (CommRingCat.of K)) := ⟨rfl⟩
  haveI hqover : q.IsOver (Spec (CommRingCat.of K)) := ⟨by
    show q ≫ _ = p ≫ (X.toScheme ↘ Spec (CommRingCat.of K))
    simp only [q, p, Category.assoc, pullback.condition]⟩
  -- Step 6: `p`, `q` proper; `Y` is a `K`-variety.
  haveI : IsProper p := inferInstance
  haveI : IsProper (ℓ.image ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (IsProper (p ≫ (X.toScheme ↘ Spec (CommRingCat.of K))))
  haveI : IsProper q := by
    have : IsProper (q ≫ ((ProjectiveLine.variety K).toScheme ↘ Spec (CommRingCat.of K))) := by
      rw [hqover.1]; infer_instance
    exact IsProper.of_comp q ((ProjectiveLine.variety K).toScheme ↘ Spec (CommRingCat.of K))
  haveI : IsSeparated (ℓ.image ↘ Spec (CommRingCat.of K)) := inferInstance
  haveI : IsOfFiniteType (ℓ.image ↘ Spec (CommRingCat.of K)) := {}
  let Yv : Variety K := { carrier := ℓ.image }
  -- Step 7: generic points.
  have hjη : j (genericPoint g.domain) = genericPoint ℓ.image :=
    j.genericPoint_eq_of_isDominant
  have hιη : g.domain.ι (genericPoint g.domain) = genericPoint X.toScheme :=
    genericPoint_eq_of_isOpenImmersion _
  have hp : p (genericPoint ℓ.image) = genericPoint X.toScheme := by
    rw [← hjη, ← Scheme.Hom.comp_apply, hjp, hιη]
  have hηU' : genericPoint g.domain = ⟨genericPoint X.toScheme, hηU⟩ :=
    g.domain.ι.isOpenEmbedding.injective hιη
  have hmaxX : IsLocalRing.maximalIdeal (X.toScheme.presheaf.stalk (genericPoint X.toScheme)) = ⊥ :=
    IsLocalRing.maximalIdeal_eq_bot (R := X.toScheme.functionField)
  have hq : q (genericPoint ℓ.image) = genericPoint (ProjectiveLine.variety K).toScheme := by
    rw [← hjη, ← Scheme.Hom.comp_apply, hjq, hηU']
    have h0 : g.domain.ι (g.domain.fromSpecStalkOfMem _ hηU (IsLocalRing.closedPoint _)) =
        genericPoint X.toScheme :=
      (congrArg (fun m : Spec (X.toScheme.presheaf.stalk (genericPoint X.toScheme)) ⟶ X.toScheme =>
          m (IsLocalRing.closedPoint _)) (Scheme.Opens.fromSpecStalkOfMem_ι g.domain _ hηU)).trans
        Scheme.fromSpecStalk_closedPoint
    have h0' : g.domain.fromSpecStalkOfMem _ hηU (IsLocalRing.closedPoint _) = ⟨_, hηU⟩ :=
      g.domain.ι.isOpenEmbedding.injective h0
    have h1 : (g.fromSpecStalkOfMem hηU) (IsLocalRing.closedPoint _) = g.hom ⟨_, hηU⟩ :=
      congrArg (fun z => g.hom z) h0'
    rw [← h1, hgφ]
    show (ProjectiveLine.specChart K)
      ((Spec.map (CommRingCat.ofHom ψ.toRingHom)) (IsLocalRing.closedPoint _)) = _
    rw [← ProjectiveLine.specChart_genericPoint]
    congr 1
    rw [genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap ψ.toRingHom
      (IsLocalRing.maximalIdeal (X.toScheme.presheaf.stalk (genericPoint X.toScheme))) = ⊥
    rw [hmaxX]
    exact Ideal.comap_bot_of_injective ψ.toRingHom hψ
  -- Step 8: `K(X) ≅ K(Y)`.
  have hmaxY : IsLocalRing.maximalIdeal (ℓ.image.presheaf.stalk (genericPoint ℓ.image)) = ⊥ :=
    IsLocalRing.maximalIdeal_eq_bot (R := ℓ.image.functionField)
  have hbij : Function.Bijective
      ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
        p.stalkMap (genericPoint ℓ.image)).hom := by
    haveI : IsIso ((j ≫ p).stalkMap (genericPoint g.domain)) := by rw [hjp]; infer_instance
    exact Scheme.Hom.stalkMap_bijective_of_comp_isIso j p _ _ _ hjη hp hmaxX hmaxY
  have hfin : letI : Algebra X.toScheme.functionField ℓ.image.functionField :=
        ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
          p.stalkMap (genericPoint ℓ.image)).hom.toAlgebra
      Module.finrank X.toScheme.functionField ℓ.image.functionField = 1 := by
    letI : Algebra X.toScheme.functionField ℓ.image.functionField :=
      ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
        p.stalkMap (genericPoint ℓ.image)).hom.toAlgebra
    let e : X.toScheme.functionField ≃ₐ[X.toScheme.functionField] ℓ.image.functionField :=
      AlgEquiv.ofBijective (Algebra.ofId _ _) hbij
    rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]
  -- Step 9: `dim Y = trdeg_K K(Y) = trdeg_K K(X) = 1`.
  have hdimY : Yv.toScheme.dimension = 1 := by
    letI algKY : Algebra K Yv.carrier.functionField :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (Yv.carrier ↘ Spec (CommRingCat.of K)).appTop ≫
        Yv.carrier.presheaf.germ ⊤ (genericPoint Yv.carrier) (by simp)).hom.toAlgebra
    have hcomm : ∀ c : K,
        ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
          p.stalkMap (genericPoint ℓ.image)).hom (algebraMap K X.toScheme.functionField c) =
        algebraMap K Yv.carrier.functionField c := by
      intro c
      have e1 : algebraMap K X.toScheme.functionField c =
          X.toScheme.presheaf.germ ⊤ (genericPoint X.toScheme) trivial
            ((X.toScheme ↘ Spec (CommRingCat.of K)).appTop
              ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)) := rfl
      have e2 : algebraMap K Yv.carrier.functionField c =
          ℓ.image.presheaf.germ ⊤ (genericPoint ℓ.image) trivial
            (p.appTop ((X.toScheme ↘ Spec (CommRingCat.of K)).appTop
              ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c))) := rfl
      have hmor : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
            (X.toScheme ↘ Spec (CommRingCat.of K)).appTop ≫
            X.toScheme.presheaf.germ ⊤ (genericPoint X.toScheme) trivial) ≫
          ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
            p.stalkMap (genericPoint ℓ.image)) =
          (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
            ((X.toScheme ↘ Spec (CommRingCat.of K)).appTop ≫ p.appTop) ≫
            ℓ.image.presheaf.germ ⊤ (genericPoint ℓ.image) trivial := by
        have e3 : X.toScheme.presheaf.germ ⊤ (genericPoint X.toScheme) trivial ≫
            (X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom =
            X.toScheme.presheaf.germ ⊤ (p (genericPoint ℓ.image)) trivial := by
          rw [TopCat.Presheaf.stalkCongr_hom]
          exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
        have e4 := Scheme.Hom.germ_stalkMap p ⊤ (genericPoint ℓ.image) trivial
        rw [Category.assoc, Category.assoc, reassoc_of% e3, e4]
        simp only [Category.assoc]
        rfl
      rw [e1, e2]
      exact congrArg (fun m => m.hom c) hmor
    let e : X.toScheme.functionField ≃ₐ[K] Yv.carrier.functionField :=
      AlgEquiv.ofBijective
        { toRingHom := ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
            p.stalkMap (genericPoint ℓ.image)).hom
          commutes' := hcomm } hbij
    have htr : Algebra.trdeg K Yv.carrier.functionField = Algebra.trdeg K X.toScheme.functionField :=
      e.trdeg_eq.symm
    obtain ⟨h1, -⟩ := Variety.topologicalKrullDim_eq_trdeg Yv
    show Scheme.dimension Yv.carrier = 1
    unfold Scheme.dimension
    rw [h1]
    simp [htr, hdimX]
  exact ⟨Yv, hdimY, p, hpover, inferInstance, hp, hfin, q, hqover, inferInstance, hq⟩

end
