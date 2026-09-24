import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.Stacks02qu
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineBundleSectionGermGenericNeZero
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # The zero-scheme cycle vanishes at points of coheight different from one

At a point of coheight `≠ 1`, the coefficient of the zero-scheme cycle `[Z(σ)]_d` of a nonzero section
`σ` of a line bundle is zero. Sources: Stacks 02QU; Krull's Hauptidealsatz (Stacks 00KV).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- (1) Local equation: if `e` is a frame of `L` on an affine open `U` (`r ↦ r • e` bijective) and
`σ|_U = f • e`, then the ideal of `idealSheafOfSection L σ` on `U` is `(f)`.

Proof: by definition the ideal is `span {φ(σ|_U) | φ ∈ Hom(Γ(L,U), Γ(X,U))}`. `⊆`:
`φ(σ|_U) = φ(f • e) = f · φ(e) ∈ (f)`. `⊇`: the bijection `r ↦ r • e` has a linear inverse `ψ` with
`ψ(σ|_U) = ψ(f • e) = f`, so `f` is one of the generators. -/
theorem idealSheafOfSection_ideal_eq_span_singleton
    {X : Scheme.{u}} (L : X.Modules) [L.IsLineBundle] (σ : (L.val.obj (op ⊤) : Type u))
    (U : X.affineOpens) (e : Γ(L, U.1))
    (hbij : Function.Bijective (fun r : Γ(X, U.1) => r • e)) (f : Γ(X, U.1))
    (hf : f • e = L.presheaf.map (homOfLE le_top).op (show Γ(L, ⊤) from σ)) :
    (idealSheafOfSection L σ).ideal U = Ideal.span {f} := by
  show Ideal.span (Set.range fun φ : Γ(L, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1) =>
    φ (L.presheaf.map (homOfLE le_top).op (show Γ(L, ⊤) from σ))) = Ideal.span {f}
  have hbij' : Function.Bijective (LinearMap.toSpanSingleton Γ(X, U.1) Γ(L, U.1) e) := hbij
  let ψ : Γ(L, U.1) ≃ₗ[Γ(X, U.1)] Γ(X, U.1) :=
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Γ(X, U.1) Γ(L, U.1) e) hbij').symm
  have hψ : ψ (L.presheaf.map (homOfLE le_top).op (show Γ(L, ⊤) from σ)) = f := by
    rw [← hf]
    exact (LinearEquiv.ofBijective _ hbij').symm_apply_apply f
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    show φ (L.presheaf.map (homOfLE le_top).op (show Γ(L, ⊤) from σ)) ∈ Ideal.span {f}
    rw [← hf, map_smul, smul_eq_mul]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.subset_span ⟨ψ.toLinearMap, hψ⟩

/-- (2) **The Krull Hauptidealsatz step**: let `U` be an affine open with `Γ(X, U)` a Noetherian domain,
`I(U) = (f)` with `f ≠ 0`, and `z ∈ U ∩ supp I` such that no other point of `supp I` specializes to `z`.
Then `coheight z = 1`.

Proof: `z = fromSpec 𝔭` (`range_fromSpec`), `coheight z = coheight 𝔭 = ht 𝔭` (Stacks 02I4,
`idealHeight_eq_coheight`). `𝔭 ⊇ (f)` (`mem_support_iff_of_mem`, `fromSpec_preimage_zeroLocus`). `𝔭` is a
minimal prime over `(f)`: if `(f) ⊆ 𝔮 ⊆ 𝔭` then `y := fromSpec 𝔮 ∈ U ∩ supp I` and `y ⤳ z`, so `y = z` by
hypothesis, and injectivity of `fromSpec` gives `𝔮 = 𝔭`. Krull's Hauptidealsatz
(`Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`) gives `ht 𝔭 ≤ 1`; in a domain
`ht 𝔭 = 0 ↔ 𝔭 = 0`, while `0 ≠ f ∈ 𝔭`, so `ht 𝔭 = 1`. -/
theorem coheight_eq_one_of_ideal_eq_span_singleton
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens)
    [IsNoetherianRing Γ(X, U.1)] [IsDomain Γ(X, U.1)]
    (f : Γ(X, U.1)) (hf0 : f ≠ 0) (hI : I.ideal U = Ideal.span {f})
    (z : X) (hzU : z ∈ U.1) (hz : z ∈ I.support)
    (hmax : ∀ y ∈ I.support, y ⤳ z → y = z) :
    Order.coheight z = 1 := by
  have hU : IsAffineOpen U.1 := U.2
  have hrange : ∀ q : Spec Γ(X, U.1), hU.fromSpec.base q ∈ U.1 := by
    intro q
    have : hU.fromSpec.base q ∈ Set.range hU.fromSpec := ⟨q, rfl⟩
    rwa [IsAffineOpen.range_fromSpec] at this
  obtain ⟨p, rfl⟩ : z ∈ Set.range hU.fromSpec.base := by
    have : z ∈ Set.range hU.fromSpec := by rw [IsAffineOpen.range_fromSpec]; exact hzU
    exact this
  rw [coheight_eq_of_isOpenImmersion, ← idealHeight_eq_coheight]
  have hsub : ∀ q : Spec Γ(X, U.1),
      hU.fromSpec.base q ∈ I.support ↔ Ideal.span {f} ≤ q.asIdeal := by
    intro q
    rw [I.mem_support_iff_of_mem (U := U) (hrange q), ← Set.mem_preimage,
      hU.fromSpec_preimage_zeroLocus]
    change ((I.ideal U : Set Γ(X, U.1)) ⊆ (q.asIdeal : Set Γ(X, U.1))) ↔ _
    rw [hI]
    exact SetLike.coe_subset_coe
  have hle : Ideal.span {f} ≤ p.asIdeal := (hsub p).mp hz
  have hmin : p.asIdeal ∈ (Ideal.span {f}).minimalPrimes := by
    refine ⟨⟨p.isPrime, hle⟩, ?_⟩
    intro q hq hqp
    let Q : Spec Γ(X, U.1) := ⟨q, hq.1⟩
    have hQ : hU.fromSpec.base Q ∈ I.support := (hsub Q).mpr hq.2
    have hspec : hU.fromSpec.base Q ⤳ hU.fromSpec.base p :=
      ((PrimeSpectrum.le_iff_specializes Q p).mp hqp).map hU.fromSpec.base.hom.continuous
    have heq : Q = p := hU.fromSpec.isOpenEmbedding.injective (hmax _ hQ hspec)
    exact (congrArg PrimeSpectrum.asIdeal heq).ge
  have h1 : p.asIdeal.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) p.asIdeal hmin
  have h0 : p.asIdeal.height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro hbot
    have hfp : f ∈ p.asIdeal := hle (Ideal.mem_span_singleton_self f)
    rw [hbot] at hfp
    exact hf0 (Ideal.mem_bot.mp hfp)
  rcases Order.le_one_iff.mp h1 with h | h
  · exact absurd h h0
  · exact h

/-- (3) The image `z` in `X` of the generic point `z′` of an irreducible component of the zero scheme
`Z(σ)` has `coheight z = 1`.

Proof: `z′` is maximal in `Z` (`isMax_of_mem_genericPoints`), and the closed immersion `ι` is an
embedding, so `z` is the only point of `supp I = range ι` specializing to `z`. Take an affine open
`W ∋ z` with a frame `e` of `L` (`exists_affine_frame_le`), `σ|_W = f • e`; `f ≠ 0`, since otherwise
`σ|_W = 0` and the germ of `σ` at the generic point `η ∈ W` would vanish, contradicting
`germ_genericPoint_ne_zero`. `Γ(X, W)` is a Noetherian domain (`X` integral and locally Noetherian,
`W ≠ ∅`), so `I(W) = (f)` by (1), and (2) gives `coheight z = 1`. -/
theorem coheight_subschemeι_eq_one_of_mem_genericPoints
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (σ : (L.val.obj (op ⊤) : Type u)) (hσ : σ ≠ 0)
    (z' : (idealSheafOfSection L σ).subscheme)
    (hgen : z' ∈ genericPoints (idealSheafOfSection L σ).subscheme) :
    Order.coheight ((idealSheafOfSection L σ).subschemeι.base z') = 1 := by
  have hmaxZ := AlgebraicGeometry.Intersection.isMax_of_mem_genericPoints _ z' hgen
  have hmax : ∀ y ∈ (idealSheafOfSection L σ).support,
      y ⤳ (idealSheafOfSection L σ).subschemeι.base z' →
        y = (idealSheafOfSection L σ).subschemeι.base z' := by
    intro y hy hspec
    have hy' : y ∈ Set.range (idealSheafOfSection L σ).subschemeι := by
      rw [Scheme.IdealSheafData.range_subschemeι]; exact hy
    obtain ⟨y', rfl⟩ := hy'
    have h1 : y' ⤳ z' :=
      (idealSheafOfSection L σ).subschemeι.isClosedEmbedding.isInducing.specializes_iff.mp hspec
    have h2 : z' ≤ y' := Scheme.le_iff_specializes.mpr h1
    have h3 : z' ⤳ y' := Scheme.le_iff_specializes.mp (hmaxZ h2)
    exact congrArg _ (h1.antisymm h3).eq
  obtain ⟨W, hW, -, hzW, e, he⟩ := Scheme.Modules.exists_affine_frame_le L
    (show (idealSheafOfSection L σ).subschemeι.base z' ∈ (⊤ : X.Opens) from trivial)
  have hbij := he W le_rfl
  obtain ⟨f, hf⟩ := hbij.2 (L.presheaf.map (homOfLE le_top).op (show Γ(L, ⊤) from σ))
  have hf' : f • (L.presheaf.map (homOfLE le_rfl).op e : Γ(L, W)) =
      L.presheaf.map (homOfLE le_top).op (show Γ(L, ⊤) from σ) := hf
  have hI : (idealSheafOfSection L σ).ideal ⟨W, hW⟩ = Ideal.span {f} :=
    idealSheafOfSection_ideal_eq_span_singleton L σ ⟨W, hW⟩ _ hbij f hf'
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : Nonempty W := ⟨⟨_, hzW⟩⟩
  have : IsDomain Γ(X, W) := IsIntegral.component_integral W
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hf'
    have hηW : genericPoint X ∈ W :=
      ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr ⟨_, Set.mem_univ _, hzW⟩
    apply Scheme.Modules.germ_genericPoint_ne_zero L σ hσ
    rw [← L.presheaf.germ_res_apply (homOfLE le_top) (genericPoint X) hηW, ← hf', map_zero]
  have hsupp : (idealSheafOfSection L σ).subschemeι.base z' ∈ (idealSheafOfSection L σ).support := by
    have : (idealSheafOfSection L σ).subschemeι.base z' ∈
        Set.range (idealSheafOfSection L σ).subschemeι := ⟨z', rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at this
  exact coheight_eq_one_of_ideal_eq_span_singleton _ ⟨W, hW⟩ f hf0 hI _ hzW hsupp hmax

end AlgebraicGeometry.Scheme

open Classical in

/-- At a point `z` of coheight `≠ 1`, the coefficient of `[Z(σ)]_d` is zero.

Sources: Stacks 02QU (the definition of `[Z]_d`); Krull's Hauptidealsatz (Stacks 00KV).
Proof: the coefficient of `[Z]_d` at `z` is the coefficient of the `fundamentalCycle` on the fibre of
`ι : Z → X` over `z` (a point or empty; `properPushforward_apply`); if it is nonzero then `z = ι z′` with
`z′` the generic point of an irreducible component of `Z`
(`AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_of_not_generic`). Near `z`, `Z` is cut out by a
single nonzero element `f` (`σ = f·e`, `f ≠ 0` since `σ ≠ 0` and `X` is integral), so Krull's
Hauptidealsatz gives `coheight z = dim O_{X,z} = 1`, contradicting the hypothesis; this step is
`coheight_subschemeι_eq_one_of_mem_genericPoints` ((1)–(3)). The case `z = η` needs no separate
treatment: if `η ∈ Z`, then `f` lies in the zero prime corresponding to `η`, contradicting `f ≠ 0`
(contained in (2)). Boundary case: if `Z` is empty (`σ` nowhere zero) then `z ∉ range ι`, the fibre is
empty and the coefficient is zero. -/
theorem AlgebraicGeometry.Scheme.idealSheafOfSection_cycle_apply_of_coheight_ne_one
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (σ : (L.val.obj (Opposite.op ⊤) : Type u)) (hσ : σ ≠ 0)
    (d : ℕ) (z : X) (hz : Order.coheight z ≠ 1) :
    (AlgebraicGeometry.Scheme.idealSheafOfSection L σ).cycle d z = 0 := by
  set I := AlgebraicGeometry.Scheme.idealSheafOfSection L σ with hIdef
  have : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  show AlgebraicGeometry.AlgebraicCycle.properPushforward I.subschemeι
    (I.subscheme.fundamentalCycle d) z = 0
  rw [AlgebraicGeometry.AlgebraicCycle.properPushforward_apply]
  by_cases hz' : z ∈ Set.range I.subschemeι.base
  · obtain ⟨z', rfl⟩ := hz'
    have hset : I.subschemeι.base ⁻¹' {I.subschemeι.base z'} = {z'} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => I.subschemeι.isClosedEmbedding.injective h, fun h => h ▸ rfl⟩
    rw [hset, finsum_mem_singleton]
    have hgen : z' ∉ genericPoints I.subscheme := fun hgen =>
      hz (AlgebraicGeometry.Scheme.coheight_subschemeι_eq_one_of_mem_genericPoints L σ hσ z' hgen)
    have hzero : I.subscheme.fundamentalCycle d z' = 0 := by
      show (if AlgebraicGeometry.Intersection.pointClosureDimension I.subscheme z' = d
        then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity I.subscheme z' else 0) = 0
      rw [AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_of_not_generic _ _ hgen]
      simp
    rw [hzero, zero_mul]
  · have hset : I.subschemeι.base ⁻¹' {z} = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      exact fun h => hz' ⟨y, h⟩
    rw [hset, finsum_mem_empty]

end
