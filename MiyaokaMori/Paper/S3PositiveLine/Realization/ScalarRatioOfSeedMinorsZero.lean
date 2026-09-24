import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.SeedBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceRestrictToZeroSection
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackTransport
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalarOfCoefficientsZero
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpace
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodUnitOfZeroSectionOne
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.Paper.S3PositiveLine.Realization.TotScalarRatioOfSeedMinorsZero
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback

/-! # The scalar ratio when the seed minors vanish

Statement: `P = (P_ℓ)` is a tuple of sections of `p^*A_ρ` on `Tot(L)` restricting along the zero section to the seed
tuple `ρ^*f_ℓ` (`hzero`), and all `2×2` minors with the seed tuple `s_ℓ = p^*ρ^*f_ℓ` vanish (`P_i ⊗ s_j = P_j ⊗ s_i`).
Then there are a nonempty open `V ⊆ C̃` and a unit `u` on `W = p_κ^{-1}(V) ⊂ C̃_(κ)(L)` restricting to `1` along the
zero section of the jet, such that for every `ℓ` the truncation `P_ℓ|_{C̃_(κ)(L)}` equals on `W` the product of `u`
with the restriction of the seed section `p_κ^*ρ^*f_ℓ`.

Proof:
1. Choose `j` with `ρ^*f_j ≠ 0`: `D.hcoord` says the `f_ℓ` have no common zero on `C`; `C̃` is nonempty, so at the
   generic point `η̃` some `f_j` does not vanish at `ρ(η̃)`, hence `ρ^*f_j` does not vanish at `η̃`. Let `V` be the
   nonvanishing locus of `ρ^*f_j` (`Modules.nonvanishingLocus`, open); `η̃ ∈ V`, so `V` is nonempty.
2. On `p^{-1}(V)`, `s_j = p^*ρ^*f_j` is nowhere zero (same lemma), hence a frame of the line bundle `p^*A_ρ`: there is
   a unique `λ ∈ Γ(p^{-1}V, O_{Tot})` with `P_j| = λ·s_j|` (a nowhere-zero section of a line bundle trivializes it;
   `projectivizationRatio` is exactly this ratio).
3. From the vanishing of the minors: `P_i ⊗ s_j = P_j ⊗ s_i = λ·(s_j ⊗ s_i)`; trivializing `(p^*A_ρ)^{⊗2}` on
   `p^{-1}V` by the frame `s_j` and cancelling `s_j` gives `P_i| = λ·s_i|` for all `i`.
4. Pull back along the zero section `σ₀`: `P_j|_0 = ρ^*f_j` (`hzero`) and `s_j|_0 = ρ^*f_j` (`σ₀ ≫ p = 𝟙`, compatibility
   of `pullbackComp`/`pullbackId`), so `(λ|_0 − 1)·ρ^*f_j = 0` on `V`; `ρ^*f_j` is a frame, hence `λ|_0 = 1`.
5. Let `u` be the restriction to `W = p_κ^{-1}(V) = i_κ^{-1}(p^{-1}V)` of the pullback of `λ` along
   `i_κ : C̃_(κ)(L) ↪ Tot(L)`. The zero section of the jet composed with `i_κ` is the zero section of `Tot(L)`
   (`jetNeighborhood.zeroSection_toTotalSpace`), so `u` is `1` along the zero section of the jet.
6. `u` is a unit: the ideal sheaf `𝓘 = ⊕_{1≤q≤κ} L^{-q}` of the zero section `C̃ ↪ C̃_(κ)(L)` satisfies `𝓘^{κ+1} = 0`;
   `u − 1 ∈ Γ(W, 𝓘)`, so `(u−1)^{κ+1} = 0` and `u = 1 +` nilpotent is invertible (Mathlib `IsNilpotent.isUnit_add_one`
   and the like).
7. Pull step 3 back along `i_κ` and restrict to `W`: `restrictToThickening` is the pullback of sections along `i_κ`
   followed by the canonical isomorphism `i_κ^*p^* ≅ p_κ^*` (`pullbackComp` and `toTotalSpace_proj`), which commutes
   with scalar multiplication and with restriction to opens; `restrictToThickening(p^*t) = p_κ^*t`
   (pseudofunctoriality of pullback). Hence `ι_W^*(restrict P_ℓ) = u • ι_W^*(p_κ^*ρ^*f_ℓ)`.

Source: proof of Theorem 4.2 of the paper ("the affine tuple would therefore be a scalar multiple of
the seed tuple, with scalar value one at zero").

## Structure

The top-level theorem `exists_scalar_ratio_of_seed_minors_eq_zero` is assembled from three lemmas, one per
mathematical ingredient, plus transport lemmas:

* `exists_tot_scalar_ratio_of_seed_minors_eq_zero` — steps 1–4 above, on `Tot(L)` (the frame argument);
* `jetNeighborhood.isUnit_of_zeroSection_appTop_eq_one` — step 6 (nilpotence of the zero-section ideal);
* `restrictToThickening_eq_thickeningRestrict` (module `GenericallyScalarOfCoefficientsZero`; see its docstring for
  the kernel obstacle it avoids) — used to unfold `restrictToThickening` as `Φ ∘ i_κ^*`; and
  `restrictToThickening_sectionPullbackAlong` (same module, derived from the bridge) — the pseudofunctoriality
  identity of step 7 (`restrictToThickening (p^*t) = p_κ^*t`);
* `sectionPullbackAlong_comp_congr` and friends (module `SectionPullbackTransport`) — transport of pulled-back
  sections across a commutative square, `resLE` congruence, etc.

Steps 5 and 7 are carried out in the body of the main theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Transport of a scalar relation across a commutative square (variable level) -/

/-- If `ι'^*P = c • ι'^*Q` and `g ≫ ι' = g' ≫ ι''`, then `g'^*ι''^*P = (g^♯c) • g'^*ι''^*Q`.
Proof: pull `ι'^*P = c • ι'^*Q` back along `g` (`sectionPullbackAlong_smul`), then transport both sides
across the square with `sectionPullbackAlong_comp_congr` (the transport is a module isomorphism, hence
commutes with `•`: `modules_hom_app_top_smul`). Stated at the variable level so that the concrete instance
in the main theorem is a single `have` (the same `congrArg` chain written there costs ~40 s). -/
theorem sectionPullbackAlong_square_smul {X Y Y' Z : AlgebraicGeometry.Scheme.{u}}
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
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp g' ι'').app M).inv.val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app M).hom.val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp g ι').app M).hom.val.app (Opposite.op ⊤)).hom y))) h1
  beta_reduce at h2
  rw [sectionPullbackAlong_comp_congr g ι' g' ι'' h,
    AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul,
    AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul,
    AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul,
    sectionPullbackAlong_comp_congr g ι' g' ι'' h] at h2
  exact h2

/-! ## A variable-level lemma about `thickeningRestrict` -/

/-- If `j^*i^*P = c • j^*i^*Q`, then the same holds after the comparison `thickeningRestrict i p h M`
(which is a module morphism applied to `i^*(-)`): `j^*(thickeningRestrict P) = c • j^*(thickeningRestrict Q)`.
Stated and proved at the variable level (`unfold` is cheap there); in the concrete situation of the main theorem
the unfolding of `thickeningRestrict` exceeds the heartbeat budget (same phenomenon as in
`GenericallyScalarOfCoefficientsZero`). -/
theorem thickeningRestrict_smul_of {W' X Y Z : AlgebraicGeometry.Scheme.{u}}
    (j : W' ⟶ X) (i : X ⟶ Y) (p : Y ⟶ Z) {g : X ⟶ Z} (h : i ≫ p = g) (M : Z.Modules)
    (P Q : (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u))
    (c : Γ(W', ⊤))
    (hkey : sectionPullbackAlong j (sectionPullbackAlong i P)
      = (show W'.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) • sectionPullbackAlong j (sectionPullbackAlong i Q)) :
    sectionPullbackAlong j (thickeningRestrict i p h M P)
      = (show W'.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) •
          sectionPullbackAlong j (thickeningRestrict i p h M Q) := by
  unfold thickeningRestrict
  rw [sectionPullbackAlong_naturality, sectionPullbackAlong_naturality, hkey]
  exact AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul _ _ _

/-- **Step 7 at the variable level.** If `j^* i_κ^* P = c • j^* i_κ^* (p^* a)` for a morphism `j` into the jet
neighbourhood, then `j^*(restrictToThickening P) = c • j^*(p_κ^* a)`. Proof: unfold `restrictToThickening`
through the bridge `restrictToThickening_eq_thickeningRestrict`, rewrite `p_κ^* a` as
`restrictToThickening (p^* a)` (`restrictToThickening_sectionPullbackAlong`), and apply
`thickeningRestrict_smul_of`. Kept separate from the main theorem because in the concrete situation there
(`L`, `seedBundlePullback f ρ`, `κ` fixed) the same rewrites exceed the heartbeat budget. -/
theorem restrictToThickening_smul_of {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) (κ : ℕ) {W' : AlgebraicGeometry.Scheme.{u}}
    (j : W' ⟶ (jetNeighborhood L κ).left)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (a : (M.toModules.val.obj (Opposite.op ⊤) : Type u)) (c : Γ(W', ⊤))
    (hkey : sectionPullbackAlong j (sectionPullbackAlong (jetNeighborhood.toTotalSpace L κ).left P)
      = (show W'.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) •
          sectionPullbackAlong j (sectionPullbackAlong (jetNeighborhood.toTotalSpace L κ).left
            (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom a))) :
    sectionPullbackAlong j (restrictToThickening L M κ P)
      = (show W'.ringCatSheaf.obj.obj (Opposite.op ⊤) from c) •
          sectionPullbackAlong j (sectionPullbackAlong (jetNeighborhood.proj L κ) a) := by
  rw [restrictToThickening_eq_thickeningRestrict, ← restrictToThickening_sectionPullbackAlong L M κ a,
    restrictToThickening_eq_thickeningRestrict]
  exact thickeningRestrict_smul_of _ _ _ _ _ _ _ _ hkey

/-! ## The theorem -/

theorem exists_scalar_ratio_of_seed_minors_eq_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} (κ : ℕ)
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
    ∃ U : ρ.source.toScheme.Opens, (U : Set ρ.source.toScheme).Nonempty ∧
      ∃ u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤)ˣ,
        ((jetNeighborhood.zeroSection L κ).resLE ((jetNeighborhood.proj L κ) ⁻¹ᵁ U) U
            (by
              change U ≤ (jetNeighborhood.zeroSection L κ ≫ jetNeighborhood.proj L κ) ⁻¹ᵁ U
              rw [jetNeighborhood.zeroSection_proj]
              exact le_rfl)).appTop
            (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤)) = 1 ∧
        ∀ ℓ,
          sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι
              (restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ))
            = (show ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from
                (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤))) •
              sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι
                (sectionPullbackAlong (jetNeighborhood.proj L κ)
                  (seedCoordPullback f ρ (D.coord ℓ))) := by
  obtain ⟨V, hV, lam, hlam1, hlam⟩ :=
    exists_tot_scalar_ratio_of_seed_minors_eq_zero (f := f) P hzero hminor
  -- W := p_κ⁻¹V ⊆ C̃_(κ)(L) lies over V' := p⁻¹V ⊆ Tot(L) under i_κ (since i_κ ≫ p = p_κ)
  have hWV' : (jetNeighborhood.proj L κ) ⁻¹ᵁ V ≤
      (jetNeighborhood.toTotalSpace L κ).left ⁻¹ᵁ
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) :=
    le_of_eq (by
      rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, jetNeighborhood.toTotalSpace_proj])
  -- the restricted closed immersion g : W → p⁻¹V
  have hσle : V ≤ (jetNeighborhood.zeroSection L κ) ⁻¹ᵁ ((jetNeighborhood.proj L κ) ⁻¹ᵁ V) :=
    le_of_eq (by
      rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, jetNeighborhood.zeroSection_proj]; rfl)
  have hσ0le : V ≤ (AlgebraicGeometry.Scheme.zeroSection L.toModules) ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) :=
    le_of_eq (by
      rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, AlgebraicGeometry.Scheme.zeroSection_comp]; rfl)
  -- the two zero sections agree after restriction: σ_κ|_V ≫ g = σ₀|_V
  have hσ : (jetNeighborhood.zeroSection L κ).resLE ((jetNeighborhood.proj L κ) ⁻¹ᵁ V) V hσle ≫
        (jetNeighborhood.toTotalSpace L κ).left.resLE
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)
          ((jetNeighborhood.proj L κ) ⁻¹ᵁ V) hWV'
      = (AlgebraicGeometry.Scheme.zeroSection L.toModules).resLE
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) V hσ0le := by
    rw [AlgebraicGeometry.Scheme.Hom.resLE_comp_resLE]
    exact AlgebraicGeometry.Scheme.Hom.resLE_congr_hom
      (jetNeighborhood.zeroSection_toTotalSpace L κ) _ _ _ _
  -- u := g^*λ has value 1 along the jet zero section
  have hu1 : ((jetNeighborhood.zeroSection L κ).resLE ((jetNeighborhood.proj L κ) ⁻¹ᵁ V) V hσle).appTop
      (((jetNeighborhood.toTotalSpace L κ).left.resLE
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)
          ((jetNeighborhood.proj L κ) ⁻¹ᵁ V) hWV').appTop lam) = 1 := by
    rw [← hlam1, ← hσ, AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have hunit := jetNeighborhood.isUnit_of_zeroSection_appTop_eq_one L κ V _ hu1
  refine ⟨V, hV, hunit.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec]
    exact hu1
  · intro ℓ
    rw [IsUnit.unit_spec]
    -- transport of the Tot-level identity along g, then across the square g ≫ ι' = W.ι ≫ i_κ
    have hsq : (jetNeighborhood.toTotalSpace L κ).left.resLE
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)
          ((jetNeighborhood.proj L κ) ⁻¹ᵁ V) hWV' ≫
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V).ι
      = ((jetNeighborhood.proj L κ) ⁻¹ᵁ V).ι ≫ (jetNeighborhood.toTotalSpace L κ).left :=
      AlgebraicGeometry.Scheme.Hom.resLE_comp_ι _ hWV'
    have key := sectionPullbackAlong_square_smul _ _ _ _ hsq (P ℓ)
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        (seedCoordPullback f ρ (D.coord ℓ))) lam (hlam ℓ)
    -- step 7: unfold `restrictToThickening` and use `key` — done at the variable level in
    -- `restrictToThickening_smul_of` (in this concrete situation the rewrites exceed the heartbeat budget)
    exact restrictToThickening_smul_of L (seedBundlePullback f ρ) κ _ (P ℓ)
      (seedCoordPullback f ρ (D.coord ℓ)) _ key

end
