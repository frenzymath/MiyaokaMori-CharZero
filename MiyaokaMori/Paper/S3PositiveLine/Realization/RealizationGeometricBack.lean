import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S4Completion.ZeroSectionTotalSpaceInclOSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.CoefficientSections
import MiyaokaMori.Paper.S3PositiveLine.Realization.EmbeddingDegreeBound
import MiyaokaMori.Paper.S3PositiveLine.Realization.NonnegDegreeVanishing
import MiyaokaMori.Paper.S3PositiveLine.Realization.ResolvedSurface
import MiyaokaMori.Paper.S3PositiveLine.Realization.ThickeningEquationsVanish
import MiyaokaMori.AlgebraicGeometry.Blowup.StrictTransformTower
import MiyaokaMori.Paper.S3PositiveLine.Realization.R0Bound
import MiyaokaMori.Paper.S3PositiveLine.PositiveLine

/-! # The geometric second half of the polynomial realization

The geometric second half of Theorem 4.2 of the paper: for given `ρ`, `L`, jet and `r₀`, construct the
polynomial tuple `P` and the resolution data `S`, `β`, `eW`, `π_S`, `σ`, `Φ`, and prove all conjuncts of the
conclusion of `realization` other than the numerical ones. It is a separate module so that the target module
`MiyaokaMori.Targets.Realization` stays fast to compile.

Source: the proof of Theorem 4.2 and Corollary 4.3 of the paper.

`sectionPullbackAlong` is the one definition (its body is the adjunction unit) and `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback`
its `Γ`-typed reducible abbrev: `unfold sectionPullbackAlong` does not produce the `Γ`-typed spelling; the proofs
below either reach the unit by plain `unfold sectionPullbackAlong` (`map_add`/`map_zero`) or reach the `Γ`-typed
spelling by a `change` (the two spellings are `rfl`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section


/- The restriction map is a composite of additive module maps.  These local
   lemmas expose that additivity without relying on reduction through the
   pullback comparison isomorphisms. -/
private lemma realization_restrict_add {Y : AlgebraicGeometry.Scheme.{u}}
    (V : Y.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    {M : Y.Modules}
    (a b : (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace V).hom).obj M).val.obj
      (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection V (a + b) =
      AlgebraicGeometry.Scheme.restrictToZeroSection V a +
        AlgebraicGeometry.Scheme.restrictToZeroSection V b := by
  unfold AlgebraicGeometry.Scheme.restrictToZeroSection
  have hinner :
      sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection V) (a + b) =
        sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection V) a +
          sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection V) b := by
    unfold sectionPullbackAlong
    exact map_add _ _ _
  rw [hinner]
  exact map_add _ _ _

private lemma realization_zero_restrict_direct {Y : AlgebraicGeometry.Scheme.{u}}
    (V : Y.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (M : Y.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection V
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace V).hom s) = s := by
  unfold AlgebraicGeometry.Scheme.restrictToZeroSection
  dsimp only [CategoryTheory.Iso.trans_hom]
  -- the `change` below is the bridge to the `Γ`-typed `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback` spelling (rfl; T18b)
  change
    (((AlgebraicGeometry.Scheme.Modules.pullbackId Y).hom.app M).val.app (Opposite.op ⊤)).hom (
      (((AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.zeroSection_comp V)).hom.app M).val.app (Opposite.op ⊤)).hom (
        (((AlgebraicGeometry.Scheme.Modules.pullbackComp
          (AlgebraicGeometry.Scheme.zeroSection V)
          (AlgebraicGeometry.Scheme.totalSpace V).hom).hom.app M).val.app
          (Opposite.op ⊤)).hom (
          AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (AlgebraicGeometry.Scheme.zeroSection V)
            (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (AlgebraicGeometry.Scheme.totalSpace V).hom s)))) = s
  have hcomp' :
      (((AlgebraicGeometry.Scheme.Modules.pullbackComp
          (AlgebraicGeometry.Scheme.zeroSection V)
          (AlgebraicGeometry.Scheme.totalSpace V).hom).hom.app M).val.app
        (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (AlgebraicGeometry.Scheme.zeroSection V)
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (AlgebraicGeometry.Scheme.totalSpace V).hom s)) =
      AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback
        (AlgebraicGeometry.Scheme.zeroSection V ≫
          (AlgebraicGeometry.Scheme.totalSpace V).hom) s := by
    exact AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp
      (AlgebraicGeometry.Scheme.zeroSection V)
      (AlgebraicGeometry.Scheme.totalSpace V).hom s
  rw [hcomp']
  have hcongr' :
      (((AlgebraicGeometry.Scheme.Modules.pullbackCongr
          (AlgebraicGeometry.Scheme.zeroSection_comp V)).hom.app M).val.app
        (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback
          (AlgebraicGeometry.Scheme.zeroSection V ≫
            (AlgebraicGeometry.Scheme.totalSpace V).hom) s) =
      AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (CategoryTheory.CategoryStruct.id Y) s := by
    exact AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply
      (AlgebraicGeometry.Scheme.zeroSection_comp V) s
  rw [hcongr']
  change (((AlgebraicGeometry.Scheme.Modules.pullbackId Y).hom.app M).app ⊤
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (CategoryTheory.CategoryStruct.id Y) s)) = s
  have h := CategoryTheory.unit_conjugateEquiv
    (CategoryTheory.Adjunction.id (C := Y.Modules))
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 Y))
    ((AlgebraicGeometry.Scheme.Modules.pullbackId Y).hom) M
  rw [AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  have hs := congrArg (fun φ => φ.app ⊤ s) h
  simp only [CategoryTheory.NatTrans.comp_app,
    AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply,
    AlgebraicGeometry.Scheme.Modules.pushforwardId_inv_app_app] at hs
  change s = _ at hs
  change s = ((AlgebraicGeometry.Scheme.Modules.pullbackId Y).hom.app M).app ⊤
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (𝟙 Y) s) at hs
  exact hs.symm

private lemma realization_restrict_sum {Y : AlgebraicGeometry.Scheme.{u}}
    (V : Y.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    {M : Y.Modules} {ι : Type} (s : Finset ι)
    (a : ι → (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace V).hom).obj M).val.obj
      (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection V (s.sum a) =
      s.sum (fun i => AlgebraicGeometry.Scheme.restrictToZeroSection V (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold AlgebraicGeometry.Scheme.restrictToZeroSection
      have hz : sectionPullbackAlong
          (AlgebraicGeometry.Scheme.zeroSection V)
          (0 : (((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.totalSpace V).hom).obj M).val.obj
            (Opposite.op ⊤) : Type u)) = 0 := by
        unfold sectionPullbackAlong
        exact map_zero _
      rw [hz]
      exact map_zero _
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, realization_restrict_add, ih,
        Finset.sum_insert hi]

private lemma realization_xi_zero_restrict {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (q : ℕ)
    (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj
      (Opposite.op ⊤)) : Type u)) (hq : 0 < q) :
    AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules
      (xiMonomial L M q c) = 0 := by
  have hq0 : q ≠ 0 := Nat.ne_of_gt hq
  have hcoeff : xiCoefficient L M (xiMonomial L M q c) 0 = 0 := by
    rw [xiCoefficient_xiMonomial]
    simp [hq0]
  have hmain := xiCoefficient_zero_eq_zeroSection L M (xiMonomial L M q c)
  rw [hcoeff, map_zero] at hmain
  have hIso :
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        (AlgebraicGeometry.Scheme.zeroSection L.toModules)
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).app M.toModules ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr
          (AlgebraicGeometry.Scheme.zeroSection_comp L.toModules)).app M.toModules ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackId C.toScheme).app M.toModules).hom =
      (zeroSectionPullbackIso L M).hom := by
    unfold zeroSectionPullbackIso
    unfold AlgebraicGeometry.Scheme.Modules.pullbackCongr
    simp [CategoryTheory.eqToIso, CategoryTheory.eqToHom_app]
  unfold AlgebraicGeometry.Scheme.restrictToZeroSection
  unfold zeroSectionPullbackIso at hmain
  rw [hIso]
  exact hmain.symm

/-- The polynomial tuple of equation (4.4) (Theorem 4.2 of the paper):
`P_ℓ := p_L^*ρ^*f_ℓ + Σ_{q=1}^{κ} c_{ℓ,q} ξ^q`, summed up to `κ` (the coefficients with `q > r₀` vanish,
`realization_hP`). Its restriction to the zero section is `ρ^*f_ℓ` (`realization_hzero`) and its truncation to
`C̃_(κ)(L)` is the `ℓ`-th cone coordinate of the jet (`realization_hjet`). -/
noncomputable def realizationTuple {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ}
    (jet : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (seedBundlePullback f ρ).toModules).val.obj (Opposite.op ⊤) : Type u) :=
  sectionPullbackAlong (M := (seedBundlePullback f ρ).toModules)
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
      (seedCoordPullback f ρ (D.coord ℓ)) +
    ∑ q : Fin κ,
      xiMonomial L (seedBundlePullback f ρ) ((q : ℕ) + 1)
        (BasedJet.coefficient jet ℓ ((q : ℕ) + 1))

private lemma realization_hzero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ}
    (jet : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (realizationTuple f jet ℓ)
      = seedCoordPullback f ρ (D.coord ℓ) := by
  have hbase := realization_zero_restrict_direct L.toModules
    (seedBundlePullback f ρ).toModules
    (seedCoordPullback f ρ (D.coord ℓ))
  have hadd :
      AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (realizationTuple f jet ℓ) =
        AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules
            (sectionPullbackAlong (M := (seedBundlePullback f ρ).toModules)
              (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
              (seedCoordPullback f ρ (D.coord ℓ))) +
          ∑ q : Fin κ,
            AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules
              (xiMonomial L (seedBundlePullback f ρ) ((q : ℕ) + 1)
                (BasedJet.coefficient jet ℓ ((q : ℕ) + 1))) := by
    unfold realizationTuple
    rw [realization_restrict_add]
    have hs := realization_restrict_sum (M := (seedBundlePullback f ρ).toModules)
      (ι := Fin κ) L.toModules
      (Finset.univ : Finset (Fin κ))
      (fun q : Fin κ =>
        xiMonomial L (seedBundlePullback f ρ) ((q : ℕ) + 1)
          (BasedJet.coefficient jet ℓ ((q : ℕ) + 1)))
    rw [hs]
  rw [hadd, hbase]
  have hsum :
      (∑ q : Fin κ,
        AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules
          (xiMonomial L (seedBundlePullback f ρ) ((q : ℕ) + 1)
            (BasedJet.coefficient jet ℓ ((q : ℕ) + 1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    exact realization_xi_zero_restrict L (seedBundlePullback f ρ) ((q : ℕ) + 1)
      (BasedJet.coefficient jet ℓ ((q : ℕ) + 1)) (by omega)
  rw [hsum]
  exact add_zero _

/- The coefficient cutoff is checked after transporting each coefficient through
   the canonical tensor reassociation from `seedBundlePullback` to the form
   accepted by `coefficient_eq_zero_of_gt_r0`. -/
private lemma realization_hP {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {r₀ : ℕ}
    (hL : 0 < L.degree)
    (hr0 : (r₀ : ℤ) =
      (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree *
        (ρ.degree : ℤ) / L.degree)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj (Opposite.op ⊤) : Type u)) :
    ∀ ℓ, xiDegree L (seedBundlePullback f ρ) (P ℓ) ≤ (r₀ : WithBot ℕ) := by
  intro ℓ
  rw [xiDegree_lt_iff]
  intro q hq
  let A : LineBundle C.toVariety :=
    LineBundle.pullback (X := C.toVariety) f (X.OX 1)
  let B : LineBundle ρ.source.toVariety := LineBundle.pullback ρ.hom A
  let τ₀ : AlgebraicGeometry.Scheme.Modules.tensor (B.zpow 1).toModules
      (L.zpow (-((q : ℕ) : ℤ))).toModules ≅
      AlgebraicGeometry.Scheme.Modules.tensor B.toModules
        (L.zpow (-((q : ℕ) : ℤ))).toModules :=
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (B.zpow 1).toModules (L.zpow (-((q : ℕ) : ℤ))).toModules) ≪≫
      (CategoryTheory.MonoidalCategory.tensorIso B.zpowOneIso
        (CategoryTheory.Iso.refl _)) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B.toModules
        (L.zpow (-((q : ℕ) : ℤ))).toModules).symm
  let τ : ((B.zpow 1).tensor (L.zpow (-((q : ℕ) : ℤ)))).toModules ≅
      (B.tensor (L.zpow (-((q : ℕ) : ℤ)))).toModules :=
    (CategoryTheory.eqToIso
      (LineBundle.tensor_toModules (B.zpow 1)
        (L.zpow (-((q : ℕ) : ℤ))))) ≪≫ τ₀ ≪≫
      (CategoryTheory.eqToIso
        (LineBundle.tensor_toModules B
          (L.zpow (-((q : ℕ) : ℤ))))).symm
  let c' : ((((B.tensor
      (L.zpow (-((q : ℕ) : ℤ)))).toModules.val.obj
      (Opposite.op ⊤)) : Type u)) :=
    (τ.hom.val.app (Opposite.op ⊤)).hom
      (xiCoefficient L (seedBundlePullback f ρ) (P ℓ) q)
  have hqbound : A.degree * (ρ.degree : ℤ) / L.degree < (q : ℤ) := by
    rw [← hr0]
    exact_mod_cast hq
  have hc' : c' = 0 := by
    apply coefficient_eq_zero_of_gt_r0 A ρ L hL q hqbound c'
  apply (realization_module_iso_map_zero_iff (k := k) (Y := ρ.source.toScheme)
    τ (xiCoefficient L (seedBundlePullback f ρ) (P ℓ) q)).mp
  simpa [c'] using hc'

/-- Pulling back global sections along `g` is additive (the adjunction unit is a module map;
variable level, so the kernel check is cheap). Companion of `sectionPullbackAlong_zero_gsz`
(`GenericallyScalarOfCoefficientsZeroThickeningRestrict`). -/
theorem sectionPullbackAlong_add_rgb {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    {N : Y.Modules} (a b : (N.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g (a + b) = sectionPullbackAlong g a + sectionPullbackAlong g b := by
  unfold sectionPullbackAlong
  exact map_add _ _ _

/-- **Additivity of `thickeningRestrict`** at variable level (`i`, `p`, `g`, `h` variables):
`thickeningRestrict i p h M` is `i^*` (additive, `sectionPullbackAlong_add_rgb`) followed by the module map
`((pullbackComp i p).app M).hom ≫ eqToHom _` on global sections (additive, `map_add`).
Stated at variable level on purpose: with `h : i ≫ p = g` a variable the kernel never evaluates the
transport `eqToHom`, see the docstring of `thickeningRestrict`
(`GenericallyScalarOfCoefficientsZeroThickeningRestrict`). -/
theorem thickeningRestrict_add {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (i : X ⟶ Y) (p : Y ⟶ Z) {g : X ⟶ Z} (h : i ≫ p = g) (M : Z.Modules)
    (a b : (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    thickeningRestrict i p h M (a + b) = thickeningRestrict i p h M a + thickeningRestrict i p h M b := by
  unfold thickeningRestrict
  rw [sectionPullbackAlong_add_rgb]
  exact map_add _ _ _

/-- **Additivity of the truncation map.**

Source: definition of `restrictToThickening` (§3 of the paper).

Proof: `restrictToThickening L M κ P` is by definition
`ψ (sectionPullbackAlong ι P)` with `ι = (jetNeighborhood.toTotalSpace L κ).left` and
`ψ = (((pullbackComp ι p_L).app M).hom ≫ eqToHom _).val.app (op ⊤)).hom`, a module map on global sections;
`sectionPullbackAlong ι` is additive (`map_add` of the adjunction unit) and so is `ψ`, hence the composite is
additive. In Lean the identity is *not* proved by unfolding `restrictToThickening` (its body is kernel-toxic: the
kernel's K-like reduction of the `eqToHom` transport forces a definitional-equality test between
`(pullback p_κ).obj M` and `(pullback (ι ≫ p_L)).obj M`, which does not finish). Instead the three occurrences are
rewritten with the bridge `restrictToThickening_eq_thickeningRestrict` to the variable-level map
`thickeningRestrict`, whose additivity `thickeningRestrict_add` above is cheap for the kernel.
Edge cases: none (a purely algebraic identity). -/
theorem restrictToThickening_add {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    (a b : (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    restrictToThickening L M κ (a + b) =
      restrictToThickening L M κ a + restrictToThickening L M κ b := by
  rw [restrictToThickening_eq_thickeningRestrict, restrictToThickening_eq_thickeningRestrict,
    restrictToThickening_eq_thickeningRestrict]
  exact thickeningRestrict_add _ _ _ _ a b

private lemma realization_thickening_zero {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ) :
    restrictToThickening L M κ (0 : (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) = 0 := by
  have h := restrictToThickening_add L M κ 0 0
  rw [add_zero] at h
  have h2 : restrictToThickening L M κ 0 + restrictToThickening L M κ 0 =
      restrictToThickening L M κ 0 + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h2

/-- `restrictToThickening` bundled as an additive map (only used to distribute it over finite sums). -/
private def realizationThickeningAddHom {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ) :
    (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u) →+
    (((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u) where
  toFun := restrictToThickening L M κ
  map_zero' := realization_thickening_zero L M κ
  map_add' := restrictToThickening_add L M κ

private lemma realization_thickening_sum {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety) (κ : ℕ)
    {ι : Type} (s : Finset ι)
    (a : ι → (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      M.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    restrictToThickening L M κ (s.sum a) =
      s.sum (fun i => restrictToThickening L M κ (a i)) :=
  map_sum (realizationThickeningAddHom L M κ) a s

/- Truncation of the tuple to the `κ`-th neighbourhood recovers the cone coordinates of the jet
   (Theorem 4.2 of the paper): `jet_coefficient_expansion` plus additivity, after
   rewriting `seedCoordPullback` through the naturality of `sectionPullbackAlong`. -/
private lemma realization_hjet {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ}
    (jet : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1)) :
    BasedJet.coneCoordinate jet ℓ
      = restrictToThickening L (seedBundlePullback f ρ) κ (realizationTuple f jet ℓ) := by
  have hbase : seedCoordPullback f ρ (D.coord ℓ) =
      sectionPullbackAlong ρ.hom
        ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom
            (D.coord ℓ)) :=
    (sectionPullbackAlong_naturality ρ.hom _ (D.coord ℓ)).symm
  unfold realizationTuple
  rw [restrictToThickening_add, realization_thickening_sum, hbase]
  exact jet_coefficient_expansion jet ℓ

/- The zero-section restriction in the form used by `morphism_near_zero_section`. -/
private lemma realization_hzero_alt {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ : ℕ}
    (jet : BasedJet f ρ L κ) (ℓ : Fin (X.embDim + 1)) :
    AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (realizationTuple f jet ℓ)
      = sectionPullbackAlong ρ.hom
          ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
            (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom
              (D.coord ℓ)) :=
  (realization_hzero f jet ℓ).trans (sectionPullbackAlong_naturality ρ.hom _ (D.coord ℓ)).symm

/- The cone equations hold identically on `Tot(L)` (Theorem 4.2 of the paper): the truncated equation
   vanishes and its ξ-degree is `≤ δ r₀ < κ`. -/
private lemma realization_hvanish {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    {ρ : FiniteCover k C} {L : LineBundle ρ.source.toVariety} {κ r₀ : ℕ}
    (jet : BasedJet f ρ L κ) (hδ : D.δ * r₀ < κ)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L (seedBundlePullback f ρ) (P ℓ) ≤ (r₀ : WithBot ℕ))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ
        = restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ)) (j : D.E.ι) :
    evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0 :=
  equations_vanish_identically L (seedBundlePullback f ρ) D.E.deg D.E.F D.E.homogeneous
    D.E.deg_le hδ P hP
    (fun j => totalSpaceZpowIso L (seedBundlePullback f ρ) (D.E.deg j))
    (fun j => restrictToThickening_evalHomogeneous_eq_zero jet P hjet j) j

/-- **The geometric second half of Theorem 4.2 of the paper.**
Source: the part of the proof of Theorem 4.2 after equation (4.1), and the first
sentence of equation (4.5) (Corollary 4.3); the resolution step follows the proof
of Debarre, *Higher-Dimensional Algebraic Geometry*, Thm 5.18 / Stacks 0C5H.

The numerical first half (`realization_numeric_front`: take `ρ`, `L`, jet from `positive_line`, `d_L > 0`,
`r₀ = ⌊ae/d_L⌋`, `1 ≤ r₀`, `δ r₀ < κ`, and the strict bound `r₀ < 2(n+1)κa/(d h_κ)`) is proved in this file. This
lemma constructs, for **given** `ρ`, `L`, jet, `r₀`, all the remaining data `P`, `S`, `β`, `eW`, `π_S`, `σ`, `Φ` and
proves all conjuncts of the conclusion of the main theorem other than the numerical ones.

Proof (for fixed `ρ`, `L`, jet, `r₀`):
1. Coordinates and coefficients: the homogeneous coordinates `f_ℓ = D.coord ℓ` of `f` and the equations
   `F_j = D.E.F j` (degrees in `[1, δ]`). The `ℓ`-th cone coordinate of the jet expands as
   `ρ^*f_ℓ + Σ_{q=1}^{κ} c_{ℓ,q} ξ^q` with `c_{ℓ,q} ∈ H⁰(C̃, ρ^*A ⊗ L^{-q})`.
2. Truncation: `deg(ρ^*A ⊗ L^{-q}) = ae − q d_L < 0` for `q > r₀` (`hr0`), so `c_{ℓ,q} = 0` (`realization_hP`
   formalizes this as `xiDegree ≤ r₀`). Put `P_ℓ := p_L^*ρ^*f_ℓ + Σ_{q=1}^{κ} c_{ℓ,q} ξ^q` (the `P` of
   `realization_hzero`; the terms with `q > r₀` vanish). Then `xiDegree (P ℓ) ≤ r₀`; truncation to the `κ`-th
   thickening keeps the coefficients with `q ≤ κ`, giving `coneCoordinate jet ℓ = restrictToThickening κ (P ℓ)`;
   the restriction along the zero section is `ρ^*f_ℓ` (`realization_hzero`).
3. The equations hold identically: the truncation of `F_j(P)` is `F_j(coordinates of the jet) = 0` (the jet lies in the
   cone `𝒵`; truncation commutes with evaluating homogeneous polynomials), and the `ξ`-degree of `F_j(P)` is
   `≤ δ r₀ < κ` (`hδ`), hence `F_j(P) = 0`.
4. The morphism on a neighbourhood of the zero section: `hnz` (the normalized tuple has no common zero on the zero
   section) gives an open `U ⊇` zero section and `Φ₀ : U → X` with `σ₀ ≫ Φ₀ = ρ ≫ f`.
5. Nonconstancy on the general fiber and the degree bound: if `Φ₀` were constant on the general fiber, the jet would
   be generically scalar, contradicting `hns`; removing a common factor only lowers the degree; so on a nonempty open
   set `1 ≤` fiber degree `≤ r₀`.
6. Move to the ruled surface `W = P(O ⊕ L)`: `Tot(L) ⊂ W` is an open immersion compatible with the projections, `eW`
   is the isomorphism `ruledSurface.toScheme_eq`, and the zero section corresponds to the `O`-section.
7. Resolution: a tower of point blowups `β` with centres away from `U_W ⊇ Σ₀` gives `S`, `π_S = β ≫ π_W` (surjective,
   with connected closed fibers), `σ`, `Φ` with `σ ≫ Φ = ρ ≫ f`, `Φ` a `k`-morphism, and an open `V` over which the
   fibers are `≅ P¹` with `1 ≤ fiberDegree ≤ r₀`; `IsBlowupTowerAvoiding` is monotone in the set, and the exceptional
   centres are not in `U_W`, hence disjoint from `Σ₀`. `EmbeddingDegreeBound Φ π_S hπS r₀` follows from the same `V`.

Edge cases: `hr1 : 1 ≤ r₀` and `hL` guarantee `a·e ≥ d_L > 0`; if the ideal is zero (no equations) step 3 is vacuous;
`κ ≥ 1` is `hκ1`. The conclusion is that of `realization` without the numerical conjuncts, and the hypotheses are
exactly the facts produced by the numerical first half (`hL`, `hns`, `hnz`, `hr0`, `hr1`, `hδ`) together with `hf`,
`hd`, `hκ1`; the paper's proof uses only these once `ρ`, `L`, jet are fixed. The proof body uses only `hL`, `hns`,
`hr0`, `hδ` (and the instance `D`); `hf`, `hd`, `hκ1`, `hnz`, `hr1` occur only in the signature, carried over from
the target's interface so that `realization_numeric_front` and this lemma fit together verbatim. -/
theorem realization_geometric_back {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f] (hf : ¬ IsConstantMorphism f)
    (hd : 0 < TangentBundle.pullbackDegree f)
    (κ : ℕ) (hκ1 : 1 ≤ κ)
    (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
    (jet : BasedJet f ρ L κ) (r₀ : ℕ)
    (hL : 0 < L.degree)
    (hns : ¬ jet.IsGenericallyScalar)
    (hnz : NormalizedTupleNowhereZero jet)
    (hr0 : (r₀ : ℤ) = (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree)
    (hr1 : 1 ≤ r₀) (hδ : D.δ * r₀ < κ) :
    ∃ (P : Fin (X.embDim + 1) →
        (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
      (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ (ruledSurface L).toScheme)
      (hβ : IsBlowupTower β)
      (eW : (ruledSurface L).toScheme ≅
        (AlgebraicGeometry.Scheme.projBundle
          (CategoryTheory.Limits.biprod (C := ρ.source.toVariety.toScheme.Modules) (show ρ.source.toVariety.toScheme.Modules from SheafOfModules.unit ρ.source.toVariety.toScheme.ringCatSheaf) L.toModules)).left)
      (πS : S.toScheme ⟶ ρ.source.toScheme)
      (hπS : AlgebraicGeometry.Surjective πS)
      (σ : ρ.source.toScheme ⟶ S.toScheme) (Φ : S.toScheme ⟶ X.toScheme),
      -- the jet extends to Tot(L) → 𝒵: a polynomial tuple of fiber degree ≤ r₀, truncating back to the jet and satisfying all equations
      (∀ ℓ, xiDegree L (seedBundlePullback f ρ) (P ℓ)
          ≤ (r₀ : WithBot ℕ)) ∧
      (∀ ℓ, BasedJet.coneCoordinate jet ℓ
          = restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ)) ∧
      (∀ j, evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0) ∧
      -- the blowup tower: all centres are closed points not above the O-section Σ₀; the identification of W with P(O ⊕ L) is compatible with the projections
      IsBlowupTowerAvoiding β
        (Set.range (AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv).base) ∧
      Disjoint (ExceptionalCenters β hβ)
        (Set.range (AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv).base) ∧
      eW.hom ≫ (AlgebraicGeometry.Scheme.projBundle
          (CategoryTheory.Limits.biprod (C := ρ.source.toVariety.toScheme.Modules) (show ρ.source.toVariety.toScheme.Modules from SheafOfModules.unit ρ.source.toVariety.toScheme.ringCatSheaf) L.toModules)).hom
        = ruledSurface.π L ∧
      πS = β ≫ ruledSurface.π L ∧
      (∀ y : ρ.source.toScheme, IsClosed ({y} : Set ρ.source.toScheme) →
        _root_.IsConnected (πS.base ⁻¹' {y})) ∧
      σ ≫ πS = CategoryTheory.CategoryStruct.id ρ.source.toScheme ∧
      σ ≫ β = AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv ∧
      σ ≫ Φ = ρ.hom ≫ f ∧
      -- Φ is a k-morphism (this provides the `[Φ.IsOver]` needed downstream; the k-compatibility of β, π_S, σ follows from hβ etc.)
      Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      (∃ V : Set ρ.source.toScheme, IsOpen V ∧ V.Nonempty ∧
        ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
          Nonempty ((πS.fiber y) ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) ∧
          1 ≤ fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y ∧
          fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y ≤ (r₀ : ℤ)) ∧
      EmbeddingDegreeBound Φ πS hπS r₀ := by
  classical
  -- Steps 1–3: the polynomial tuple, its truncation, its zero-section restriction, the equations.
  let P := realizationTuple f jet
  have hP : ∀ ℓ, xiDegree L (seedBundlePullback f ρ) (P ℓ) ≤ (r₀ : WithBot ℕ) :=
    realization_hP f hL hr0 P
  have hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ
      = restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ) :=
    fun ℓ => realization_hjet f jet ℓ
  have hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ)
      = seedCoordPullback f ρ (D.coord ℓ) :=
    fun ℓ => realization_hzero f jet ℓ
  have hvanish : ∀ j, evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0 :=
    fun j => realization_hvanish f jet hδ P hP hjet j
  -- Step 4: the morphism `Φ₀ : U → X` on an open neighbourhood `U` of the zero section of `Tot(L)`.
  obtain ⟨U, Φ₀, hproj, hreal⟩ :=
    morphism_near_zero_section jet P hjet (fun ℓ => realization_hzero_alt f jet ℓ) hvanish
  obtain ⟨hU0, σ₀, ν, jetx, hσ₀ι, hσ₀Φ, -, -⟩ := hreal
  -- Step 5: fibre degrees on a nonempty open set of `C̃`.
  obtain ⟨V, hVopen, hVne, hV⟩ :=
    fiber_degree_between jet hns P hP hjet hzero U Φ₀ hproj hU0
  -- Step 6: move to the ruled surface `W = P(O ⊕ L)` along the open immersion `Tot(L) ↪ W`.
  let incl : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left ⟶ (ruledSurface L).toScheme :=
    ruledSurface.totalSpaceIncl L
  haveI hincl : AlgebraicGeometry.IsOpenImmersion incl := ruledSurface.totalSpaceIncl_isOpenImmersion L
  let UW : (ruledSurface L).toScheme.Opens := (AlgebraicGeometry.Scheme.Hom.opensFunctor incl).obj U
  have hUWset : (UW : Set (ruledSurface L).toScheme) = incl.base '' (U : Set _) := rfl
  have hrange : Set.range (U.ι ≫ incl).base = Set.range UW.ι.base := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι, hUWset, ← AlgebraicGeometry.Scheme.Opens.range_ι U,
      ← Set.range_comp]
    rfl
  let e : U.toScheme ≅ UW.toScheme :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq (U.ι ≫ incl) UW.ι hrange
  have he_hom : e.hom ≫ UW.ι = U.ι ≫ incl :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac (U.ι ≫ incl) UW.ι hrange
  have he_inv : e.inv ≫ (U.ι ≫ incl) = UW.ι :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac (U.ι ≫ incl) UW.ι hrange
  let Φ₀W : UW.toScheme ⟶ X.toScheme := e.inv ≫ Φ₀
  -- `U_W` is a nonempty open subset of the irreducible surface `W`, hence dense.
  obtain ⟨y₀⟩ : Nonempty ρ.source.toScheme := inferInstance
  have hUWdense : Dense (UW : Set (ruledSurface L).toScheme) := by
    apply UW.2.dense
    refine ⟨incl.base (U.ι.base (σ₀.base y₀)), ?_⟩
    show incl.base (U.ι.base (σ₀.base y₀)) ∈ incl.base '' (U : Set _)
    refine ⟨U.ι.base (σ₀.base y₀), ?_, rfl⟩
    rw [← AlgebraicGeometry.Scheme.Opens.range_ι]
    exact Set.mem_range_self _
  -- The rational map `W ⇢ X` represented by `Φ₀W` on `U_W`.
  let g : (ruledSurface L).toScheme.PartialMap X.toScheme := ⟨UW, hUWdense, Φ₀W⟩
  haveI : X.toScheme.IsSeparated :=
    AlgebraicGeometry.Scheme.isSeparated_of_isProper_over_field (k := k) X.toScheme
  let Φrat : (ruledSurface L).toScheme ⤏ X.toScheme := g.toRationalMap
  have hU : IsRegularOn Φrat UW := g.le_domain_toRationalMap
  have hhom : (ruledSurface L).toScheme.homOfLE hU ≫ Φrat.toPartialMap.hom = Φ₀W := by
    exact g.toPartialMap_toRationalMap_restrict
  -- `Φ₀` is a `k`-morphism (it is the projectivization of the tuple), hence so is the rational map.
  have hΦ₀over : Φ₀ ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
    obtain ⟨hU', hΦ₀e⟩ := hproj
    rw [← X.embedding.over, ← Category.assoc, hΦ₀e, projectivizationMorphism_comp_over]
  have hgover : g.hom ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = g.domain.ι ≫ ((ruledSurface L).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    show (e.inv ≫ Φ₀) ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = UW.ι ≫ ((ruledSurface L).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [Category.assoc, hΦ₀over]
    show e.inv ≫ U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫
        (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = UW.ι ≫ ruledSurface.π L ≫ (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    rw [← ruledSurface.totalSpaceIncl_comp_π, ← he_inv]
    simp only [Category.assoc]
    rfl
  have hgIsOver : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    AlgebraicGeometry.Scheme.PartialMap.isOver_iff.mpr hgover
  have hΦratOver : Φrat.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := inferInstance
  -- The zero section, moved to `U_W`.
  let σ₀W : ρ.source.toScheme ⟶ UW.toScheme := σ₀ ≫ e.hom
  have hσ₀W : σ₀W ≫ UW.ι ≫ ruledSurface.π L = CategoryTheory.CategoryStruct.id _ := by
    show (σ₀ ≫ e.hom) ≫ UW.ι ≫ ruledSurface.π L = _
    rw [Category.assoc, ← Category.assoc e.hom, he_hom]
    simp only [Category.assoc]
    rw [ruledSurface.totalSpaceIncl_comp_π, ← Category.assoc, hσ₀ι,
      AlgebraicGeometry.Scheme.zeroSection_comp]
  have hσΦW : σ₀W ≫ (ruledSurface L).toScheme.homOfLE hU ≫ Φrat.toPartialMap.hom = ρ.hom ≫ f := by
    rw [hhom]
    show (σ₀ ≫ e.hom) ≫ e.inv ≫ Φ₀ = _
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hσ₀Φ
  -- Step 7: resolution of the rational map by point blowups avoiding `U_W`.
  obtain ⟨S, β, hβ, havoid, πS, hπS, σ, Φ, hπS_eq, hconn, hσπ, hσβ, hσΦ', hΦover, hVdeg⟩ :=
    resolved_surface (r₀ := r₀) Φrat UW hU σ₀W hσ₀W hσΦW (by
      refine ⟨V, hVopen, hVne, fun y hy hcl => ?_⟩
      obtain ⟨ey, Φy, ⟨O, hO, jO, hjO1, hjO2⟩, h1, h2⟩ := hV y hy hcl
      refine ⟨ey, Φy, ⟨O, hO, jO ≫ e.hom, ?_, ?_⟩, h1, h2⟩
      · rw [Category.comp_id, Category.assoc, he_hom]
        exact hjO1
      · rw [hhom]
        show (jO ≫ e.hom) ≫ e.inv ≫ Φ₀ = _
        rw [Category.assoc, Iso.hom_inv_id_assoc]
        exact hjO2)
  -- `W` is by definition `P(O ⊕ L)`; the identification is the identity.
  let eW : (ruledSurface L).toScheme ≅
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := ρ.source.toVariety.toScheme.Modules)
          (show ρ.source.toVariety.toScheme.Modules from
            SheafOfModules.unit ρ.source.toVariety.toScheme.ringCatSheaf) L.toModules)).left :=
    CategoryTheory.Iso.refl _
  have hoSec : AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv
      = AlgebraicGeometry.Scheme.oSection L.toModules := Category.comp_id _
  -- The O-section `Σ₀` lies in `U_W`.
  have hSigma0 : Set.range (AlgebraicGeometry.Scheme.oSection L.toModules).base
      ⊆ (UW : Set (ruledSurface L).toScheme) := by
    rw [← ruledSurface.zeroSection_comp_totalSpaceIncl L, hUWset]
    rintro _ ⟨c, rfl⟩
    exact ⟨(AlgebraicGeometry.Scheme.zeroSection L.toModules).base c, hU0 (Set.mem_range_self c), rfl⟩
  have havoidSigma : IsBlowupTowerAvoiding β
      (Set.range (AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv).base) := by
    rw [hoSec]
    exact MiyaokaMori.Statement.IsPointBlowupSequenceOver.mono havoid (Set.compl_subset_compl.mpr hSigma0)
  have hdisj : Disjoint (ExceptionalCenters β hβ)
      (Set.range (AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv).base) := by
    rw [hoSec]
    haveI hiso : IsIso (β ∣_ UW) :=
      MiyaokaMori.Statement.IsPointBlowupSequenceOver.isIso_morphismRestrict UW β havoid
    have hle : UW ≤ (⨆ (V' : (ruledSurface L).toScheme.Opens) (_ : IsIso (β ∣_ V')), V') :=
      le_iSup₂ (f := fun (V' : (ruledSurface L).toScheme.Opens) (_ : IsIso (β ∣_ V')) => V') UW hiso
    rw [Set.disjoint_left]
    rintro x ⟨s, hs, rfl⟩ hx
    exact hs ((SetLike.le_def.mp hle) (hSigma0 hx))
  refine ⟨P, S, β, hβ, eW, πS, hπS, σ, Φ, hP, hjet, hvanish, havoidSigma, hdisj, ?_, hπS_eq, hconn, hσπ, ?_,
    hσΦ', hΦover, hVdeg, ?_⟩
  · exact Category.id_comp _
  · rw [hσβ, hoSec]
    show (σ₀ ≫ e.hom) ≫ UW.ι = _
    rw [Category.assoc, he_hom, ← Category.assoc, hσ₀ι]
    exact ruledSurface.zeroSection_comp_totalSpaceIncl L
  · unfold EmbeddingDegreeBound
    obtain ⟨V', hV'o, hV'ne, hV'⟩ := hVdeg
    exact ⟨V', hV'o, hV'ne, fun y hy hc => (hV' y hy hc).2.2⟩

end
