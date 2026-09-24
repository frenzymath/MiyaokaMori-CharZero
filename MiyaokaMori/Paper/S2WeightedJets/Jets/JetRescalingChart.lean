import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Jets.OfBasedJetChartSections
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraCoaction
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetOfAffineSpace

/-! # The rescaling action in jet chart coordinates

Formulas for the `𝔾_m`-rescaling action `jetRescalingAction` (`t ↦ λt`) on the chart coordinates of the
based jet scheme, and the section-level description of the "weight `m` defect":
* `GroupSchemeAction.weightDefect_app_apply`: `φ_m(a) = act^♯(a) − λ^m · pr₂^♯(a)` on every open set and section;
* `AlgebraicGeometry.Scheme.Modules.exists_kernel_section`: the kernel of a morphism of sheaves of modules is
  computed sectionwise;
* `jetRescalingAction_act_appLE_coeffClass`: `act^♯(d_q b) = λ^{q+1} · pr₂^♯(d_q b)`;
* consequently `jetRescalingAction_weightDefect_jetCoordinate`: `φ_{q+1}(d_q b) = 0`, i.e. the coefficient of
  order `q + 1` has weight `q + 1`.
Three auxiliary lemmas (the comorphism of the universal jet, naturality of `jetThickeningMap` with respect to
`sectionsHom`, coefficients of the rescaled universal jet) feed the third item.

Reference: §2 of the paper (the grading of the coordinate algebra of `J_k^s` by parameter rescaling; the
coefficient of order `q` has weight `q`); Demailly [Dem11, (0.3)].

Implementation note: `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with
`jetProjection_surjective` (so that `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and
`Ideal.Quotient.lift_mk` is rewritten with `erw` (it matches only up to unfolding `AdjoinRoot`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## General lemmas on sheaves of modules -/

/-- The kernel of a morphism of sheaves of modules is computed sectionwise: if `f : M ⟶ N`, `y ∈ M(U)` and
`f(y) = 0`, then `y` comes from `(ker f)(U)`.

Proof sketch: the forgetful functor from sheaves to presheaves of modules is a right adjoint (the left adjoint
is sheafification), so it preserves kernels; kernels of presheaves of modules are computed objectwise
(`PresheafOfModules.evaluation` preserves limits), and kernels in `ModuleCat` are `LinearMap.ker`. These
identifications are compatible with `kernel.ι`, so `y ∈ ker (f.val.app U)` yields the required `x`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_kernel_section {Y : AlgebraicGeometry.Scheme.{u}}
    {M N : Y.Modules} (f : M ⟶ N) (U : Y.Opens) (y : (M.val.obj (Opposite.op U) : Type u))
    (hy : (f.val.app (Opposite.op U)).hom y = 0) :
    ∃ x : ((CategoryTheory.Limits.kernel f).val.obj (Opposite.op U) : Type u),
      ((CategoryTheory.Limits.kernel.ι f).val.app (Opposite.op U)).hom x = y := by
  have hGa : (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).Additive :=
    inferInstanceAs (SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.evaluation Y.ringCatSheaf.obj (Opposite.op U)).Additive
  have hGf : ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f).hom y = 0 := hy
  let z : ((CategoryTheory.Limits.kernel
      ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f) : ModuleCat.{u} Γ(Y, U)) : Type u) :=
    (ModuleCat.kernelIsoKer ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f)).inv.hom ⟨y, hGf⟩
  refine ⟨(CategoryTheory.Limits.PreservesKernel.iso
    (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)) f).inv.hom z, ?_⟩
  have h1 := congrArg (fun φ : CategoryTheory.Limits.kernel
      ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f) ⟶
      (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).obj M => φ.hom z)
    (CategoryTheory.Limits.PreservesKernel.iso_inv_ι (SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)) f)
  have h3 := ModuleCat.kernelIsoKer_inv_kernel_ι_apply
    ((SheafOfModules.evaluation Y.ringCatSheaf (Opposite.op U)).map f) ⟨y, hGf⟩
  simp only [ModuleCat.hom_comp] at h1
  exact h1.trans h3

/-- Converse of the previous lemma: a section of the kernel is sent to `0` by `f` (`kernel.condition`,
evaluated on sections). -/
theorem AlgebraicGeometry.Scheme.Modules.kernel_ι_app_apply {Y : AlgebraicGeometry.Scheme.{u}}
    {M N : Y.Modules} (f : M ⟶ N) (U : Y.Opens)
    (x : ((CategoryTheory.Limits.kernel f).val.obj (Opposite.op U) : Type u)) :
    (f.val.app (Opposite.op U)).hom (((CategoryTheory.Limits.kernel.ι f).val.app (Opposite.op U)).hom x) = 0 := by
  have h : CategoryTheory.Limits.kernel.ι f ≫ f = 0 := CategoryTheory.Limits.kernel.condition f
  have h2 := congrArg (fun g : CategoryTheory.Limits.kernel f ⟶ N => (g.val.app (Opposite.op U)).hom x) h
  exact h2

/-- Section-level formula for the weight-`m` defect: `φ_m(a) = act^♯(a) − λ^m · pr₂^♯(a)`.
Here `W := 𝔾_m ×_k T`, `act^♯ = α.act.appLE (π⁻¹U) ((pr₂ ≫ π)⁻¹U)` (the inclusion of open sets comes from
`α.act_over` and is passed as the argument `hle`), `pr₂^♯ = pr₂.appLE (π⁻¹U) ((pr₂ ≫ π)⁻¹U)`, and `λ` is the
coordinate of `𝔾_m` (`LaurentPolynomial.T 1`) pulled back along `pr₁` to `W` and restricted to `(pr₂ ≫ π)⁻¹U`.

Proof sketch: unfold `GroupSchemeAction.weightDefect` and evaluate each piece on sections over `U`:
`pushforward.map`, `pushforwardComp.hom.app` and `pushforwardCongr.hom.app` are respectively the original map on
the preimage open set, the identity, and restriction along an equality of open sets, which together give
`Scheme.Hom.appLE`; `unitToPushforwardObjUnit` evaluates to `g.app V`; `unitMul c` is multiplication by the
restriction of `c`; and differences of morphisms are differences on sections. -/
theorem GroupSchemeAction.weightDefect_app_apply {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    (α : GmActionOver k T) (m : ℕ) (U : S.Opens) (a : Γ(T.left, T.hom ⁻¹ᵁ U))
    (hle : (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom) ⁻¹ᵁ U ≤
      α.act ⁻¹ᵁ (T.hom ⁻¹ᵁ U)) :
    (show Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))),
        (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom) ⁻¹ᵁ U) from
      ((GroupSchemeAction.weightDefect α m).val.app (Opposite.op U)).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
          (SheafOfModules.unit T.left.ringCatSheaf)).val.obj (Opposite.op U) : Type u) from a)) =
    (α.act.appLE (T.hom ⁻¹ᵁ U) _ hle).hom a -
      ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map
          (CategoryTheory.homOfLE le_top).op).hom
        ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
            (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
            (LaurentPolynomial.T 1)) ^ m) *
      ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appLE (T.hom ⁻¹ᵁ U) _
          (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom a := by
  -- first term on sections: restricting `act^♯ a` along `eqToHom` is `appLE`
  have hA : (show Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))), (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom) ⁻¹ᵁ U) from
      ((((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).map
          (SheafOfModules.unitToPushforwardObjUnit α.act.toRingCatSheafHom) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp α.act T.hom).hom.app _ ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardCongr α.act_over).hom.app _).val.app (Opposite.op U)).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
          (SheafOfModules.unit T.left.ringCatSheaf)).val.obj (Opposite.op U) : Type u) from a))) =
      (α.act.appLE (T.hom ⁻¹ᵁ U) _ hle).hom a := by
    show ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map (CategoryTheory.eqToHom
          (by rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, α.act_over])).op).hom
        ((α.act.app (T.hom ⁻¹ᵁ U)).hom a) = _
    show _ = ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map (CategoryTheory.homOfLE hle).op).hom ((α.act.app (T.hom ⁻¹ᵁ U)).hom a)
    congr 3
  -- second term on sections: `pr₂^♯ a` times the restriction of `c` (`unitMul` is `x ↦ x • res c`)
  have hB : (show Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))), (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom) ⁻¹ᵁ U) from
      ((((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).map
          (SheafOfModules.unitToPushforwardObjUnit (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).toRingCatSheafHom) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardComp (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) T.hom).hom.app _ ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom)).map
          (AlgebraicGeometry.Scheme.Modules.unitMul ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
          (LaurentPolynomial.T 1)) ^ m))).val.app (Opposite.op U)).hom
        (show (((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
          (SheafOfModules.unit T.left.ringCatSheaf)).val.obj (Opposite.op U) : Type u) from a))) =
      ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map (CategoryTheory.homOfLE le_top).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
          (LaurentPolynomial.T 1)) ^ m) *
        ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appLE (T.hom ⁻¹ᵁ U) _ (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom a := by
    show ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).app (T.hom ⁻¹ᵁ U)).hom a *
        ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map (CategoryTheory.homOfLE le_top).op).hom ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
          (LaurentPolynomial.T 1)) ^ m) = _
    rw [mul_comm]
    congr 1
    exact (congrArg (fun φ : Γ(T.left, T.hom ⁻¹ᵁ U) ⟶ Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))), (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom) ⁻¹ᵁ U) => φ.hom a)
      (AlgebraicGeometry.Scheme.Hom.appLE_eq_app (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))))).symm
  exact (congrArg₂ (· - ·) hA hB : _)

/-- Let `g : Y ⟶ Z`, `V ⊆ Y` open, `Z_U ⊆ Z` affine open and `σ : Γ(Z, Z_U) → Γ(Y, V)`. If
`V.ι ≫ g = V.toSpecΓ ≫ Spec.map σ ≫ hU.fromSpec`, then the comorphism of `g` on `(Z_U, V)` is `σ`.

Proof sketch: apply `appLE Z_U ⊤` to both sides of the hypothesis; the left side is `g.appLE Z_U V ≫ V.topIso⁻¹`
(`comp_appLE`, `Opens.ι_appLE`), the right side becomes `σ ≫ V.topIso⁻¹` by `IsAffineOpen.fromSpec_app_self`,
`ΓSpecIso_naturality` and `Opens.toSpecΓ_appTop`; cancel the isomorphism `V.topIso`. -/
theorem AlgebraicGeometry.Scheme.appLE_of_ι_comp_fromSpec {Y Z : AlgebraicGeometry.Scheme.{u}}
    (V : Y.Opens) {ZU : Z.Opens} (hU : AlgebraicGeometry.IsAffineOpen ZU) (g : Y ⟶ Z) (σ : Γ(Z, ZU) ⟶ Γ(Y, V))
    (hfac : V.ι ≫ g = V.toSpecΓ ≫ AlgebraicGeometry.Spec.map σ ≫ hU.fromSpec)
    (hle : V ≤ g ⁻¹ᵁ ZU) :
    g.appLE ZU V hle = σ := by
  -- (1) V.toSpecΓ ≫ Spec.map (g.appLE) ≫ fromSpec = V.ι ≫ g (toSpecΓ_SpecMap_appLE + toSpecΓ_fromSpec + resLE_comp_ι)
  have h1 : V.toSpecΓ ≫ AlgebraicGeometry.Spec.map (g.appLE ZU V hle) ≫ hU.fromSpec = V.ι ≫ g := by
    rw [← CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE,
      CategoryTheory.Category.assoc, AlgebraicGeometry.IsAffineOpen.toSpecΓ_fromSpec,
      AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  -- (2) cancel the monomorphism `fromSpec`
  have h2 : V.toSpecΓ ≫ AlgebraicGeometry.Spec.map (g.appLE ZU V hle) =
      V.toSpecΓ ≫ AlgebraicGeometry.Spec.map σ := by
    have h := h1.trans hfac
    rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc,
      CategoryTheory.cancel_mono] at h
    exact h
  -- (3) take global sections: `toSpecΓ.appTop = ΓSpecIso.hom ≫ topIso.inv` is an isomorphism; after
-- `ΓSpecIso_naturality`, cancel it
  have h3 := congrArg (fun φ : V.toScheme ⟶ AlgebraicGeometry.Spec Γ(Z, ZU) => φ.appTop) h2
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop] at h3
  rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc, CategoryTheory.cancel_mono,
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality, AlgebraicGeometry.Scheme.ΓSpecIso_naturality,
    CategoryTheory.cancel_epi] at h3
  exact h3

/-- The open-set inclusion hypothesis of `appLE_of_ι_comp_fromSpec` follows from the factorization itself:
the image of `fromSpec` is `ZU` (`IsAffineOpen.range_fromSpec`). -/
theorem AlgebraicGeometry.Scheme.le_preimage_of_ι_comp_fromSpec {Y Z : AlgebraicGeometry.Scheme.{u}}
    (V : Y.Opens) {ZU : Z.Opens} (hU : AlgebraicGeometry.IsAffineOpen ZU) (g : Y ⟶ Z) (σ : Γ(Z, ZU) ⟶ Γ(Y, V))
    (hfac : V.ι ≫ g = V.toSpecΓ ≫ AlgebraicGeometry.Spec.map σ ≫ hU.fromSpec) :
    V ≤ g ⁻¹ᵁ ZU := by
  intro y hy
  have h : g.base y = hU.fromSpec.base ((V.toSpecΓ ≫ AlgebraicGeometry.Spec.map σ).base ⟨y, hy⟩) :=
    congrArg (fun f : V.toScheme ⟶ Z => f.base ⟨y, hy⟩) hfac
  show g.base y ∈ ZU
  rw [h]
  have hm : hU.fromSpec ((V.toSpecΓ ≫ AlgebraicGeometry.Spec.map σ) ⟨y, hy⟩) ∈ Set.range hU.fromSpec :=
    Set.mem_range_self _
  rw [hU.range_fromSpec] at hm
  exact hm


/-- Pulling back a global section along `f` and then restricting to `f⁻¹V` equals restricting to `V` first and
then pulling back (`Scheme.Hom.naturality` on sections). -/
theorem AlgebraicGeometry.Scheme.Hom.map_appTop_eq_app_map {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (x : Γ(Y, ⊤)) :
    (X.presheaf.map (CategoryTheory.homOfLE (le_top : f ⁻¹ᵁ V ≤ ⊤)).op).hom (f.appTop.hom x) =
      (f.app V).hom ((Y.presheaf.map (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op).hom x) := by
  have h := congrArg (fun φ : Γ(Y, ⊤) ⟶ Γ(X, f ⁻¹ᵁ V) => φ.hom x)
    (f.naturality (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  exact h.symm

variable {k : Type u} [Field k]

/-- Naturality of `jetThickeningMap` with respect to `sectionsHom`: for `g : W' ⟶ W` over `k`, `V ⊆ W` open and
`p ∈ Γ(W, V)[t]/(t^{r+1})`, `(g × 𝟙)^♯ (sectionsHom_V p) = sectionsHom_{g⁻¹V} (g^♯ applied coefficientwise to p)`.

Proof sketch: both sides are ring homomorphisms out of the truncated polynomial ring, so it suffices to compare
them on constants (use `jetThickeningMap_proj`: `(g × 𝟙) ≫ pr = pr ≫ g`) and on `X ↦ t` (use
`jetThickeningMap_snd`: `(g × 𝟙) ≫ snd = snd`, and the definition of `jetThickening.parameter`). -/
theorem jetThickeningMap_appLE_sectionsHom (r : ℕ) {W W' : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [W'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : W' ⟶ W) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] (V : W.Opens)
    (p : MiyaokaMori.Jet.TruncatedJetRing Γ(W, V) r)
    (hle : jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V) ≤
      jetThickeningMap (k := k) r g ⁻¹ᵁ (jetThickeningProj (k := k) r W ⁻¹ᵁ V)) :
    ((jetThickeningMap (k := k) r g).appLE _ _ hle).hom (jetThickening.sectionsHom (k := k) r W V p) =
      jetThickening.sectionsHom (k := k) r W' (g ⁻¹ᵁ V)
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (g.app V).hom p) :=
  jetThickening.sectionsHom_jetThickeningMap (k := k) r g V p hle

/-- Pure algebra: after the rescaling `t ↦ c·t` and applying `σ` to the coefficients, the coefficient of order
`n` of the universal jet is `c^n · σ(D_n b)`. -/
theorem BasedJetAlgebra.coeff_rescale_map_universalJet {R B S : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] (ε : B →ₐ[R] R) (r : ℕ) (σ : BasedJetAlgebra ε r →+* S) (c : S) (n : ℕ) (hn : n ≤ r) (b : B) :
    MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn
        (MiyaokaMori.Jet.TruncatedJetRing.rescale r c
          (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r σ (BasedJetAlgebra.universalJet ε r b))) =
      c ^ n * σ (BasedJetAlgebra.coeffClass ε r n b) := by
  rw [MiyaokaMori.Jet.TruncatedJetRing.coeff_rescale, MiyaokaMori.Jet.TruncatedJetRing.coeff_map,
    BasedJetAlgebra.coeff_universalJet]

variable {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-! ## The action of `ρ_λ` on sections -/

/-- The scalar `λ` appearing when `ρ_λ` acts on sections: the coordinate `T 1` of `𝔾_m` pulled back along `λ`
to `V` and restricted to `V₀`. -/

noncomputable def jetThickening.rescaleSection (r : ℕ) (V : AlgebraicGeometry.Scheme.{u})
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (lam : V ⟶ Gm k) (V₀ : V.Opens) :
    Γ(V, V₀) :=
  (V.presheaf.map (CategoryTheory.homOfLE le_top).op).hom
    (lam.appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
        (LaurentPolynomial.T 1)))

/-- `ρ_λ` sends the parameter `t` to `pr^♯(λ) · t` (the section-level form of "the coaction is `t ↦ λ ⊗ t`").

Proof sketch: `jetThickening.rescaleBy_snd` gives `ρ_λ ≫ snd = τ_λ = pullback.lift (pr ≫ λ) snd _ ≫
jetBaseRescaling k r`, and `parameter r V = snd.appTop (ΓSpecIso⁻¹ [X])`. Split `τ_λ` as
`pullbackSpecIso.hom ≫ Spec.map (ofHom coaction)`; on global sections `Spec.map (ofHom φ)` is `φ`
(`ΓSpecIso_naturality`), `coaction [X] = T 1 ⊗ [X]` (`AdjoinRoot.lift_root`), and `pullbackSpecIso` sends
`a ⊗ b` to `pr₁^♯(a) · pr₂^♯(b)`. Hence `τ_λ^♯(t) = (pr ≫ λ)^♯(T 1) · snd^♯([X]) = pr^♯(λ) · t`
(`pullback.lift_fst`, `pullback.lift_snd`, `Scheme.comp_appTop`). -/

theorem jetThickening.rescaleBy_appTop_parameter (r : ℕ) (V : AlgebraicGeometry.Scheme.{u})
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (lam : V ⟶ Gm k)
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) :
    (jetThickening.rescaleBy (k := k) r V lam hlam).appTop.hom
        (jetThickening.parameter (k := k) r V) =
      (jetThickeningProj (k := k) r V).appTop.hom
          (lam.appTop.hom
            ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
              (LaurentPolynomial.T 1))) *
        jetThickening.parameter (k := k) r V := by
  -- notation: `ξ` is the coordinate `[X]` of `D_r`, `μ` the coordinate `T 1` of `𝔾_m` (both as global sections of Spec)
  set ξ : Γ(AlgebraicGeometry.Spec (CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r)), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r))).inv.hom
      (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))) with hξ
  set μ : Γ(AlgebraicGeometry.Spec (CommRingCat.of (LaurentPolynomial k)), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
      (LaurentPolynomial.T 1) with hμ
  -- the parameter `t = snd^♯ ξ` (by definition)
  have hpar : jetThickening.parameter (k := k) r V =
      (CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom ξ := rfl
  -- (1) ρ^♯(t) = (ρ ≫ snd)^♯ ξ = τ^♯ ξ
  have h1 : (jetThickening.rescaleBy (k := k) r V lam hlam).appTop.hom
      (jetThickening.parameter (k := k) r V) =
      (jetThickening.rescaleParam (k := k) r V lam hlam).appTop.hom ξ := by
    have h := congrArg (fun φ : jetThickening (k := k) r V ⟶ jetBase k r => φ.appTop.hom ξ)
      (jetThickening.rescaleBy_snd (k := k) r V lam hlam)
    exact h
  -- (2) (Spec.map coaction)^♯ ξ = ΓSpecIso⁻¹(T 1 ⊗ [X]) (ΓSpecIso_inv_naturality + AdjoinRoot.lift_root)
  have h2 : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescaling.coaction k r))).appTop.hom ξ =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
        (TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k)
          (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))) := by
    have h := congrArg (fun φ : CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r) ⟶
        Γ(AlgebraicGeometry.Spec (CommRingCat.of (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))), ⊤) =>
        φ.hom (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (jetBaseRescaling.coaction k r)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    have hc : jetBaseRescaling.coaction k r (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))) =
        TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k)
          (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))) :=
      AdjoinRoot.lift_root (jetBaseRescaling.coaction_wellDefined k r)
    rw [hc] at h
    exact h.symm
  -- (3) in `Γ(Spec(A ⊗ B))`, `a ⊗ b = (a ⊗ 1)(1 ⊗ b)`, and `pullbackSpecIso.hom ≫ Spec.map includeLeft = fst`, etc.
  have hfst := congrArg (fun φ : CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (MiyaokaMori.Jet.TruncatedJetRing k r)))) ⟶
        AlgebraicGeometry.Spec (CommRingCat.of (LaurentPolynomial k)) => φ.appTop.hom μ)
    (AlgebraicGeometry.pullbackSpecIso_hom_fst k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))
  have hsnd := congrArg (fun φ : CategoryTheory.Limits.pullback
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k))))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k (MiyaokaMori.Jet.TruncatedJetRing k r)))) ⟶
        AlgebraicGeometry.Spec (CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r)) => φ.appTop.hom ξ)
    (AlgebraicGeometry.pullbackSpecIso_hom_snd k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hfst hsnd
  -- (Spec.map includeLeft)^♯ μ = ΓSpecIso⁻¹(T 1 ⊗ 1), (Spec.map includeRight)^♯ ξ = ΓSpecIso⁻¹(1 ⊗ [X])
  have hL : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : LaurentPolynomial k →+*
          TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).appTop.hom μ =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
        (TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k) (1 : MiyaokaMori.Jet.TruncatedJetRing k r)) := by
    have h := congrArg (fun φ : CommRingCat.of (LaurentPolynomial k) ⟶
        Γ(AlgebraicGeometry.Spec (CommRingCat.of (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))), ⊤) =>
        φ.hom (LaurentPolynomial.T 1))
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : LaurentPolynomial k →+*
          TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h.symm
  have hR : (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : MiyaokaMori.Jet.TruncatedJetRing k r →ₐ[k]
          TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)) : MiyaokaMori.Jet.TruncatedJetRing k r →+*
          TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).appTop.hom ξ =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)))).inv.hom
        (TensorProduct.tmul k (1 : LaurentPolynomial k)
          (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1)))) := by
    have h := congrArg (fun φ : CommRingCat.of (MiyaokaMori.Jet.TruncatedJetRing k r) ⟶
        Γ(AlgebraicGeometry.Spec (CommRingCat.of (TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))), ⊤) =>
        φ.hom (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))))
      (AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : MiyaokaMori.Jet.TruncatedJetRing k r →ₐ[k]
          TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)) : MiyaokaMori.Jet.TruncatedJetRing k r →+*
          TensorProduct k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    exact h.symm
  rw [hL] at hfst
  rw [hR] at hsnd
  -- (3) by definition `τ^♯ ξ = lift^♯ (pbIso^♯ ((Spec.map coaction)^♯ ξ))`
  have h3 : (jetThickening.rescaleParam (k := k) r V lam hlam).appTop.hom ξ =
      (CategoryTheory.Limits.pullback.lift
          (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam)
          (CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
          (jetThickening.rescaleParam_cond (k := k) r V lam hlam)).appTop.hom
        ((AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom.appTop.hom
          ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescaling.coaction k r))).appTop.hom ξ)) := rfl
  -- (4) pbIso^♯ (ΓSpecIso⁻¹ (T 1 ⊗ [X])) = fst^♯ μ · snd^♯ ξ
  have htmul : TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k)
        (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))) =
      TensorProduct.tmul k (LaurentPolynomial.T 1 : LaurentPolynomial k) (1 : MiyaokaMori.Jet.TruncatedJetRing k r) *
        TensorProduct.tmul k (1 : LaurentPolynomial k)
          (AdjoinRoot.root ((Polynomial.X : Polynomial k) ^ (r + 1))) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h4 : (AlgebraicGeometry.pullbackSpecIso k (LaurentPolynomial k) (MiyaokaMori.Jet.TruncatedJetRing k r)).hom.appTop.hom
        ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom (jetBaseRescaling.coaction k r))).appTop.hom ξ) =
      (CategoryTheory.Limits.pullback.fst (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom μ *
        (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop.hom ξ := by
    rw [h2, htmul, map_mul, map_mul]
    exact congrArg₂ (· * ·) hfst hsnd
  -- (5) assemble: `lift ≫ fst = pr ≫ λ`, `lift ≫ snd = snd`
  have h5 := congrArg (fun φ : jetThickening (k := k) r V ⟶ Gm k => φ.appTop.hom μ)
    (CategoryTheory.Limits.pullback.lift_fst
      (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam)
      (CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      (jetThickening.rescaleParam_cond (k := k) r V lam hlam))
  have h6 := congrArg (fun φ : jetThickening (k := k) r V ⟶ jetBase k r => φ.appTop.hom ξ)
    (CategoryTheory.Limits.pullback.lift_snd
      (CategoryTheory.Limits.pullback.fst (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ lam)
      (CategoryTheory.Limits.pullback.snd (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      (jetThickening.rescaleParam_cond (k := k) r V lam hlam))
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at h5 h6
  rw [h1, h3, h4, map_mul, hpar]
  exact congrArg₂ (· * ·) h5 h6

/-- `ρ_λ^♯` commutes with rescaling of truncated polynomials:
`ρ_λ^♯ (sectionsHom_{V₀} p) = sectionsHom_{V₀} (rescale λ|_{V₀} p)`.

Proof sketch: both sides are ring homomorphisms `Γ(V, V₀)[t]/(t^{r+1}) → Γ(V ×_k D_r, pr⁻¹V₀)`, so compare them
on generators. On a constant `a` both give `pr^♯(a)` (`rescaleBy_proj`, `rescale_eta`); on `X ↦ t` the left side
is `(pr^♯(λ) · t)|_{pr⁻¹V₀}` by `rescaleBy_appTop_parameter`, the right side is `pr^♯(λ|_{V₀}) · t|`, and the
two agree by naturality of `pr^♯` with respect to restriction (`appLE_map` / `map_appLE`). -/

theorem jetThickening.rescaleBy_appLE_sectionsHom (r : ℕ) (V : AlgebraicGeometry.Scheme.{u})
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (lam : V ⟶ Gm k)
    (hlam : lam ≫ (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (V₀ : V.Opens) (p : MiyaokaMori.Jet.TruncatedJetRing Γ(V, V₀) r)
    (hle : jetThickeningProj (k := k) r V ⁻¹ᵁ V₀ ≤
      jetThickening.rescaleBy (k := k) r V lam hlam ⁻¹ᵁ (jetThickeningProj (k := k) r V ⁻¹ᵁ V₀)) :
    ((jetThickening.rescaleBy (k := k) r V lam hlam).appLE
        (jetThickeningProj (k := k) r V ⁻¹ᵁ V₀) _ hle).hom
      (jetThickening.sectionsHom (k := k) r V V₀ p) =
    jetThickening.sectionsHom (k := k) r V V₀
      (MiyaokaMori.Jet.TruncatedJetRing.rescale r
        (jetThickening.rescaleSection (k := k) r V lam V₀) p) := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  unfold jetThickening.sectionsHom
  rw [MiyaokaMori.Jet.lift_jetProjection, MiyaokaMori.Jet.TruncatedJetRing.rescale_projection,
    MiyaokaMori.Jet.lift_jetProjection]
  simp only [Polynomial.coe_eval₂RingHom]
  rw [Polynomial.eval₂_comp, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.hom_eval₂]
  congr 1
  · -- constants: `ρ^♯ ∘ pr^♯ = pr^♯` (since `ρ ≫ pr = pr`)
    ext a
    have h1 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetThickening.rescaleBy (k := k) r V lam hlam)
      (jetThickeningProj (k := k) r V) V₀ (jetThickeningProj (k := k) r V ⁻¹ᵁ V₀) hle
    have h3 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (jetThickening.rescaleBy_proj (k := k) r V lam hlam) V₀
      (jetThickeningProj (k := k) r V ⁻¹ᵁ V₀) hle le_rfl
    rw [h1] at h3
    have h4 := congrArg (fun φ : Γ(V, V₀) ⟶ Γ(jetThickening (k := k) r V,
      jetThickeningProj (k := k) r V ⁻¹ᵁ V₀) => φ.hom a) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h4
    rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app] at h4
    exact h4
  · -- the parameter: `ρ^♯(t|) = (pr^♯ λ · t)| = pr^♯(λ|) · t|`
    have h1 := AlgebraicGeometry.Scheme.Hom.map_appLE (jetThickening.rescaleBy (k := k) r V lam hlam) hle
      (CategoryTheory.homOfLE (le_top : jetThickeningProj (k := k) r V ⁻¹ᵁ V₀ ≤ ⊤)).op
    have h2 := congrArg (fun φ : Γ(jetThickening (k := k) r V, ⊤) ⟶
      Γ(jetThickening (k := k) r V, jetThickeningProj (k := k) r V ⁻¹ᵁ V₀) =>
        φ.hom (jetThickening.parameter (k := k) r V)) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    rw [h2]
    show ((jetThickening (k := k) r V).presheaf.map (CategoryTheory.homOfLE le_top).op).hom
        ((jetThickening.rescaleBy (k := k) r V lam hlam).appTop.hom (jetThickening.parameter (k := k) r V)) = _
    rw [jetThickening.rescaleBy_appTop_parameter, map_mul]
    congr 1
    exact AlgebraicGeometry.Scheme.Hom.map_appTop_eq_app_map (jetThickeningProj (k := k) r V) V₀ _

/-- The universal based jet maps `pr⁻¹J_U` into `π⁻¹U` (`ι_glueMorphisms` and
`le_preimage_of_ι_comp_fromSpec`). -/
theorem relativeJetScheme.universalJet_le (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U ≤
      relativeJetScheme.universalJet (k := k) Z s hs r ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1) := by
  let _ : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  exact AlgebraicGeometry.Scheme.le_preimage_of_ι_comp_fromSpec _ (U.2.preimage Z.hom)
    (relativeJetScheme.universalJet (k := k) Z s hs r)
    (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U))
    (AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms
      ((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover
        (fun U : C.AffineZariskiSite =>
          jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
            relativeJetScheme.chartOpen (k := k) Z s hs r U)
        (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r))
      (fun U =>
        (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
            relativeJetScheme.chartOpen (k := k) Z s hs r U).toSpecΓ ≫
          AlgebraicGeometry.Spec.map
            (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U)) ≫
          (U.2.preimage Z.hom).fromSpec)
      (relativeJetScheme.universalJet_glue_compat (k := k) Z s hs r) U)

/-- The comorphism of the universal based jet on the chart `U` is `universalJetSections U`: `universalJet` is a
`glueMorphisms`, `Cover.ι_glueMorphisms` gives
`(pr⁻¹J_U).ι ≫ universalJet = toSpecΓ ≫ Spec.map (universalJetSections U) ≫ fromSpec`, and we conclude with
`appLE_of_ι_comp_fromSpec`. -/
theorem relativeJetScheme.universalJet_appLE (U : C.AffineZariskiSite) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    ∀ (hle : jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U ≤
      relativeJetScheme.universalJet (k := k) Z s hs r ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1)),
    (relativeJetScheme.universalJet (k := k) Z s hs r).appLE (Z.hom ⁻¹ᵁ U.1) _ hle =
      CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U) := by
  let _ : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  intro hle
  have h := AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms
    ((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).openCoverOfIsOpenCover
      (fun U : C.AffineZariskiSite =>
        jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U)
      (relativeJetScheme.universalJet_isOpenCover (k := k) Z s hs r))
    (fun U =>
      (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U).toSpecΓ ≫
        AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U)) ≫
        (U.2.preimage Z.hom).fromSpec)
    (relativeJetScheme.universalJet_glue_compat (k := k) Z s hs r) U
  exact AlgebraicGeometry.Scheme.appLE_of_ι_comp_fromSpec _ (U.2.preimage Z.hom)
    (relativeJetScheme.universalJet (k := k) Z s hs r)
    (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U)) h hle

/-- The rescaling action on jet coordinates: `act^♯(d_q b) = λ^{q+1} · pr₂^♯(d_q b)`, where `d_q b` is viewed as
an element of `Γ(J, π⁻¹U)` (chart sections transported to `π⁻¹U` via `preimage_eq_chartOpen`).

Proof sketch (each step is a lemma of this file or of an upstream module):
(1) by definition `(jetRescalingAction Z s hs r).act = (ofBasedJet W x).left` with `W = 𝔾_m ×_k J`,
    `x = ρ_λ ≫ x₀` and `x₀ = toBasedJet pr₂ = jetThickeningMap pr₂ ≫ universalJet`;
(2) `relativeJetScheme.ofBasedJet_appLE_coeffClass`: `act^♯(chartSections(d_q b))` is the `t^{q+1}`-coefficient
    of `x^♯ b`;
(3) `x^♯ b = ρ_λ^♯((pr₂ × 𝟙)^♯(universalJet^♯ b))`, and `universalJet^♯ b = universalJetSections U b`
    `= sectionsHom (map chartSections (algebraic universal jet of b))` (`universalJet_appLE`);
(4) `jetThickeningMap_appLE_sectionsHom` moves `(pr₂ × 𝟙)^♯` inside `sectionsHom`;
(5) `jetThickening.rescaleBy_appLE_sectionsHom`: `ρ_λ^♯ (sectionsHom p) = sectionsHom (rescale λ p)`;
(6) `BasedJetAlgebra.coeff_rescale_map_universalJet` extracts the `t^{q+1}`-coefficient, giving
    `λ^{q+1} · pr₂^♯(chartSections(d_q b))`;
(7) transport both sides along `eqToHom hU` to `π⁻¹U` (`appLE_map`, `map_appLE`). -/
theorem jetRescalingAction_act_appLE_coeffClass (U : C.AffineZariskiSite) (q : Fin r)
    (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
    (hU : (relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1 = relativeJetScheme.chartOpen (k := k) Z s hs r U)
    (hle : (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
          (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U.1 ≤
      (jetRescalingAction (k := k) Z s hs r).act ⁻¹ᵁ ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1)) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    ((jetRescalingAction (k := k) Z s hs r).act.appLE
        ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) _ hle).hom
      (((relativeJetScheme (k := k) Z s hs r).left.presheaf.map (CategoryTheory.eqToHom hU).op).hom
        ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
          (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r ((q : ℕ) + 1) b))) =
    ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map
          (CategoryTheory.homOfLE le_top).op).hom
        ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
            ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
            (LaurentPolynomial.T 1)) ^ ((q : ℕ) + 1)) *
      ((CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appLE
          ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1) _
          (AlgebraicGeometry.Scheme.Hom.comp_preimage _ _ _).le).hom
        (((relativeJetScheme (k := k) Z s hs r).left.presheaf.map (CategoryTheory.eqToHom hU).op).hom
          ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
            (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r ((q : ℕ) + 1) b))) := by
  let _ := relativeJetScheme.sectionsAlgebra Z U.1
  -- notation (verbatim as in the definition of `jetRescalingAction`)
  let J := relativeJetScheme (k := k) Z s hs r
  let W : CategoryTheory.Over C := CategoryTheory.Over.mk
    (CategoryTheory.Limits.pullback.snd (Gm k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ J.hom)
  let _ : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let _ : J.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let lam : W.left ⟶ Gm k := CategoryTheory.Limits.pullback.fst _ _
  let ρ : jetThickening (k := k) r W.left ⟶ jetThickening (k := k) r W.left :=
    jetThickening.rescaleBy (k := k) r W.left lam (jetRescalingAction_lam_over (k := k) Z s hs r)
  let a : W ⟶ J := CategoryTheory.Over.homMk (CategoryTheory.Limits.pullback.snd _ _) rfl
  let x₀ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W) :=
    (relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv a
  let x : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W) :=
    ⟨ρ ≫ x₀.1, jetRescalingAction_point_prop (k := k) Z s hs r⟩
  have hact : (jetRescalingAction (k := k) Z s hs r).act =
      (relativeJetScheme.ofBasedJet (k := k) Z s hs r W x).left := rfl
  -- (7) first change the source open set of `act^♯` to the chart image along `eqToHom hU`
  have hB := AlgebraicGeometry.Scheme.Hom.map_appLE (jetRescalingAction (k := k) Z s hs r).act hle
    (CategoryTheory.eqToHom hU).op
  have hB' := congrArg (fun φ => φ.hom ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
    (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r ((q : ℕ) + 1) b))) hB
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hB'
  rw [hB']
  -- (2) `ofBasedJet` on the chart: `act^♯(d_q b)` is the coefficient of order `q + 1` of `x^♯ b`
  have hφ := relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W x U
  have hC := relativeJetScheme.ofBasedJet_appLE_coeffClass (k := k) Z s hs r W x U q b
    (by rw [← hU]; exact hle) hφ
  refine hC.trans ?_
  -- (3)(4)(5) expand `x^♯ b`: `x = ρ ≫ (pr₂ × 𝟙) ≫ universalJet`, take comorphisms piece by piece
  let V₀ : J.left.Opens := relativeJetScheme.chartOpen (k := k) Z s hs r U
  let pr₂ : W.left ⟶ J.left := CategoryTheory.Limits.pullback.snd _ _
  have hpr₂ : pr₂.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.Over.w_assoc a _⟩
  have e₁ := relativeJetScheme.universalJet_le (k := k) Z s hs r U
  have e₂ : jetThickeningProj (k := k) r W.left ⁻¹ᵁ (pr₂ ⁻¹ᵁ V₀) ≤
      jetThickeningMap (k := k) r pr₂ ⁻¹ᵁ (jetThickeningProj (k := k) r J.left ⁻¹ᵁ V₀) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage (jetThickeningMap (k := k) r pr₂)
      (jetThickeningProj (k := k) r J.left) V₀, jetThickeningMap_proj,
      AlgebraicGeometry.Scheme.Hom.comp_preimage]
  have e₃ : jetThickeningProj (k := k) r W.left ⁻¹ᵁ (pr₂ ⁻¹ᵁ V₀) ≤
      ρ ⁻¹ᵁ (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (pr₂ ⁻¹ᵁ V₀)) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage ρ (jetThickeningProj (k := k) r W.left) (pr₂ ⁻¹ᵁ V₀),
      jetThickening.rescaleBy_proj]
  have hres : W.hom ⁻¹ᵁ U.1 ≤ pr₂ ⁻¹ᵁ V₀ := by
    show pr₂ ⁻¹ᵁ (J.hom ⁻¹ᵁ U.1) ≤ pr₂ ⁻¹ᵁ V₀
    rw [show J.hom ⁻¹ᵁ U.1 = V₀ from hU]
  have hres' : jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1) ≤
      jetThickeningProj (k := k) r W.left ⁻¹ᵁ (pr₂ ⁻¹ᵁ V₀) := fun _ hx => hres hx
  have hD : x.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1)) hφ =
      (((relativeJetScheme.universalJet (k := k) Z s hs r).appLE (Z.hom ⁻¹ᵁ U.1)
          (jetThickeningProj (k := k) r J.left ⁻¹ᵁ V₀) e₁ ≫
        (jetThickeningMap (k := k) r pr₂).appLE (jetThickeningProj (k := k) r J.left ⁻¹ᵁ V₀)
          (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (pr₂ ⁻¹ᵁ V₀)) e₂) ≫
        ρ.appLE (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (pr₂ ⁻¹ᵁ V₀))
          (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (pr₂ ⁻¹ᵁ V₀)) e₃) ≫
        (jetThickening (k := k) r W.left).presheaf.map (CategoryTheory.homOfLE hres').op := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE, AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE,
      AlgebraicGeometry.Scheme.Hom.appLE_map]
    rfl
  have hD' := congrArg (fun φ => φ.hom b) hD
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hD'
  rw [hD', relativeJetScheme.universalJet_appLE (k := k) Z s hs r U e₁]
  -- (3) `universalJetSections = sectionsHom ∘ map chartSections ∘ (algebraic universal jet)` (by definition)
  rw [show (CommRingCat.ofHom (relativeJetScheme.universalJetSections (k := k) Z s hs r U)).hom b =
      jetThickening.sectionsHom (k := k) r J.left V₀
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (relativeJetScheme.chartSections (k := k) Z s hs r U).hom
          (BasedJetAlgebra.universalJet (relativeJetScheme.augmentation Z s hs U.1) r b)) from rfl]
  -- (4) `(pr₂ × 𝟙)^♯` commutes with `sectionsHom`
  rw [jetThickening.sectionsHom_jetThickeningMap (k := k) r pr₂ V₀ _ e₂]
  -- (5) `ρ^♯` and `sectionsHom`: rescaling
  simp only [ρ]
  rw [jetThickening.rescaleBy_appLE_sectionsHom (k := k) r W.left lam
    (jetRescalingAction_lam_over (k := k) Z s hs r) (pr₂ ⁻¹ᵁ V₀) _ e₃]
  -- restrict to `pr⁻¹(w⁻¹U)` and take the coefficient of order `q + 1`
  rw [← jetThickening.sectionsHom_restrict (k := k) r W.left hres, jetThickening.coeff_sectionsHom,
    MiyaokaMori.Jet.TruncatedJetRing.coeff_map, MiyaokaMori.Jet.TruncatedJetRing.coeff_rescale,
    MiyaokaMori.Jet.TruncatedJetRing.coeff_map]
  erw [MiyaokaMori.Jet.TruncatedJetRing.coeff_map, BasedJetAlgebra.coeff_universalJet]
  rw [map_mul, map_pow]
  congr 1
  · -- the restriction of `λ`: both sides are `(res (global section of λ))^(q+1)`
    rw [map_pow]
    congr 1
    show ((W.left.presheaf.map (CategoryTheory.homOfLE hres).op).hom
        ((W.left.presheaf.map (CategoryTheory.homOfLE le_top).op).hom (lam.appTop.hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
            (LaurentPolynomial.T 1))))) =
      ((W.left.presheaf.map (CategoryTheory.homOfLE (le_top : W.hom ⁻¹ᵁ U.1 ≤ ⊤)).op).hom (lam.appTop.hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
            (LaurentPolynomial.T 1))))
    rw [← CommRingCat.comp_apply, ← W.left.presheaf.map_comp]
    have hh : ((CategoryTheory.homOfLE (le_top : pr₂ ⁻¹ᵁ V₀ ≤ ⊤)).op ≫ (CategoryTheory.homOfLE hres).op) =
        (CategoryTheory.homOfLE (le_top : W.hom ⁻¹ᵁ U.1 ≤ ⊤)).op := rfl
    rw [hh]
  · -- transport the restriction of `pr₂^♯` along `eqToHom hU`
    show (pr₂.appLE V₀ (W.hom ⁻¹ᵁ U.1) (fun _ hx => hres hx)).hom _ = _
    exact (congrArg (fun φ : Γ(J.left, V₀) ⟶ Γ(W.left, W.hom ⁻¹ᵁ U.1) => φ.hom
      ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
        (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r ((q : ℕ) + 1) b)))
      (AlgebraicGeometry.Scheme.Hom.map_appLE pr₂
        (AlgebraicGeometry.Scheme.Hom.comp_preimage pr₂ J.hom U.1).le (CategoryTheory.eqToHom hU).op)).symm

/-- Inclusion of open sets (taking preimages of `U` on both sides of `act_over`; in fact an equality). -/
theorem GroupSchemeAction.preimage_le_act_preimage {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    (α : GmActionOver k T) (U : S.Opens) :
    (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom) ⁻¹ᵁ U ≤
      α.act ⁻¹ᵁ (T.hom ⁻¹ᵁ U) := by
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, α.act_over]

/-- The weight-`(q+1)` defect of the jet coordinate `d_q b` vanishes. -/
theorem jetRescalingAction_weightDefect_jetCoordinate (U : C.AffineZariskiSite) (q : Fin r)
    (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
    (hU : (relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1 = relativeJetScheme.chartOpen (k := k) Z s hs r U) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    ((GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) ((q : ℕ) + 1)).val.app
        (Opposite.op U.1)).hom
      (show (((AlgebraicGeometry.Scheme.Modules.pushforward (relativeJetScheme (k := k) Z s hs r).hom).obj
          (SheafOfModules.unit (relativeJetScheme (k := k) Z s hs r).left.ringCatSheaf)).val.obj
            (Opposite.op U.1) : Type u) from
        ((relativeJetScheme (k := k) Z s hs r).left.presheaf.map (CategoryTheory.eqToHom hU).op).hom
          ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
            (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r ((q : ℕ) + 1) b))) = 0 := by
  have hle := GroupSchemeAction.preimage_le_act_preimage (jetRescalingAction (k := k) Z s hs r) U.1
  have h1 := GroupSchemeAction.weightDefect_app_apply (jetRescalingAction (k := k) Z s hs r) ((q : ℕ) + 1) U.1
    (((relativeJetScheme (k := k) Z s hs r).left.presheaf.map (CategoryTheory.eqToHom hU).op).hom
      ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
        (letI := relativeJetScheme.sectionsAlgebra Z U.1
         BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r ((q : ℕ) + 1) b))) hle
  have h2 := jetRescalingAction_act_appLE_coeffClass (k := k) Z s hs r U q b hU hle
  rw [h2, sub_self] at h1
  exact h1

end
