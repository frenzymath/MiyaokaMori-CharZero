import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupExceptionalInvertible
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agsChartAlgebra
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agsChartsGenericPoint

/-! # Stacks 0AGS: global sections of the blowup of a regular local ring of dimension two

Stacks 0AGS concerns the cohomology of quasi-coherent sheaves on the blowup `X` of a two-dimensional
regular local ring `(A, 𝔪)` along `𝔪`. This file proves the part used by Stacks 0AGT:
`Γ(X, O_X) = A` (Stacks 0AGS(4) with `n = 0`).

The route (the proof of 0AGS(4) for `n = 0`, avoiding any computation of `Γ(V_x ⊓ V_y)`): the charts
`V_a ≅ Spec A[𝔪/a]` of Stacks 0804 have a common point (`blowup_preimage_affine_cover_generic`); a
global section restricts on `V_x`, `V_y` to `f ∈ A[𝔪/x]`, `g ∈ A[𝔪/y]` which agree in
`Γ(V_x ⊓ V_y)`; since `A → Γ(V_x ⊓ V_y)` is injective (restriction from the integral chart `V_x`,
`presheaf_map_injective_of_iso_spec_of_isDomain`), the pure algebra `A[𝔪/x] ∩ A[𝔪/y] = A`
(`affineBlowup_exists_eq_algebraMap_of_prime`: `x` prime, `x ∤ y`) gives `f = g = c ∈ A`; the same
constant is the restriction to every other chart (`affineBlowup_eq_algebraMap_of_apply_eq`), and
the sheaf axiom glues. Injectivity of `A → Γ(X, O_X)` is read off on the chart `V_x`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Restriction of sections is transitive, in the `homOfLE` spelling (stated at the variable level so
that instances on concrete schemes are matched syntactically). -/
theorem AlgebraicGeometry.Scheme.presheaf_map_homOfLE_map_homOfLE_hom {X : AlgebraicGeometry.Scheme.{u}}
    {U V W : X.Opens} (h₁ : W ≤ V) (h₂ : V ≤ U) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₁).op).hom ((X.presheaf.map (homOfLE h₂).op).hom s) =
      (X.presheaf.map (homOfLE (h₁.trans h₂)).op).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/-- **Stacks 0AGS(4), `n = 0`: `Γ(X, O_X) = A`** (the structure morphism of `X = Bl_𝔪 Spec A` is an
isomorphism on global sections), `A` a regular local ring of dimension `2`.

Source: Stacks 0AGS(4), `H⁰(X, O_X(n)) = 𝔪^{max(0,n)}`, for `n = 0`.

Proof (Stacks 0AGS, proof of (4)):
1. **Charts.** `𝔪 = (x, y)` with `x` a prime element and `x ∤ y`
   (`IsRegularLocalRing.exists_span_pair_prime_not_dvd`: `spanFinrank 𝔪 = 2`, Nakayama gives `x ∉ 𝔪²`,
   hence `x` is irreducible, hence prime in the UFD `A`).
   By Stacks 0804 (`blowup_preimage_affine_cover_generic`) `X` is covered by opens
   `V_a ≅ Spec A[𝔪/a]` (`a ∈ 𝔪`),
   compatibly with `b : X → Spec A`, and any two charts `V_a`, `V_b` with `a, b ≠ 0` share a point (the
   image of the generic point of `Proj (⊕ 𝔪ⁿ)`). Under the chart isomorphism `ψ_a : A[𝔪/a] ≅ Γ(X, V_a)`,
   `b^♯` followed by restriction to `V_a` is `A → A[𝔪/a]` (`Scheme.Hom.appLE_eq_of_iso_spec`).
2. **Injectivity.** `A → A[𝔪/x] ⊆ A_x` is injective (`x ≠ 0`, `A` a domain), so `A → Γ(X, O_X)` is.
3. **Comparison in `Γ(V_x ⊓ V_y)`.** For `s ∈ Γ(X, O_X)` let `r_a := ψ_a⁻¹(s|_{V_a}) ∈ A[𝔪/a]`. The
   restrictions of `r_x`, `r_y` to `W := V_x ⊓ V_y ≠ ∅` agree (both are `s|_W`), and `A → Γ(X, W)` is
   injective because it factors through the restriction `Γ(X, V_x) → Γ(X, W)` from the integral affine
   scheme `V_x ≅ Spec A[𝔪/x]` (`presheaf_map_injective_of_iso_spec_of_isDomain`, Stacks 01OM). Hence
   `A[𝔪/x] ∩ A[𝔪/y] = A` in the form `affineBlowup_exists_eq_algebraMap_of_prime`: `xⁿ r_x = a`,
   `yᵐ r_y = b` with `yᵐ a = xⁿ b` in `A`; `x` prime, `x ∤ y` ⇒ `xⁿ ∣ a`, so `r_x = r_y = c ∈ A`.
4. **All charts.** For `a ∈ 𝔪`, `a ≠ 0`, compare `r_a` with `r_x = c` in `Γ(V_a ⊓ V_x) ≠ ∅` the same
   way (`affineBlowup_eq_algebraMap_of_apply_eq`): `r_a = c`. For `a = 0`, `A[𝔪/0] = 0`.
5. **Gluing.** `s` and `b^♯(c)` agree on every `V_a`, and the `V_a` cover `X`, so `s = b^♯(c)`
   (`TopCat.Sheaf.eq_of_locally_eq'`). Thus `b^♯ : A → Γ(X, O_X)` is bijective, hence an isomorphism in
   `CommRingCat` (`ConcreteCategory.isIso_iff_bijective`).

Everything is transported from `A` to `Γ(Spec A, ⊤)` along `ΓSpecIso` (`IsRegularLocalRing.of_ringEquiv`,
`IsLocalRing.map_ringEquiv_maximalIdeal`), as in
`AlgebraicGeometry.blowup_regularLocalRing_dimTwo_isRegularLocalRing_stalk`. -/
theorem AlgebraicGeometry.blowup_regularLocalRing_dimTwo_sections
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    let J : (AlgebraicGeometry.Spec (CommRingCat.of A)).IdealSheafData :=
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal A).map
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    CategoryTheory.IsIso ((AlgebraicGeometry.Scheme.blowup J).hom.appTop) := by
  intro J
  -- Step 0: transport regularity and dimension of `A` to `R := Γ(Spec A, ⊤)` along `ΓSpecIso`
  let ε : A ≃+* Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  have : IsRegularLocalRing Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    IsRegularLocalRing.of_ringEquiv ε
  -- local instance: the global one (`IsRegularLocalRing.isDomain`) has low priority, and instance search
  -- would first `whnf` the sections type of the structure sheaf (timeout)
  have : IsDomain Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) := IsRegularLocalRing.isDomain _
  have hdim' : ringKrullDim Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) = 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv ε, hdim]
  have hmax : (IsLocalRing.maximalIdeal A).map
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom =
        IsLocalRing.maximalIdeal Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    IsLocalRing.map_ringEquiv_maximalIdeal ε
  let U : (AlgebraicGeometry.Spec (CommRingCat.of A)).affineOpens :=
    ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
  -- the same local instance in the `Γ(Spec A, U)` spelling (instance search does not unfold the `let` `U`)
  have : IsDomain Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U) :=
    IsRegularLocalRing.isDomain Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤)
  have hJ : J.ideal U = IsLocalRing.maximalIdeal Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) := by
    show (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop _).ideal ⟨⊤, _⟩ = _
    simpa using hmax
  -- from here on only `hJ` is used about `J`; make it opaque
  clear_value J
  -- Step 1: `𝔪 = (x, y)` with `x` prime and `x ∤ y`
  obtain ⟨x, y, hspan, hx, hxy⟩ := IsRegularLocalRing.exists_span_pair_prime_not_dvd
    Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) hdim'
  have hxJ : x ∈ J.ideal U := by
    rw [hJ, ← hspan]
    exact Ideal.subset_span (by simp)
  have hyJ : y ∈ J.ideal U := by
    rw [hJ, ← hspan]
    exact Ideal.subset_span (by simp)
  have hx0 : x ≠ 0 := hx.ne_zero
  have hy0 : y ≠ 0 := fun h => hxy (h ▸ dvd_zero x)
  -- the charts of Stacks 0804, with a common point for any two nonzero `a, b`
  obtain ⟨V, hV, hE, hcov, hgen⟩ :=
    AlgebraicGeometry.Scheme.blowup_preimage_affine_cover_generic J U
  choose ch hch using hE
  -- `ψ a : A[𝔪/a] ≅ Γ(X, V a)`
  let ψ : ∀ a : J.ideal U,
      CommRingCat.of (Ideal.affineBlowup (J.ideal U)
          (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U))) ⟶
        Γ((AlgebraicGeometry.Scheme.blowup J).left, V a) :=
    fun a => (AlgebraicGeometry.Scheme.ΓSpecIso _).inv ≫ (ch a).hom.appTop ≫ (V a).topIso.hom
  have hψ : ∀ a, Function.Bijective (ψ a).hom := fun a => ConcreteCategory.bijective_of_isIso
    ((AlgebraicGeometry.Scheme.ΓSpecIso _).symm ≪≫ AlgebraicGeometry.Scheme.Γ.mapIso (ch a).op ≪≫
      (V a).topIso).hom
  have happLE : ∀ a, (AlgebraicGeometry.Scheme.blowup J).hom.appLE U (V a) (hV a) =
      CommRingCat.ofHom (algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
        (Ideal.affineBlowup (J.ideal U)
          (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)))) ≫ ψ a :=
    fun a => AlgebraicGeometry.Scheme.Hom.appLE_eq_of_iso_spec _ U (V a) (hV a) _ _ (ch a) (hch a)
  -- restricting a global section `b^♯ r` to `V a` is `appLE`
  have hres : ∀ (a : J.ideal U) (r : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤)),
      ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom
          ((AlgebraicGeometry.Scheme.blowup J).hom.appTop.hom r) =
        ((AlgebraicGeometry.Scheme.blowup J).hom.appLE U (V a) (hV a)).hom r := fun a r => rfl
  -- `ρ : A[𝔪/a] → Γ(X, W)` (`W ≤ V a`) restricts to `appLE U W` on `A`
  have hρ : ∀ (a : J.ideal U) (W : (AlgebraicGeometry.Scheme.blowup J).left.Opens) (hW : W ≤ V a),
      ((ψ a ≫ (AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hW).op).hom).comp
          (algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
            (Ideal.affineBlowup (J.ideal U)
              (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)))) =
        ((AlgebraicGeometry.Scheme.blowup J).hom.appLE U W (hW.trans (hV a))).hom := by
    intro a W hW
    rw [← AlgebraicGeometry.Scheme.Hom.appLE_map _ (hV a) (homOfLE hW).op, happLE a]
    rfl
  -- `A[𝔪/x]` is a domain
  have : IsDomain (Localization.Away (x : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤))) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  -- `appLE U W : A → Γ(X, W)` is injective for `∅ ≠ W ≤ V x` (restriction from the integral chart `V x`)
  have hinjW : ∀ (W : (AlgebraicGeometry.Scheme.blowup J).left.Opens) (hW : W ≤ V ⟨x, hxJ⟩),
      (W : Set (AlgebraicGeometry.Scheme.blowup J).left).Nonempty →
      Function.Injective
        ((AlgebraicGeometry.Scheme.blowup J).hom.appLE U W (hW.trans (hV ⟨x, hxJ⟩))).hom := by
    intro W hW hne
    rw [← hρ ⟨x, hxJ⟩ W hW, RingHom.coe_comp, CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((AlgebraicGeometry.Scheme.presheaf_map_injective_of_iso_spec_of_isDomain (V ⟨x, hxJ⟩) W hW
      _ (ch ⟨x, hxJ⟩) hne).comp (hψ _).1).comp
      (Ideal.affineBlowup_algebraMap_injective (J.ideal U) hx0)
  -- Step 2: injectivity of `b^♯`
  have hinj : Function.Injective (AlgebraicGeometry.Scheme.blowup J).hom.appTop.hom := by
    obtain ⟨p, hpx, -⟩ := hgen ⟨x, hxJ⟩ ⟨x, hxJ⟩ hx0 hx0
    intro r r' hrr
    apply hinjW (V ⟨x, hxJ⟩) le_rfl ⟨p, hpx⟩
    calc ((AlgebraicGeometry.Scheme.blowup J).hom.appLE U (V ⟨x, hxJ⟩) _).hom r
        = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom
            ((AlgebraicGeometry.Scheme.blowup J).hom.appTop.hom r) := (hres ⟨x, hxJ⟩ r).symm
      _ = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom
            ((AlgebraicGeometry.Scheme.blowup J).hom.appTop.hom r') :=
          congrArg ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom hrr
      _ = ((AlgebraicGeometry.Scheme.blowup J).hom.appLE U (V ⟨x, hxJ⟩) _).hom r' := hres ⟨x, hxJ⟩ r'
  -- Steps 3–5: surjectivity of `b^♯`
  have hsurj : Function.Surjective (AlgebraicGeometry.Scheme.blowup J).hom.appTop.hom := by
    intro s
    -- the chart components `r a ∈ A[𝔪/a]` of `s`
    have hr : ∀ a : J.ideal U, ∃ r, (ψ a).hom r =
        ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom s :=
      fun a => (hψ a).2 _
    choose r hr using hr
    -- the components agree on any `W ≤ V a ⊓ V b`
    have hsW : ∀ (a b : J.ideal U) (W : (AlgebraicGeometry.Scheme.blowup J).left.Opens)
        (hWa : W ≤ V a) (hWb : W ≤ V b),
        (ψ a ≫ (AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWa).op).hom (r a) =
          (ψ b ≫ (AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWb).op).hom (r b) := by
      intro a b W hWa hWb
      calc (ψ a ≫ (AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWa).op).hom (r a)
          = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWa).op).hom
              ((ψ a).hom (r a)) := rfl
        _ = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWa).op).hom
              (((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom s) :=
            congrArg ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWa).op).hom (hr a)
        _ = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE (hWa.trans le_top)).op).hom
              s := AlgebraicGeometry.Scheme.presheaf_map_homOfLE_map_homOfLE_hom _ _ _
        _ = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE (hWb.trans le_top)).op).hom
              s := rfl
        _ = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWb).op).hom
              (((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom s) :=
            (AlgebraicGeometry.Scheme.presheaf_map_homOfLE_map_homOfLE_hom _ _ _).symm
        _ = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWb).op).hom
              ((ψ b).hom (r b)) :=
            (congrArg ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWb).op).hom
              (hr b)).symm
        _ = (ψ b ≫ (AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE hWb).op).hom (r b) :=
            rfl
    -- Step 3: `r x = r y = c ∈ A`, compared in `Γ(V x ⊓ V y)`
    obtain ⟨p, hpx, hpy⟩ := hgen ⟨x, hxJ⟩ ⟨y, hyJ⟩ hx0 hy0
    obtain ⟨c, hcx, -⟩ := Ideal.affineBlowup_exists_eq_algebraMap_of_prime (J.ideal U) hx hxy _
      (hinjW (V ⟨x, hxJ⟩ ⊓ V ⟨y, hyJ⟩) inf_le_left ⟨p, hpx, hpy⟩) _ (hρ ⟨x, hxJ⟩ _ inf_le_left) _
      (hρ ⟨y, hyJ⟩ _ inf_le_right) (r ⟨x, hxJ⟩) (r ⟨y, hyJ⟩)
      (hsW ⟨x, hxJ⟩ ⟨y, hyJ⟩ _ inf_le_left inf_le_right)
    refine ⟨c, ?_⟩
    -- Step 5: glue over the cover `{V a}`
    refine (AlgebraicGeometry.Scheme.blowup J).left.sheaf.eq_of_locally_eq' V ⊤
      (fun a => homOfLE le_top) ?_ ((AlgebraicGeometry.Scheme.blowup J).hom.appTop c) s ?_
    · rw [hcov]
      intro z _
      exact trivial
    intro a
    -- Step 4: `r a = c` for every chart
    have hra : r a = algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
        (Ideal.affineBlowup (J.ideal U) (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U))) c := by
      by_cases ha0 : (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)) = 0
      · have := Ideal.affineBlowup_subsingleton_of_eq_zero (J.ideal U) ha0
        exact Subsingleton.elim _ _
      · obtain ⟨q, hqa, hqx⟩ := hgen a ⟨x, hxJ⟩ ha0 hx0
        refine Ideal.affineBlowup_eq_algebraMap_of_apply_eq (J.ideal U) _ _
          (hinjW (V a ⊓ V ⟨x, hxJ⟩) inf_le_right ⟨q, hqa, hqx⟩) _ (hρ a _ inf_le_left) (r a) c ?_
        calc (ψ a ≫ (AlgebraicGeometry.Scheme.blowup J).left.presheaf.map
                (homOfLE (inf_le_left : V a ⊓ V ⟨x, hxJ⟩ ≤ V a)).op).hom (r a)
            = (ψ ⟨x, hxJ⟩ ≫ (AlgebraicGeometry.Scheme.blowup J).left.presheaf.map
                (homOfLE (inf_le_right : V a ⊓ V ⟨x, hxJ⟩ ≤ V ⟨x, hxJ⟩)).op).hom (r ⟨x, hxJ⟩) :=
              hsW a ⟨x, hxJ⟩ _ inf_le_left inf_le_right
          _ = (ψ ⟨x, hxJ⟩ ≫ (AlgebraicGeometry.Scheme.blowup J).left.presheaf.map
                (homOfLE (inf_le_right : V a ⊓ V ⟨x, hxJ⟩ ≤ V ⟨x, hxJ⟩)).op).hom
                (algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
                  (Ideal.affineBlowup (J.ideal U) (x : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)))
                  c) :=
              congrArg _ hcx
          _ = ((AlgebraicGeometry.Scheme.blowup J).hom.appLE U (V a ⊓ V ⟨x, hxJ⟩)
                (inf_le_right.trans (hV ⟨x, hxJ⟩))).hom c :=
              DFunLike.congr_fun (hρ ⟨x, hxJ⟩ _ inf_le_right) c
    show ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom
        ((AlgebraicGeometry.Scheme.blowup J).hom.appTop.hom c) =
      ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom s
    calc ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom
          ((AlgebraicGeometry.Scheme.blowup J).hom.appTop.hom c)
        = ((AlgebraicGeometry.Scheme.blowup J).hom.appLE U (V a) (hV a)).hom c := hres a c
      _ = (CommRingCat.ofHom (algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
            (Ideal.affineBlowup (J.ideal U) (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)))) ≫
            ψ a).hom c := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (happLE a)) c
      _ = (ψ a).hom (algebraMap Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U)
            (Ideal.affineBlowup (J.ideal U) (a : Γ(AlgebraicGeometry.Spec (CommRingCat.of A), U))) c) :=
          rfl
      _ = (ψ a).hom (r a) := (congrArg (ψ a).hom hra).symm
      _ = ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.map (homOfLE le_top).op).hom s := hr a
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

end
