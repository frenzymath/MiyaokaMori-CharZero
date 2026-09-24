import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveAsSmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueIso
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleGenericSection

/-! # Every line bundle is `O_X(D)` for a Cartier divisor

Every line bundle on a variety (in particular on a smooth projective curve) is of the form `O_X(D)` for
a Cartier divisor `D` (surjectivity of `CaCl X → Pic X`, Hartshorne II.6.15). By II.6.15 this needs only
that `X` is integral — neither regularity nor Cartier = Weil. The general statement is
`LineBundle.exists_cartierDivisor_variety` for any `Variety k`; the curve case is an instance of it.
The proof follows II.6.15 with the "nonzero rational section `s`" taken to be a reference frame
`e₀ := e_{x₀}` (`x₀` any point): `f_x :=` the generic value of the coordinate of `e₀` in the frame `e_x`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- For frames `e ∈ Γ(M, W)`, `e' ∈ Γ(N, W)`, the section map on `V ≤ W` (`restrictSectionMap`) of the
local isomorphism `hf.restrictIso ≪≫ hf'.restrictIso.symm : M|_W ≅ N|_W` is "take the `e`-coordinate and
multiply it onto `e'`": `x ↦ coord_e(x) • e'|_V`. In particular it sends `e|_V` to `e'|_V`. -/
theorem restrictSectionMap_frameIso_apply {M N : X.Modules} {W : X.Opens}
    {e : Γ(M, W)} {e' : Γ(N, W)} (hf : IsFrame M W e) (hf' : IsFrame N W e')
    (V : X.Opens) (hV : V ≤ W) (x : Γ(M, V)) :
    restrictSectionMap (hf.restrictIso ≪≫ hf'.restrictIso.symm).hom V hV x =
      hf.coord hV x • N.res hV e' := by
  have h1 : W.ι ''ᵁ W.ι ⁻¹ᵁ V ≤ V := W.ι.image_preimage_le V
  have h2 : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V := by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact le_inf hV le_rfl
  change N.presheaf.map (homOfLE h2).op
    ((hf.restrictIso ≪≫ hf'.restrictIso.symm).hom.app (W.ι ⁻¹ᵁ V)
      (M.presheaf.map (homOfLE h1).op x)) = _
  rw [Iso.trans_hom, Iso.symm_hom, Hom.comp_app]
  change N.presheaf.map (homOfLE h2).op
    (hf'.restrictIso.inv.val.app (op (W.ι ⁻¹ᵁ V))
      (hf.restrictIso.hom.val.app (op (W.ι ⁻¹ᵁ V)) (M.presheaf.map (homOfLE h1).op x))) = _
  rw [hf.restrictIso_hom_app, hf'.restrictIso_inv_app, Iso.hom_inv_id_apply]
  change N.res h2 (hf.coord (h1.trans hV) (M.res h1 x) • N.res (h1.trans hV) e') = _
  rw [hf.coord_map h1 hV x, res_smul, res_res]
  congr 1
  rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  have : (homOfLE h1).op ≫ (homOfLE h2).op = 𝟙 (op V) := rfl
  rw [this, X.presheaf.map_id]
  rfl

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Scheme.Modules in
/-- **Hartshorne II.6.15**: on an integral scheme `CaCl X → Pic X` is surjective, i.e. every line bundle
is of the form `O_X(D)`.

Source: Hartshorne, *Algebraic Geometry*, Prop. II.6.15: "If `X` is an integral scheme, the
homomorphism `CaCl X → Pic X` of (6.14) is an isomorphism." The proof uses only that `X` is integral
(so `𝒦_X` is the constant sheaf `K = K(X)` and `X` is irreducible); it needs neither regularity,
normality, local factoriality nor Cartier = Weil (II.6.11). The `integral` field of `Variety k`
provides exactly this hypothesis.

Proof (Hartshorne's argument in the "local frames and local equations" form):
1. At every point `x` take a frame neighbourhood `(U_x, e_x)` of `L` (`exists_frame`; `L` is locally
   free of rank one). Fix a point `x₀`; `e₀ := e_{x₀}` plays the role of Hartshorne's "nonzero rational
   section `s`". On `W_x := U_x ∩ U_{x₀}` (nonempty, containing the generic point `η`) the two frames
   differ by a unit `c_x ∈ O(W_x)^×`: `c_x • e_x = e₀` (`IsFrame.exists_unit`). Put `f_x := (c_x)_η ∈ K(X)^×`.
2. Compatibility: if `d • e_y = e_x` on `V ⊆ U_x ∩ U_y`, then `f_x · d_η = f_y` (`hkey`: on `V ∩ U_{x₀}`,
   `c_x d • e_y = e₀ = c_y • e_y`, injectivity of the frame gives `c_x d = c_y`, then take generic
   values). With `d` the transition unit of `e_x`, `e_y` on `U_x ∩ U_y`, `f_x / f_y = (d⁻¹)_η` is the
   image in `K(X)` of a unit of every stalk, i.e. `CartierDivisor.IsLocalData U f`. Put
   `D := CartierDivisor.ofLocalData U f`; `local_section_ofLocalData` gives a local equation `t_x` of `D`
   on `U_x` with value `f_x`.
3. `O_X(D)` has the frame `t_x⁻¹` on `U_x` (`IsLocalEquation.isFrame`) and `L` the frame `e_x`; the two
   `IsFrame.restrictIso` combine to `φ_x : O_X(D)|_{U_x} ≅ L|_{U_x}` with section map
   `s ↦ coord_{t_x⁻¹}(s) • e_x` (`restrictSectionMap_frameIso_apply`). On `V ⊆ U_x ∩ U_y`,
   `exists_transition` gives `t_x⁻¹ = c • t_y⁻¹` with `f_x c_η = f_y`; comparing with step 2
   (`germToFunctionField_injective`) gives `c = d`, so `coord_y(s) • e_y = coord_x(s) c • e_y = coord_x(s) • e_x`:
   the section maps agree. For `V = ∅` both sides lie in `Γ(L, ∅)` and agree by the sheaf property
   (`eq_of_locally_eq'` for the empty cover).
4. `glueIso` glues `O_X(D) ≅ L` (as module sheaves), which is then packaged as an isomorphism in
   `LineBundle X`. -/
theorem LineBundle.exists_cartierDivisor_variety {k : Type u} [Field k] (X : Variety k)
    (L : LineBundle X) :
    ∃ D : CartierDivisor X, Nonempty (CartierDivisor.lineBundle D ≅ L) := by
  classical
  let S := X.toScheme
  let M : S.Modules := L.toModules
  let K := S.functionField
  have hη : ∀ (V : S.Opens), Nonempty V → genericPoint S ∈ V := fun V hV =>
    ((genericPoint_spec S).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  -- Step 1: frames of L
  have hfr : ∀ x : S, ∃ (U : S.Opens) (_ : x ∈ U) (e : Γ(M, U)), IsFrame M U e :=
    fun x => exists_frame M x
  choose U hxU e he using hfr
  have hne : ∀ x, Nonempty (U x) := fun x => ⟨⟨x, hxU x⟩⟩
  have hcover : (⨆ x, U x) = ⊤ :=
    top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩
  obtain ⟨x₀⟩ : Nonempty S := inferInstance
  let W : S → S.Opens := fun x => U x ⊓ U x₀
  have hηW : ∀ x, genericPoint S ∈ W x := fun x => ⟨hη _ (hne x), hη _ (hne x₀)⟩
  have hneW : ∀ x, Nonempty (W x) := fun x => ⟨⟨_, hηW x⟩⟩
  have hc : ∀ x, ∃ c : (Γ(S, W x))ˣ,
      (c : Γ(S, W x)) • M.res (inf_le_left : W x ≤ U x) (e x) =
        M.res (inf_le_right : W x ≤ U x₀) (e x₀) :=
    fun x => ((he x).restrict inf_le_left).exists_unit ((he x₀).restrict inf_le_right)
  choose c hc using hc
  let f : S → Kˣ := fun x =>
    Units.map (haveI := hneW x; (S.germToFunctionField (W x)).hom.toMonoidHom) (c x)
  have hf : ∀ x, (f x : K) = (haveI := hneW x; (S.germToFunctionField (W x)).hom (c x)) :=
    fun x => rfl
  -- Step 2: compatibility of the f_x
  have hkey : ∀ (x y : S) (V : S.Opens) (hVx : V ≤ U x) (hVy : V ≤ U y) (hV : Nonempty V)
      (d : Γ(S, V)), d • M.res hVy (e y) = M.res hVx (e x) →
      (f x : K) * (S.germToFunctionField V).hom d = f y := by
    intro x y V hVx hVy hV d hd
    let T : S.Opens := V ⊓ U x₀
    have hηT : genericPoint S ∈ T := ⟨hη V hV, hη _ (hne x₀)⟩
    have : Nonempty T := ⟨⟨_, hηT⟩⟩
    have hTV : T ≤ V := inf_le_left
    have hT0 : T ≤ U x₀ := inf_le_right
    have hTWx : T ≤ W x := le_inf (hTV.trans hVx) hT0
    have hTWy : T ≤ W y := le_inf (hTV.trans hVy) hT0
    have h1 : S.presheaf.map (homOfLE hTWx).op (c x) • M.res (hTV.trans hVx) (e x) =
        M.res hT0 (e x₀) := by
      have := congrArg (M.res hTWx) (hc x)
      rw [res_smul, res_res, res_res] at this
      exact this
    have h2 : S.presheaf.map (homOfLE hTWy).op (c y) • M.res (hTV.trans hVy) (e y) =
        M.res hT0 (e x₀) := by
      have := congrArg (M.res hTWy) (hc y)
      rw [res_smul, res_res, res_res] at this
      exact this
    have h3 : S.presheaf.map (homOfLE hTV).op d • M.res (hTV.trans hVy) (e y) =
        M.res (hTV.trans hVx) (e x) := by
      have := congrArg (M.res hTV) hd
      rw [res_smul, res_res, res_res] at this
      exact this
    have h4 : S.presheaf.map (homOfLE hTWx).op (c x) * S.presheaf.map (homOfLE hTV).op d =
        S.presheaf.map (homOfLE hTWy).op (c y) := by
      apply (((he y).restrict (hTV.trans hVy)) T le_rfl).1
      simp only [res_self]
      rw [mul_smul, h3, h1, h2]
    have h5 := congrArg (S.germToFunctionField T).hom h4
    rw [map_mul] at h5
    have r1 : (S.germToFunctionField T).hom (S.presheaf.map (homOfLE hTWx).op (c x)) =
        (S.germToFunctionField (W x)).hom (c x) :=
      S.presheaf.germ_res_apply (homOfLE hTWx) _ hηT (c x)
    have r2 : (S.germToFunctionField T).hom (S.presheaf.map (homOfLE hTWy).op (c y)) =
        (S.germToFunctionField (W y)).hom (c y) :=
      S.presheaf.germ_res_apply (homOfLE hTWy) _ hηT (c y)
    have r3 : (S.germToFunctionField T).hom (S.presheaf.map (homOfLE hTV).op d) =
        (S.germToFunctionField V).hom d :=
      S.presheaf.germ_res_apply (homOfLE hTV) _ hηT d
    rw [r1, r2, r3] at h5
    rw [hf x, hf y]
    exact h5
  -- Step 2': local data
  have hratio : ∀ x y : S, ∀ z ∈ U x ⊓ U y,
      ((f x / f y : Kˣ) : K) ∈
        Set.range (fun v : (S.presheaf.stalk z)ˣ =>
          algebraMap (S.presheaf.stalk z) K v) := by
    intro x y z hz
    let V : S.Opens := U x ⊓ U y
    have hV : Nonempty V := ⟨⟨z, hz⟩⟩
    obtain ⟨d, hd⟩ := ((he y).restrict (inf_le_right : V ≤ U y)).exists_unit
      ((he x).restrict (inf_le_left : V ≤ U x))
    have hk := hkey x y V inf_le_left inf_le_right hV d hd
    refine ⟨Units.map (S.presheaf.germ V z hz).hom.toMonoidHom d⁻¹, ?_⟩
    change algebraMap (S.presheaf.stalk z) K
      (S.presheaf.germ V z hz ((d⁻¹ : (Γ(S, V))ˣ) : Γ(S, V))) = _
    rw [AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField S hz,
      Units.val_div_eq_div_val, ← hk]
    have hd1 : (S.germToFunctionField V).hom ((d⁻¹ : (Γ(S, V))ˣ) : Γ(S, V)) *
        (S.germToFunctionField V).hom (d : Γ(S, V)) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hfx : (f x : K) ≠ 0 := Units.ne_zero _
    have hdne : (S.germToFunctionField V).hom (d : Γ(S, V)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hd1
      exact zero_ne_one hd1
    rw [eq_div_iff (mul_ne_zero hfx hdne)]
    calc (S.germToFunctionField V).hom ((d⁻¹ : (Γ(S, V))ˣ) : Γ(S, V)) *
          ((f x : K) * (S.germToFunctionField V).hom (d : Γ(S, V)))
        = (f x : K) * ((S.germToFunctionField V).hom ((d⁻¹ : (Γ(S, V))ˣ) : Γ(S, V)) *
            (S.germToFunctionField V).hom (d : Γ(S, V))) := by ring
      _ = f x := by rw [hd1, mul_one]
  have hUf : CartierDivisor.IsLocalData U f :=
    ⟨hcover, fun x y z hz => ⟨hratio x y z hz, hratio y x z ⟨hz.2, hz.1⟩⟩⟩
  let D : CartierDivisor X := CartierDivisor.ofLocalData U f
  have ht : ∀ x, ∃ t : S.rationalFunctionsUnitsSheaf.val.obj (op (U x)),
      (haveI := hne x; S.rationalUnitsSectionToFunctionField (U x) t) = f x ∧
      CartierDivisor.IsLocalEquation D (U x) t := by
    intro x
    obtain ⟨t, h1, h2⟩ :=
      CartierToWeilLocalSection.local_section_ofLocalData U f hUf x x (hxU x)
    exact ⟨t, h1, h2⟩
  choose t htv hte using ht
  -- Step 3: local isomorphisms and their compatibility
  let N : S.Modules := CartierDivisor.lineBundleModules D
  let φ : ∀ x, N.restrict (U x).ι ≅ M.restrict (U x).ι := fun x =>
    (hte x).isFrame.restrictIso ≪≫ (he x).restrictIso.symm
  have hφ : ∀ x y (V : S.Opens) (hx : V ≤ U x) (hy : V ≤ U y),
      restrictSectionMap (φ x).hom V hx = restrictSectionMap (φ y).hom V hy := by
    intro x y V hx hy
    ext s
    by_cases hV : Nonempty V
    · have := hne x
      have := hne y
      have := hV
      change restrictSectionMap (φ x).hom V hx s = restrictSectionMap (φ y).hom V hy s
      simp only [φ]
      rw [restrictSectionMap_frameIso_apply, restrictSectionMap_frameIso_apply]
      obtain ⟨cc, hcc, hccf⟩ := (hte x).exists_transition (hte y) hx hy
      rw [htv x, htv y] at hccf
      obtain ⟨d, hd⟩ := ((he y).restrict hy).exists_unit ((he x).restrict hx)
      have hk := hkey x y V hx hy hV d hd
      have hcd : cc = d := by
        apply S.germToFunctionField_injective V
        exact mul_left_cancel₀ (Units.ne_zero (f x)) (hccf.trans hk.symm)
      have hcoord : (hte y).isFrame.coord hy s = (hte x).isFrame.coord hx s * cc := by
        apply IsFrame.coord_unique
        rw [mul_smul, ← hcc]
        exact (hte x).isFrame.coord_smul_frame hx s
      rw [hcoord, hcd, mul_smul, hd]
    · have hVbot : V = ⊥ := by
        ext z
        simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hz => hV ⟨⟨z, hz⟩⟩
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
        (fun i : PEmpty.{u + 1} => (⊥ : S.Opens)) V (fun i => i.elim) ?_ _ _ (fun i => i.elim)
      rw [hVbot]
      exact bot_le
  -- Step 4: glue
  obtain ⟨E, -⟩ := glueIso U hcover N M φ hφ
  refine ⟨D, ⟨?_⟩⟩
  exact
    { hom := ⟨E.hom⟩
      inv := ⟨E.inv⟩
      hom_inv_id := by
        apply CategoryTheory.InducedCategory.hom_ext
        change E.hom ≫ E.inv = 𝟙 _
        exact E.hom_inv_id
      inv_hom_id := by
        apply CategoryTheory.InducedCategory.hom_ext
        change E.inv ≫ E.hom = 𝟙 _
        exact E.inv_hom_id }

theorem LineBundle.exists_cartierDivisor {k : Type u} [Field k] (C : SmoothProjectiveCurve k)
    (L : LineBundle C.toVariety) :
    ∃ D : CartierDivisor C.toVariety, Nonempty (CartierDivisor.lineBundle D ≅ L) :=
  LineBundle.exists_cartierDivisor_variety C.toVariety L

end
