import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleDualPairing
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffCartier
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheafOld

/-! # Pairing an effective Cartier divisor with a Cartier divisor

Let `X` be a variety, `D` an effective Cartier divisor on `X` (`EffCartier`, with ideal sheaf `I_D`)
and `D'` a Cartier divisor (`CartierDivisor X`). If near every point there is a pair `(e, t)` with `e`
a frame of `I_D`, `t` a local equation of `D'` and `t = ι(e)` (`LocalPair`, `HasLocalPairs`), then
`O_X(D') ≅ O_X(D) := I_D^∨` (`lineBundleModulesIsoSheaf`).

Proof (Hartshorne II.6.18 and II.6.13(b): `I_D ≅ O(−D)`, `O(D) ≅ Hom(I_D, O)`):
1. The pairing at the presheaf level, `pairingPresheafHom : O_X(D') ⟶ 𝓗om(I_D, O_X)`,
   `h ↦ (V ↦ (a ↦ ι⁻¹(h|_V · ι(a))))`. Here `h|_V · ι(a)` lies in the image of `O_X`: on an open with
   a pair `(e, t)`, `a = c • e` and `h · ι(a) = c · (h · t)` with `h · t ∈ O_X`
   (`IsLocalEquation.mem_lineBundleSections_iff`); the image of `O_X` in `𝒦_X` is a subsheaf
   (`mem_range_toRationalFunctionsSheaf_of_locally`).
2. On an open with a pair `(e, t)`, `t⁻¹` is a frame of `O_X(D')` and the pairing sends it to the dual
   frame `e^∨` of the frame `e` of `I_D` (`pairingFamily_invSection`), so the pairing is locally
   bijective (`_isLocallySurjective` / `_isLocallyInjective`).
3. A locally bijective map becomes an isomorphism after sheafification
   (`moduleSheafification_map_isIso_of_locallyBijective`); the sheafification of the target is
   isomorphic to `dualSheaf I_D` (`dualSheafIsoOld`).
Sources: Hartshorne II.6.13(b), II.6.18; Stacks 01WX.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.EffCartierPairing

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules CartierDivisor

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {X : Variety k}

/-- `ι : Γ(X, V) → 𝒦_X(V)` as a `Γ(X, V)`-linear map. -/
def iotaK (V : X.toScheme.Opens) :
    Γ(X.toScheme, V) →ₗ[Γ(X.toScheme, V)] X.toScheme.rationalFunctionsSheaf.val.obj (op V) where
  toFun := (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom
  map_add' := fun a b => map_add _ a b
  map_smul' := fun r a => by
    change (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom (r * a) =
      (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom r *
        (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom a
    rw [map_mul]

theorem iotaK_apply (V : X.toScheme.Opens) (a : Γ(X.toScheme, V)) :
    iotaK V a = (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom a := rfl

theorem iotaK_injective (V : X.toScheme.Opens) : Function.Injective (iotaK (X := X) V) :=
  X.toScheme.toRationalFunctionsSheaf_app_injective V

/-- A pair of local data: a frame `e` of `I_D` on `W` and a local equation `t` of `D'` on `W` with
`t = ι(e) ∈ 𝒦_X(W)`. -/
structure LocalPair (D : X.toScheme.EffCartier) (D' : CartierDivisor X) (W : X.toScheme.Opens) where
  /-- The frame of `I_D`. -/
  e : Γ(D.ideal.toModules, W)
  isFrame : IsFrame D.ideal.toModules W e
  /-- The local equation of `D'`. -/
  t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op W)
  isLocalEquation : IsLocalEquation D' W t
  val_eq : unitVal t =
    (X.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom (EffCartier.idealIota D.ideal W e)

/-- Near every point there is a pair of local data. -/
def HasLocalPairs (D : X.toScheme.EffCartier) (D' : CartierDivisor X) : Prop :=
  ∀ p : X.toScheme, ∃ (W : X.toScheme.Opens) (_ : p ∈ W), Nonempty (LocalPair D D' W)

variable {D : X.toScheme.EffCartier} {D' : CartierDivisor X}

/-- Restriction of a pair of local data to a smaller open. -/
def LocalPair.restrict {W : X.toScheme.Opens} (P : LocalPair D D' W) {V : X.toScheme.Opens}
    (hVW : V ≤ W) : LocalPair D D' V where
  e := D.ideal.toModules.res hVW P.e
  isFrame := P.isFrame.restrict hVW
  t := X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hVW).op P.t
  isLocalEquation := P.isLocalEquation.restrict hVW
  val_eq := by
    rw [unitVal_restrict, P.val_eq, ← X.toScheme.toRationalFunctionsSheaf_res]
    congr 1
    exact (EffCartier.idealIota_map D.ideal (homOfLE hVW) P.e).symm

/-- For `h ∈ O_X(D')(W)`, `V ≤ W` and `y ∈ Γ(I_D, V)`, `h|_V · ι(y) ∈ ι(Γ(X, V))`. -/
theorem mul_iota_mem (hrel : HasLocalPairs D D') {W : X.toScheme.Opens}
    (h : lineBundleSections D' W) {V : X.toScheme.Opens} (hVW : V ≤ W)
    (y : Γ(D.ideal.toModules, V)) :
    (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVW).op).hom h.1 *
        (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom (EffCartier.idealIota D.ideal V y) ∈
      Set.range (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom := by
  apply X.toScheme.mem_range_toRationalFunctionsSheaf_of_locally
  intro x hx
  obtain ⟨W₀, hxW₀, ⟨P⟩⟩ := hrel x
  have hV₁V : (V ⊓ W₀ : X.toScheme.Opens) ≤ V := inf_le_left
  have hV₁W₀ : (V ⊓ W₀ : X.toScheme.Opens) ≤ W₀ := inf_le_right
  let P₁ := P.restrict hV₁W₀
  let h₁ := lineBundleRestrict D' (homOfLE (hV₁V.trans hVW)) h
  obtain ⟨s, hs⟩ := (P.isLocalEquation.mem_lineBundleSections_iff hV₁W₀ h₁.1).mp h₁.2
  refine ⟨V ⊓ W₀, ⟨hx, hxW₀⟩, hV₁V, ?_⟩
  let c := P₁.isFrame.coord le_rfl (D.ideal.toModules.res hV₁V y)
  have hc : c • P₁.e = D.ideal.toModules.res hV₁V y := by
    have := P₁.isFrame.coord_smul_frame le_rfl (D.ideal.toModules.res hV₁V y)
    rwa [res_self] at this
  refine ⟨c * (show Γ(X.toScheme, V ⊓ W₀) from s), ?_⟩
  rw [map_mul, map_mul, hs, X.toScheme.rationalFunctionsSheaf_map_map,
    ← X.toScheme.toRationalFunctionsSheaf_res]
  have hy : X.toScheme.presheaf.map (homOfLE hV₁V).op (EffCartier.idealIota D.ideal V y) =
      c * EffCartier.idealIota D.ideal (V ⊓ W₀) P₁.e := by
    rw [← EffCartier.idealIota_map D.ideal (homOfLE hV₁V) y]
    change EffCartier.idealIota D.ideal (V ⊓ W₀) (D.ideal.toModules.res hV₁V y) = _
    rw [← hc, _root_.map_smul, smul_eq_mul]
  rw [hy, map_mul, ← P₁.val_eq]
  change (X.toScheme.toRationalFunctionsSheaf.hom.app (op (V ⊓ W₀))).hom c *
      (h₁.1 * unitVal P₁.t) = h₁.1 * (_ * unitVal P₁.t)
  ring

/-- The pairing before applying `ι⁻¹`: `y ↦ h|_V · ι(y) ∈ 𝒦_X(V)` (`Γ(X, V)`-linear). -/
def pairingRaw {W : X.toScheme.Opens} (h : lineBundleSections D' W) {V : X.toScheme.Opens}
    (hVW : V ≤ W) :
    Γ(D.ideal.toModules, V) →ₗ[Γ(X.toScheme, V)] X.toScheme.rationalFunctionsSheaf.val.obj (op V) where
  toFun := fun y => (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVW).op).hom h.1 *
    (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom (EffCartier.idealIota D.ideal V y)
  map_add' := fun y y' => by
    simp only [map_add, mul_add]
  map_smul' := fun r y => by
    change (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVW).op).hom h.1 *
        (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom
          (EffCartier.idealIota D.ideal V (r • y)) =
      (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom r *
        ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVW).op).hom h.1 *
          (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom (EffCartier.idealIota D.ideal V y))
    rw [_root_.map_smul, smul_eq_mul, map_mul]
    ring

theorem pairingRaw_apply {W : X.toScheme.Opens} (h : lineBundleSections D' W) {V : X.toScheme.Opens}
    (hVW : V ≤ W) (y : Γ(D.ideal.toModules, V)) :
    pairingRaw h hVW y = (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVW).op).hom h.1 *
      (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom (EffCartier.idealIota D.ideal V y) := rfl

/-- The pairing functional `y ↦ ι⁻¹(h|_V · ι(y))`. -/
def pairingFun (hrel : HasLocalPairs D D') {W : X.toScheme.Opens}
    (h : lineBundleSections D' W) {V : X.toScheme.Opens} (hVW : V ≤ W) :
    Γ(D.ideal.toModules, V) →ₗ[Γ(X.toScheme, V)] Γ(X.toScheme, V) :=
  (LinearEquiv.ofInjective (iotaK V) (iotaK_injective V)).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range (iotaK V)) (pairingRaw h hVW)
      (fun y => LinearMap.mem_range.mpr (mul_iota_mem hrel h hVW y))

/-- Evaluation formula: `ι(⟨h, y⟩) = h|_V · ι(y)`. -/
theorem iotaK_pairingFun (hrel : HasLocalPairs D D') {W : X.toScheme.Opens}
    (h : lineBundleSections D' W) {V : X.toScheme.Opens} (hVW : V ≤ W)
    (y : Γ(D.ideal.toModules, V)) :
    (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom (pairingFun hrel h hVW y) =
      (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hVW).op).hom h.1 *
        (X.toScheme.toRationalFunctionsSheaf.hom.app (op V)).hom
          (EffCartier.idealIota D.ideal V y) := by
  have key := LinearEquiv.ofInjective_apply (iotaK V) (h := iotaK_injective V)
    ((LinearEquiv.ofInjective (iotaK V) (iotaK_injective V)).symm
      (LinearMap.codRestrict (LinearMap.range (iotaK V)) (pairingRaw h hVW)
        (fun y => LinearMap.mem_range.mpr (mul_iota_mem hrel h hVW y)) y))
  rw [LinearEquiv.apply_symm_apply] at key
  exact key.symm

/-- The family of pairing functionals `V ↦ (y ↦ ι⁻¹(h|_V · ι(y)))`, compatible with restriction. -/
def pairingFamily (hrel : HasLocalPairs D D') {W : X.toScheme.Opens}
    (h : lineBundleSections D' W) :
    AlgebraicGeometry.Scheme.Modules.LocalDualSections X.toScheme D.ideal.toModules W :=
  ⟨fun V => pairingFun hrel h (leOfHom V.hom), by
    intro V V' i y
    have hi : i.left = homOfLE (leOfHom i.left) := Subsingleton.elim _ _
    apply X.toScheme.toRationalFunctionsSheaf_app_injective
    beta_reduce
    rw [hi, iotaK_pairingFun, X.toScheme.toRationalFunctionsSheaf_res, iotaK_pairingFun, map_mul,
      EffCartier.idealIota_map, X.toScheme.toRationalFunctionsSheaf_res]
    congr 1
    exact (X.toScheme.rationalFunctionsSheaf_map_map (leOfHom V'.hom) (leOfHom i.left) h.1).symm⟩

theorem pairingFamily_apply (hrel : HasLocalPairs D D') {W : X.toScheme.Opens}
    (h : lineBundleSections D' W) (V : Over W) :
    (pairingFamily hrel h).1 V = pairingFun hrel h (leOfHom V.hom) := rfl

/-- The pairing at the presheaf level, `O_X(D') ⟶ 𝓗om(I_D, O_X)`: `h ↦ (y ↦ ι⁻¹(h·ι(y)))`. -/
def pairingPresheafHom (hrel : HasLocalPairs D D') :
    lineBundlePresheaf D' ⟶ AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf D.ideal.toModules where
  app W := ModuleCat.ofHom
    { toFun := fun h => pairingFamily hrel h
      map_add' := fun h h' => by
        apply Subtype.ext
        funext V
        apply LinearMap.ext
        intro y
        apply X.toScheme.toRationalFunctionsSheaf_app_injective
        change (X.toScheme.toRationalFunctionsSheaf.hom.app (op V.left)).hom
            (pairingFun hrel (h + h') (leOfHom V.hom) y) =
          (X.toScheme.toRationalFunctionsSheaf.hom.app (op V.left)).hom
            (pairingFun hrel h (leOfHom V.hom) y + pairingFun hrel h' (leOfHom V.hom) y)
        rw [map_add, iotaK_pairingFun, iotaK_pairingFun, iotaK_pairingFun]
        change (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (leOfHom V.hom)).op).hom
          (h.1 + h'.1) * _ = _
        rw [map_add, add_mul]
      map_smul' := fun r h => by
        apply Subtype.ext
        funext V
        apply LinearMap.ext
        intro y
        apply X.toScheme.toRationalFunctionsSheaf_app_injective
        change (X.toScheme.toRationalFunctionsSheaf.hom.app (op V.left)).hom
            (pairingFun hrel (r • h) (leOfHom V.hom) y) =
          (X.toScheme.toRationalFunctionsSheaf.hom.app (op V.left)).hom
            ((X.toScheme.presheaf.map V.hom.op).hom r * pairingFun hrel h (leOfHom V.hom) y)
        rw [map_mul, iotaK_pairingFun, iotaK_pairingFun, toRationalFunctionsSheaf_res']
        change (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (leOfHom V.hom)).op).hom
          ((X.toScheme.toRationalFunctionsSheaf.hom.app (op W.unop)).hom r * h.1) * _ = _
        rw [map_mul, mul_assoc]
        congr 2 }
  naturality {W W'} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro y
    apply X.toScheme.toRationalFunctionsSheaf_app_injective
    change (X.toScheme.toRationalFunctionsSheaf.hom.app (op V.left)).hom
        (pairingFun hrel (lineBundleRestrict D' i.unop h) (leOfHom V.hom) y) =
      (X.toScheme.toRationalFunctionsSheaf.hom.app (op V.left)).hom
        (pairingFun hrel h (leOfHom (V.hom ≫ i.unop)) y)
    rw [iotaK_pairingFun, iotaK_pairingFun]
    congr 1
    change (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (leOfHom V.hom)).op).hom
      ((X.toScheme.rationalFunctionsSheaf.val.map i.unop.op).hom h.1) = _
    rw [rationalFunctionsSheaf_map_map']
    exact rationalFunctionsSheaf_map_congr _ _ _

/-- The frame `t⁻¹` of `O_X(D')` on `W` pairs to the dual frame `e^∨` of the frame `e` of `I_D`. -/
theorem pairingFamily_invSection (hrel : HasLocalPairs D D') {W : X.toScheme.Opens}
    (P : LocalPair D D' W) :
    pairingFamily hrel (P.isLocalEquation.invSection le_rfl) =
      (P.isFrame.dualFrame : AlgebraicGeometry.Scheme.Modules.LocalDualSections X.toScheme D.ideal.toModules W) := by
  apply Subtype.ext
  funext V'
  apply LinearMap.ext
  intro y
  change pairingFun hrel (P.isLocalEquation.invSection le_rfl) (leOfHom V'.hom) y =
    P.isFrame.coord (leOfHom V'.hom) y
  symm
  apply P.isFrame.coord_unique
  apply EffCartier.idealIota_injective
  rw [_root_.map_smul, smul_eq_mul]
  have hres : EffCartier.idealIota D.ideal V'.left (D.ideal.toModules.res (leOfHom V'.hom) P.e) =
      X.toScheme.presheaf.map (homOfLE (leOfHom V'.hom)).op (EffCartier.idealIota D.ideal W P.e) :=
    EffCartier.idealIota_map D.ideal (homOfLE (leOfHom V'.hom)) P.e
  rw [hres]
  apply X.toScheme.toRationalFunctionsSheaf_app_injective
  rw [map_mul, iotaK_pairingFun, X.toScheme.toRationalFunctionsSheaf_res, ← P.val_eq,
    ← unitVal_restrict]
  change (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (leOfHom V'.hom)).op).hom
    ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE (le_refl W)).op).hom (unitVal P.t⁻¹)) *
    _ * _ = _
  rw [rationalFunctionsSheaf_map_self, mul_right_comm, unitVal_inv_restrict_mul, one_mul]

/-- The pairing is locally surjective: `φ|_V = φ(e)·e^∨` is the image of `φ(e)·t⁻¹`. -/
theorem pairingPresheafHom_isLocallySurjective (hrel : HasLocalPairs D D') :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X.toScheme)
      (pairingPresheafHom hrel) := by
  refine ⟨fun {W} φ ↦ ?_⟩
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨U, hxU, ⟨P⟩⟩ := hrel x
  have hVU : (U ⊓ W : X.toScheme.Opens) ≤ U := inf_le_left
  have hVW : (U ⊓ W : X.toScheme.Opens) ≤ W := inf_le_right
  let P' := P.restrict hVU
  refine ⟨U ⊓ W, homOfLE hVW, ?_, ⟨hxU, hx⟩⟩
  let φ' : Γ(dualSheaf D.ideal.toModules, U ⊓ W) :=
    (AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf D.ideal.toModules).map (homOfLE hVW).op φ
  have key := P'.isFrame.eq_smul_dualFrame le_rfl φ'
  simp only [res_self] at key
  refine ⟨dualPair φ' le_rfl P'.e • P'.isLocalEquation.invSection le_rfl, ?_⟩
  change (pairingPresheafHom hrel).app (op (U ⊓ W))
    (dualPair φ' le_rfl P'.e • P'.isLocalEquation.invSection le_rfl) = φ'
  rw [_root_.map_smul]
  change dualPair φ' le_rfl P'.e • pairingFamily hrel (P'.isLocalEquation.invSection le_rfl) = φ'
  rw [pairingFamily_invSection]
  exact key

/-- The pairing is locally injective: `O_X(D')` is freely generated on `V` by `t⁻¹` and the target by
`e^∨`. -/
theorem pairingPresheafHom_isLocallyInjective (hrel : HasLocalPairs D D') :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X.toScheme)
      (pairingPresheafHom hrel) := by
  refine ⟨fun {W} h₁ h₂ heq ↦ ?_⟩
  change (pairingPresheafHom hrel).app W h₁ = (pairingPresheafHom hrel).app W h₂ at heq
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨U, hxU, ⟨P⟩⟩ := hrel x
  have hVU : (U ⊓ W.unop : X.toScheme.Opens) ≤ U := inf_le_left
  have hVW : (U ⊓ W.unop : X.toScheme.Opens) ≤ W.unop := inf_le_right
  let P' := P.restrict hVU
  refine ⟨U ⊓ W.unop, homOfLE hVW, ?_, ⟨hxU, hx⟩⟩
  change (lineBundlePresheaf D').map (homOfLE hVW).op h₁ =
    (lineBundlePresheaf D').map (homOfLE hVW).op h₂
  obtain ⟨r₁, hr₁⟩ := (P'.isLocalEquation.bijective_smul_invSection le_rfl).2
    ((lineBundlePresheaf D').map (homOfLE hVW).op h₁)
  obtain ⟨r₂, hr₂⟩ := (P'.isLocalEquation.bijective_smul_invSection le_rfl).2
    ((lineBundlePresheaf D').map (homOfLE hVW).op h₂)
  have hr₁' : r₁ • P'.isLocalEquation.invSection le_rfl =
    (lineBundlePresheaf D').map (homOfLE hVW).op h₁ := hr₁
  have hr₂' : r₂ • P'.isLocalEquation.invSection le_rfl =
    (lineBundlePresheaf D').map (homOfLE hVW).op h₂ := hr₂
  have key : (pairingPresheafHom hrel).app (op (U ⊓ W.unop))
      ((lineBundlePresheaf D').map (homOfLE hVW).op h₁) =
    (pairingPresheafHom hrel).app (op (U ⊓ W.unop))
      ((lineBundlePresheaf D').map (homOfLE hVW).op h₂) := by
    rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, heq]
  rw [← hr₁', ← hr₂', _root_.map_smul, _root_.map_smul] at key
  change r₁ • pairingFamily hrel (P'.isLocalEquation.invSection le_rfl) =
    r₂ • pairingFamily hrel (P'.isLocalEquation.invSection le_rfl) at key
  rw [pairingFamily_invSection] at key
  have hinj := (P'.isFrame.dualFrame_isFrame (U ⊓ W.unop) le_rfl).1
  have hr : r₁ = r₂ := hinj (by simpa only [res_self] using key)
  rw [← hr₁', ← hr₂', hr]

/-- After sheafification the pairing is an isomorphism. -/
theorem isIso_sheafification_map_pairingPresheafHom (hrel : HasLocalPairs D D') :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.toScheme.ringCatSheaf.obj)).map
      (pairingPresheafHom hrel)) :=
  @AlgebraicGeometry.Scheme.Modules.moduleSheafification_map_isIso_of_locallyBijective _ _ _ (pairingPresheafHom hrel)
    (pairingPresheafHom_isLocallyInjective hrel) (pairingPresheafHom_isLocallySurjective hrel)

/-- `O_X(D') ≅ O_X(D) = I_D^∨` (Hartshorne II.6.18 and II.6.13(b)). -/
def lineBundleModulesIsoSheaf (hrel : HasLocalPairs D D') :
    lineBundleModules D' ≅ D.sheaf :=
  letI := isIso_sheafification_map_pairingPresheafHom hrel
  (asIso ((PresheafOfModules.sheafification (𝟙 X.toScheme.ringCatSheaf.obj)).map
    (pairingPresheafHom hrel)) : lineBundleModules D' ≅ AlgebraicGeometry.Scheme.Modules.moduleSheafDual D.ideal.toModules) ≪≫
    (dualSheafIsoOld D.ideal.toModules).symm

end MiyaokaMori.EffCartierPairing

end
