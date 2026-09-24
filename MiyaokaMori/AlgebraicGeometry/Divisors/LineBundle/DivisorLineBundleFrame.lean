import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleIsSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleLocalEquation
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameTrivialization
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso

/-! # Frames of the line bundle of a Cartier divisor

Let `t ∈ 𝒦^*(U)` be a local equation of the Cartier divisor `D` on `U`. Then `t^{-1} ∈ O_X(D)(U)`, and it
is a frame of `O_X(D)` on `U` (`IsLocalEquation.isFrame`: for every `W ⊆ U`, `r ↦ r·t^{-1}|_W` is a
bijection `O_X(W) → O_X(D)(W)`). Consequently `O_X(D)` is a line bundle (`lineBundleModules_isLineBundle`),
hence locally free, of finite type and of rank `1` at every point — the three propositional fields of
`CartierDivisor.lineBundle`.

Proof:
1. Injectivity: `O_X → 𝒦_X` is injective on every open and `t` is a unit.
2. Surjectivity: sections are characterized by `h ∈ O_X(D)(W) ⟺ h·t|_W ∈ O_X(W)`
   (`DivisorLineBundleLocalEquation`).
3. Sheafification does not change sections (`DivisorLineBundleIsSheaf`), which transports the bijection
   to `Γ(O_X(D), W)`; every point has a local equation nearby, hence a frame
   (`isLineBundle_iff_exists_frame`).
Source: Hartshorne II.6.13(a): `L(D)|_{U_i} = f_i^{-1}·O_{U_i}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CartierDivisor

variable {k : Type u} [Field k] {X : Variety k}

theorem unitVal_inv_mul {U : X.toScheme.Opens}
    (g : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    unitVal g⁻¹ * unitVal g = 1 :=
  Units.inv_mul (show (X.toScheme.rationalFunctionsSheaf.val.obj (op U))ˣ from g)

/-- The product of `t^{-1}|_W` and `t|_W` is `1`. -/
theorem unitVal_inv_restrict_mul {U W : X.toScheme.Opens} (hWU : W ≤ U)
    (t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom (unitVal t⁻¹) *
      unitVal (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t) = 1 := by
  rw [unitVal_restrict, ← map_mul, unitVal_inv_mul, map_one]

variable {D : CartierDivisor X} {U : X.toScheme.Opens}
  {t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)}

/-- `t^{-1}|_W ∈ O_X(D)(W)`. -/
def IsLocalEquation.invSection (ht : IsLocalEquation D U t) {W : X.toScheme.Opens} (hWU : W ≤ U) :
    CartierDivisor.lineBundleSections D W :=
  ⟨(X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom (unitVal t⁻¹),
    (ht.mem_lineBundleSections_iff hWU _).mpr
      ⟨1, (map_one _).trans (unitVal_inv_restrict_mul hWU t).symm⟩⟩

theorem IsLocalEquation.invSection_restrict (ht : IsLocalEquation D U t) {W W' : X.toScheme.Opens}
    (hWU : W ≤ U) (hW'W : W' ≤ W) :
    CartierDivisor.lineBundleRestrict D (homOfLE hW'W) (ht.invSection hWU) =
      ht.invSection (hW'W.trans hWU) :=
  Subtype.ext (X.toScheme.rationalFunctionsSheaf_map_map hWU hW'W (unitVal t⁻¹))

/-- `r ↦ r·t^{-1}|_W` is a bijection `O_X(W) → O_X(D)(W)`. -/
theorem IsLocalEquation.bijective_smul_invSection (ht : IsLocalEquation D U t)
    {W : X.toScheme.Opens} (hWU : W ≤ U) :
    Function.Bijective (fun r : Γ(X.toScheme, W) => r • ht.invSection hWU) := by
  have hinv := unitVal_inv_restrict_mul hWU t
  have hsmul : ∀ r : Γ(X.toScheme, W), (r • ht.invSection hWU).1 =
      (X.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom r * (ht.invSection hWU).1 :=
    fun _ => rfl
  constructor
  · intro r r' hrr
    apply X.toScheme.toRationalFunctionsSheaf_app_injective W
    have h1 := congrArg Subtype.val hrr
    change (r • ht.invSection hWU).1 = (r' • ht.invSection hWU).1 at h1
    rw [hsmul, hsmul] at h1
    have h2 := congrArg (fun z => z *
      unitVal (X.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t)) h1
    change _ * (ht.invSection hWU).1 * _ = _ * (ht.invSection hWU).1 * _ at h2
    rw [mul_assoc, mul_assoc] at h2
    change _ * ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom (unitVal t⁻¹) * _)
      = _ * ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom (unitVal t⁻¹) * _) at h2
    rw [hinv, mul_one, mul_one] at h2
    exact h2
  · intro z
    obtain ⟨r₀, hr⟩ := (ht.mem_lineBundleSections_iff hWU z.1).mp z.2
    let r : Γ(X.toScheme, W) := r₀
    refine ⟨r, Subtype.ext ?_⟩
    change (r • ht.invSection hWU).1 = z.1
    rw [hsmul, hr]
    change z.1 * _ * (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom
      (unitVal t⁻¹) = z.1
    rw [mul_assoc, mul_comm (unitVal _), hinv, mul_one]

/-- The frame element: `t^{-1}` viewed as an element of `Γ(O_X(D), U)`. -/
def IsLocalEquation.frame (ht : IsLocalEquation D U t) :
    Γ(CartierDivisor.lineBundleModules D, U) :=
  CartierDivisor.lineBundleSectionEquiv D U (ht.invSection le_rfl)

theorem IsLocalEquation.res_frame (ht : IsLocalEquation D U t) {W : X.toScheme.Opens}
    (hWU : W ≤ U) :
    (CartierDivisor.lineBundleModules D).res hWU ht.frame =
      CartierDivisor.lineBundleSectionEquiv D W (ht.invSection hWU) := by
  refine (CartierDivisor.lineBundleSectionEquiv_restrict D hWU _).trans ?_
  rw [ht.invSection_restrict]

/-- Hartshorne II.6.13(a): `t^{-1}` is a frame of `O_X(D)` on `U`. -/
theorem IsLocalEquation.isFrame (ht : IsLocalEquation D U t) :
    AlgebraicGeometry.Scheme.Modules.IsFrame (CartierDivisor.lineBundleModules D) U ht.frame := by
  intro W hWU
  have hfun : (fun r : Γ(X.toScheme, W) =>
      r • (CartierDivisor.lineBundleModules D).res hWU ht.frame) =
      (CartierDivisor.lineBundleSectionEquiv D W) ∘
        (fun r : Γ(X.toScheme, W) => r • ht.invSection hWU) := by
    funext r
    rw [ht.res_frame hWU]
    exact ((CartierDivisor.lineBundleSectionEquiv D W).map_smul r _).symm
  rw [hfun]
  exact (CartierDivisor.lineBundleSectionEquiv D W).bijective.comp
    (ht.bijective_smul_invSection hWU)

end CartierDivisor

/-- `O_X(D)` is a line bundle (locally isomorphic to `O_X`). -/
instance CartierDivisor.lineBundleModules_isLineBundle {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) :
    AlgebraicGeometry.Scheme.Modules.IsLineBundle (CartierDivisor.lineBundleModules D) :=
  (AlgebraicGeometry.Scheme.Modules.isLineBundle_iff_exists_frame _).mpr fun p => by
    obtain ⟨U, hpU, t, ht⟩ := CartierDivisor.exists_isLocalEquation D p
    exact ⟨U, hpU, ht.frame, ht.isFrame⟩

end
