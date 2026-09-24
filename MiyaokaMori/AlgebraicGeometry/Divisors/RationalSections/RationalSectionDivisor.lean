import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrd
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdCoordinate

/-! # The divisor of a rational section of a line bundle

For a line bundle `L` on an integral locally Noetherian scheme `W` and a nonzero rational section
`s ∈ L_η`, the Weil cycle `div_L(s) = Σ_z ord_{z,L}(s)[z]` (`z` over the points of coheight `1`,
`ord_{z,L}(s) = ord_z(s/t_z)` for a generator `t_z` of `L_z`); nonzero rational sections exist; changing
the section `s ↦ g·s` changes the divisor by a principal cycle. This is the material for the definition
of `c_1(L) ∩ [W]` in Stacks 02SJ (Fulton, Chapter 2), used for the intersection products in the proof
of Proposition 2.4 of the paper. The definition of `rationalSectionOrd` is in
`RationalSectionOrd`, and `RationalSectionOrdCoordinate` identifies it with the `Scheme.ord` of a
trivialization coordinate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry.Divisors AlgebraicGeometry.Divisors.LineGenericCoordinates

/-- `div_L(s)`: the cycle with coefficients `rationalSectionOrd`; local finiteness of the support is
`exists_nhds_finite_support_rationalSectionOrd` (on an affine open neighbourhood inside a trivializing open
the coefficient is the `Scheme.ord` of the rational function `c(s)`, nonzero at finitely many points). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor {W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (L : W.Modules) [L.IsLineBundle] (s : L.stalk (genericPoint W)) :
    AlgebraicGeometry.AlgebraicCycle W ℤ where
  toFun := AlgebraicGeometry.Scheme.Modules.rationalSectionOrd L s
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := fun z _ =>
    AlgebraicGeometry.Scheme.Modules.exists_nhds_finite_support_rationalSectionOrd L s z

@[simp]
theorem AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_apply
    {W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (L : W.Modules) [L.IsLineBundle] (s : L.stalk (genericPoint W)) (z : W) :
    L.rationalSectionDivisor s z = L.rationalSectionOrd s z := rfl

theorem AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero {W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] (L : W.Modules) [L.IsLineBundle] :
    ∃ s : L.stalk (genericPoint W), s ≠ 0 :=
  AlgebraicGeometry.Scheme.Modules.exists_ne_zero_of_trivialization L

theorem AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_smul {W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (L : W.Modules) [L.IsLineBundle] (s : L.stalk (genericPoint W)) (hs : s ≠ 0)
    (g : W.functionFieldˣ) :
    L.rationalSectionDivisor ((g : W.functionField) • s)
      = L.rationalSectionDivisor s + W.principalCycle g := by
  ext z
  obtain ⟨U, hzU, ⟨eU⟩⟩ := AlgebraicGeometry.Scheme.Modules.exists_trivialization L z
  have hc := AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_eq_ord_genericCoordinate'
    L U z hzU eU
  have hcs : genericCoordinate W L U ⟨⟨z, hzU⟩⟩ eU s ≠ 0 :=
    genericCoordinate_ne_zero W L U ⟨⟨z, hzU⟩⟩ eU s hs
  have hsm : genericCoordinate W L U ⟨⟨z, hzU⟩⟩ eU ((g : W.functionField) • s)
      = (g : W.functionField) * genericCoordinate W L U ⟨⟨z, hzU⟩⟩ eU s :=
    (genericCoordinate W L U ⟨⟨z, hzU⟩⟩ eU).map_smul (g : W.functionField) s
  show L.rationalSectionOrd ((g : W.functionField) • s) z
      = L.rationalSectionOrd s z + W.principalCycle g z
  rw [hc ((g : W.functionField) • s), hc s, hsm,
    AlgebraicGeometry.Scheme.ord_mul g.ne_zero hcs,
    AlgebraicGeometry.Scheme.principalCycle_apply, add_comm]

theorem AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_support {W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (L : W.Modules) [L.IsLineBundle] (s : L.stalk (genericPoint W)) (z : W)
    (hz : L.rationalSectionDivisor s z ≠ 0) : Order.coheight z = 1 := by
  by_contra h
  exact hz
    (AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_eq_zero_of_coheight_ne_one L s h)

namespace AlgebraicGeometry.Scheme.Modules

variable {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
  [AlgebraicGeometry.IsLocallyNoetherian W]

/-- (a) The divisor of a rational section of the trivial line bundle is a principal cycle (a consequence of
`rationalSectionOrd_eq_ord_genericCoordinate`). -/
theorem rationalSectionDivisor_eq_principalCycle_of_iso_unit (M : W.Modules)
    [M.IsLineBundle] (e : M ≅ SheafOfModules.unit W.ringCatSheaf)
    (s : M.stalk (genericPoint W)) (hs : s ≠ 0) :
    ∃ g : W.functionFieldˣ, M.rationalSectionDivisor s = W.principalCycle g := by
  let eU := topTrivializationOfIsoUnit M e
  have hne : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  let c := genericCoordinate W M ⊤ hne eU
  have hc : c s ≠ 0 := genericCoordinate_ne_zero W M ⊤ hne eU s hs
  refine ⟨Units.mk0 (c s) hc, ?_⟩
  ext z
  rw [AlgebraicGeometry.Scheme.principalCycle_apply]
  exact rationalSectionOrd_eq_ord_genericCoordinate M ⊤ z trivial eU s hs

/-- (b) A rational function `f`, viewed as a rational section of `O_W`, has divisor `div(f)`. -/
theorem exists_unit_rationalSection_divisor_eq_principalCycle
    (f : W.functionFieldˣ) :
    ∃ t : AlgebraicGeometry.Scheme.Modules.stalk (X := W) (SheafOfModules.unit W.ringCatSheaf)
        (genericPoint W), t ≠ 0 ∧
      AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor (W := W)
        (SheafOfModules.unit W.ringCatSheaf) t = W.principalCycle f := by
  obtain ⟨t₀, ht₀⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero
    (SheafOfModules.unit W.ringCatSheaf : W.Modules)
  obtain ⟨g₀, hg₀⟩ := rationalSectionDivisor_eq_principalCycle_of_iso_unit
    (SheafOfModules.unit W.ringCatSheaf : W.Modules) (Iso.refl _) t₀ ht₀
  refine ⟨((f * g₀⁻¹ : W.functionFieldˣ) : W.functionField) • t₀, ?_, ?_⟩
  · intro h
    apply ht₀
    have h2 := congrArg (fun x => (((f * g₀⁻¹)⁻¹ : W.functionFieldˣ) : W.functionField) • x) h
    simp only [smul_smul, smul_zero] at h2
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h2
  · rw [AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_smul _ t₀ ht₀, hg₀,
      ← AlgebraicGeometry.Scheme.principalCycle_mul, mul_comm, inv_mul_cancel_right]

end AlgebraicGeometry.Scheme.Modules

end
