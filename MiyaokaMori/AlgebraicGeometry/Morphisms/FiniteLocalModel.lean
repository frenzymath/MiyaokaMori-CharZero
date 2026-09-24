import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.FiniteLocalModelAlgebra
import MiyaokaMori.RingTheory.OrderOfVanishing.LatticeDetOrd
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteAffineNeighbourhood
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineFiberModel
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.DominantAffineAlgebraic

/-! # The finite local model of a proper morphism over a codimension-one point

For a proper morphism `p : X → Y` of integral locally Noetherian schemes, generically finite, and a
point `z ∈ Y` of codimension one, we construct a finite extension `A = O_{Y,z} → B` of domains whose
maximal ideals are the points of the fibre `p⁻¹{z}`, matching coheights, residue degrees and orders of
vanishing (`exists_finite_local_model`). This is the local model used in the proof of Stacks Project,
Tag 02RT (proper pushforward of principal divisors); see also Tag 02RM.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- The function field extension `R(Y) → R(X)` given by the stalk map at the generic point. -/
@[reducible] def functionFieldAlgebra {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Y)
    (hp : p.base (genericPoint X) = genericPoint Y) : Algebra Y.functionField X.functionField :=
  ((Y.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
    p.stalkMap (genericPoint X)).hom.toAlgebra

/-- The composite `O_{Y,z} → R(Y) → R(X)`. -/
@[reducible] def stalkToFunctionFieldAlgebraOfHom {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ Y) (hp : p.base (genericPoint X) = genericPoint Y) (z : Y) :
    Algebra (Y.presheaf.stalk z) X.functionField :=
  ((functionFieldAlgebra p hp).algebraMap.comp
    (algebraMap (Y.presheaf.stalk z) Y.functionField)).toAlgebra

/-- **Finite local model.** Let `X`, `Y` be integral locally Noetherian schemes, `p : X → Y` proper and
sending the generic point to the generic point, with finite function field extension `R(X)/R(Y)` (the
residue field map at the generic point is finite), and let `z ∈ Y` have codimension one
(`coheight z = 1`). Write `A = O_{Y,z}`, `K = R(Y)`, `L = R(X)`, with `K → L` the stalk map at the
generic point. Then there is a domain `B` (in the universe of `X`) with a finite injective
homomorphism `A → B` and a map `B → L` making `L = Frac B`, compatible with `A → K → L`, together with
a bijection `e : MaxSpec B ≃ p⁻¹{z}` such that for every maximal ideal `m` (with `x = e m`):
(i) `coheight x = 1` (note: not `height x = height z`; Mathlib's `Order.height x` is
`dim closure {x}`, which is not a local quantity — for varieties the user recovers it from the
coheight by the dimension formula);
(ii) `[κ(m) : κ(m_A)]` (`Ideal.inertiaDeg'`) `= [κ(x) : κ(z)]` (`p.residueDegree x`);
(iii) for `b ∈ B ∖ 0`: `ord_x(b)` (Mathlib's `Scheme.ord`, with `b` viewed in `L`) `= ord_{B_m}(b)`
(`Ring.ord`).

Proof.
1. `exists_affine_finite_neighbourhood` (with `dim O_{Y,z} = coheight z = 1`,
   `ringKrullDim_stalk_eq_coheight`) gives an affine open neighbourhood `U` of `z` with `W = p⁻¹U`
   affine and `R = Γ(Y, U) → C = Γ(X, W)` finite; `appLE_injective_of_genericPoint` gives that `R → C`
   is injective; `X`, `Y` integral makes `R`, `C` domains; `Y` locally Noetherian makes `R` Noetherian;
   `L = Frac C` (`functionField_isFractionRing_of_isAffineOpen`).
2. Let `𝔭 ⊂ R` be the prime of `z`, so `A = R_𝔭` (`IsAffineOpen.isLocalization_stalk`) and
   `ht 𝔭 = dim A = 1`. Put `B := C_𝔭 = FiniteLocalModel.LocB C 𝔭`; the algebraic lemmas
   `FiniteLocalModel.isDomain_B`, `finite_AB`, `injective_AB`, `isFractionRing_BL`, `tower_ABL` give
   that `B` is a domain, `A → B` is finite and injective, `Frac B = L`, and the tower is compatible.
   The compatibility "`A → K → L` and `R → C → L` agree on `R`" needed for the tower comes from
   `stalkMapOfEq_germ` at the generic point (`p η_X = η_Y`).
3. `e := FiniteLocalModel.maxEquiv` (`MaxSpec B ≃ {𝔮 | 𝔮 ∩ R = 𝔭}`) composed with `fiberEquiv`
   (`{𝔮 | 𝔮 ∩ R = 𝔭} ≃ p⁻¹{z}`); explicitly `e m = fromSpec (m ∩ C)`.
4. For `m`, let `𝔮 = m ∩ C`, `x = fromSpec 𝔮`; then `S = O_{X,x}` is the localization of `C` at `𝔮`
   (`IsAffineOpen.isLocalization_stalk'`). (i): `coheight x = dim S = ht 𝔮 = 1`
   (`FiniteLocalModel.height_eq_one_of_comap_eq`).
5. (ii): the stalk map `φ : A ≅ O_{Y,p x} → S` agrees with `R → C → S` on `R` (`stalkMapOfEq_germ`);
   `FiniteLocalModel.inertiaDeg_eq` gives `inertiaDeg' = [κ(S) : κ(A)]`, and
   `finrank_residueField_stalkMapOfEq` identifies this with `p.residueDegree x`.
6. (iii): `S → L` (Mathlib's stalk-to-function-field map) is compatible with `C → L`
   (`functionField_isScalarTower`); `FiniteLocalModel.exists_ord_eq` provides `s ∈ S` with the same
   image as `b` in `L` and `ord_S(s) = ord_{B_m}(b)`; `Scheme.ord` is by definition `Ring.ordFrac S`,
   which agrees with `Ring.ord` on elements of `S` (`Submodule.ordFrac_algebraMap`). -/
theorem exists_finite_local_model {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (p : X ⟶ Y) [IsProper p]
    (hp : p.base (genericPoint X) = genericPoint Y)
    (hfin : (p.residueFieldMap (genericPoint X)).hom.Finite) (z : Y)
    (hz : Order.coheight z = 1) :
    letI := functionFieldAlgebra p hp
    letI := stalkToFunctionFieldAlgebraOfHom p hp z
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : Algebra (Y.presheaf.stalk z) B)
      (_ : FaithfulSMul (Y.presheaf.stalk z) B) (_ : Module.Finite (Y.presheaf.stalk z) B)
      (_ : Algebra B X.functionField) (_ : IsFractionRing B X.functionField)
      (_ : IsScalarTower (Y.presheaf.stalk z) B X.functionField)
      (e : MaximalSpectrum B ≃ {x : X // p.base x = z}),
      ∀ m : MaximalSpectrum B,
        Order.coheight (e m).1 = 1 ∧
        Ideal.inertiaDeg' (IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) m.asIdeal =
          p.residueDegree (e m).1 ∧
        ∀ b : B, b ≠ 0 → X.ord (algebraMap B X.functionField b) (e m).1 =
          ((Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap B _ b)).toNat : ℤ) := by
  classical
  letI algKL : Algebra Y.functionField X.functionField := functionFieldAlgebra p hp
  letI algAL : Algebra (Y.presheaf.stalk z) X.functionField :=
    stalkToFunctionFieldAlgebraOfHom p hp z
  have hdimz : ringKrullDim (Y.presheaf.stalk z) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight, hz]; rfl
  obtain ⟨U, hU, hzU, hW, hfinapp⟩ := exists_affine_finite_neighbourhood p hp hfin z hdimz
  have hηU : genericPoint Y ∈ U := genericPoint_mem_of_nonempty U ⟨z, hzU⟩
  have hηW : genericPoint X ∈ p ⁻¹ᵁ U := by
    show p.base _ ∈ U
    rw [hp]; exact hηU
  haveI : Nonempty U := ⟨⟨z, hzU⟩⟩
  haveI : Nonempty (p ⁻¹ᵁ U) := ⟨⟨_, hηW⟩⟩
  letI algRC : Algebra Γ(Y, U) Γ(X, p ⁻¹ᵁ U) := (p.app U).hom.toAlgebra
  have hinj : Function.Injective (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) := by
    have := appLE_injective_of_genericPoint p hp U (p ⁻¹ᵁ U) le_rfl hηW
    rwa [← Scheme.Hom.app_eq_appLE] at this
  haveI : Module.Finite Γ(Y, U) Γ(X, p ⁻¹ᵁ U) := hfinapp
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let 𝔭 : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
  letI algRA : Algebra Γ(Y, U) (Y.presheaf.stalk z) := Y.presheaf.algebra_section_stalk ⟨z, hzU⟩
  haveI hlocA : IsLocalization.AtPrime (Y.presheaf.stalk z) 𝔭 := hU.isLocalization_stalk ⟨z, hzU⟩
  have h𝔭 : 𝔭.height = 1 := by
    have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (Y.presheaf.stalk z)
    rw [hdimz] at h1
    exact_mod_cast h1.symm
  haveI hfracC : IsFractionRing Γ(X, p ⁻¹ᵁ U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X _ hW
  letI algAB := FiniteLocalModel.algAB Γ(X, p ⁻¹ᵁ U) 𝔭 (Y.presheaf.stalk z)
  letI algBL := FiniteLocalModel.algBL Γ(X, p ⁻¹ᵁ U) 𝔭 X.functionField hinj
  have hRL : (algebraMap (Y.presheaf.stalk z) X.functionField).comp
      (algebraMap Γ(Y, U) (Y.presheaf.stalk z)) =
      (algebraMap Γ(X, p ⁻¹ᵁ U) X.functionField).comp
        (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) := by
    ext r
    show stalkMapOfEq p hp (algebraMap (Y.presheaf.stalk z) Y.functionField
      (Y.presheaf.germ U z hzU r)) = _
    rw [Scheme.algebraMap_germ_eq_germToFunctionField]
    exact stalkMapOfEq_germ p hp U hηU r
  let e : MaximalSpectrum (FiniteLocalModel.LocB Γ(X, p ⁻¹ᵁ U) 𝔭) ≃ {x : X // p.base x = z} :=
    (FiniteLocalModel.maxEquiv Γ(X, p ⁻¹ᵁ U) 𝔭 (Y.presheaf.stalk z)).trans
      (fiberEquiv p hU hW hzU)
  refine ⟨FiniteLocalModel.LocB Γ(X, p ⁻¹ᵁ U) 𝔭, inferInstance,
    FiniteLocalModel.isDomain_B _ 𝔭 hinj, algAB,
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (FiniteLocalModel.injective_AB _ 𝔭 (Y.presheaf.stalk z) hinj),
    FiniteLocalModel.finite_AB _ 𝔭 _, algBL,
    FiniteLocalModel.isFractionRing_BL _ 𝔭 _ hinj,
    FiniteLocalModel.tower_ABL _ 𝔭 _ _ hinj hRL, e, ?_⟩
  intro m
  haveI := m.isMaximal
  let 𝔮 : PrimeSpectrum Γ(X, p ⁻¹ᵁ U) :=
    ⟨m.asIdeal.comap (algebraMap Γ(X, p ⁻¹ᵁ U) _), inferInstance⟩
  have hxe : (e m).1 = hW.fromSpec 𝔮 := rfl
  have hxW : hW.fromSpec 𝔮 ∈ p ⁻¹ᵁ U := fromSpec_mem_of_isAffineOpen hW 𝔮
  have hxz : p.base (hW.fromSpec 𝔮) = z := (e m).2
  rw [hxe]
  letI algCS : Algebra Γ(X, p ⁻¹ᵁ U) (X.presheaf.stalk (hW.fromSpec 𝔮)) :=
    X.presheaf.algebra_section_stalk ⟨hW.fromSpec 𝔮, hxW⟩
  haveI hlocS : IsLocalization.AtPrime (X.presheaf.stalk (hW.fromSpec 𝔮))
      (m.asIdeal.comap (algebraMap Γ(X, p ⁻¹ᵁ U) _)) := hW.isLocalization_stalk' 𝔮 hxW
  have h𝔮R := FiniteLocalModel.comap_R_of_isMaximal Γ(X, p ⁻¹ᵁ U) 𝔭 (Y.presheaf.stalk z) m.asIdeal
  have hco : Order.coheight (hW.fromSpec 𝔮) = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight (hW.fromSpec 𝔮)
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (m.asIdeal.comap (algebraMap Γ(X, p ⁻¹ᵁ U) _)) (X.presheaf.stalk (hW.fromSpec 𝔮)),
      FiniteLocalModel.height_eq_one_of_comap_eq _ 𝔭 hinj h𝔭 h𝔮R] at h1
    exact_mod_cast h1.symm
  refine ⟨hco, ?_, ?_⟩
  · have hφ : (stalkMapOfEq p hxz).comp (algebraMap Γ(Y, U) (Y.presheaf.stalk z)) =
        (algebraMap Γ(X, p ⁻¹ᵁ U) (X.presheaf.stalk (hW.fromSpec 𝔮))).comp
          (algebraMap Γ(Y, U) Γ(X, p ⁻¹ᵁ U)) := by
      ext r
      exact stalkMapOfEq_germ p hxz U hzU r
    rw [FiniteLocalModel.inertiaDeg_eq _ 𝔭 _ m.asIdeal _ (stalkMapOfEq p hxz) hφ]
    exact finrank_residueField_stalkMapOfEq p hxz
  · intro b hb
    haveI : IsScalarTower Γ(X, p ⁻¹ᵁ U) (X.presheaf.stalk (hW.fromSpec 𝔮)) X.functionField :=
      functionField_isScalarTower X (p ⁻¹ᵁ U) ⟨hW.fromSpec 𝔮, hxW⟩
    obtain ⟨s, hs1, hs2⟩ := FiniteLocalModel.exists_ord_eq Γ(X, p ⁻¹ᵁ U) 𝔭 (Y.presheaf.stalk z)
      m.asIdeal (X.presheaf.stalk (hW.fromSpec 𝔮)) X.functionField hinj b
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk (hW.fromSpec 𝔮)) :=
      krullDimLE_of_coheight_le hco.le
    haveI := FiniteLocalModel.isFractionRing_BL Γ(X, p ⁻¹ᵁ U) 𝔭 X.functionField hinj
    haveI := FiniteLocalModel.isDomain_B Γ(X, p ⁻¹ᵁ U) 𝔭 hinj
    have hb' : algebraMap (FiniteLocalModel.LocB Γ(X, p ⁻¹ᵁ U) 𝔭) X.functionField b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ X.functionField)).mpr hb
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [map_zero] at hs1
      exact hb' hs1.symm
    rw [Scheme.ord_eq_iff hco hb']
    change Ring.ordFrac (X.presheaf.stalk (hW.fromSpec 𝔮)) _ = _
    rw [← hs1, Submodule.ordFrac_algebraMap hs0, hs2]
    rfl

end AlgebraicGeometry

end
