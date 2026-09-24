import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.GammaStarAwayRingHom
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01pw
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01pwUniformExponent
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos

/-! # Stacks 01PW in the language of the section ring

**Stacks 01PW in the language of the section ring**: for `X` quasi-compact and quasi-separated,
`L` a line bundle and `s ∈ Γ(X, L^{⊗e})`, the ring map

  `awayToSections : Γ_*(X, L)_{(s)} → Γ(X_s, O_X)`,  `a/s^n ↦ a · s^{-n}`

is bijective (`awayToSections_bijective`). This is the form in which Stacks 01Q1 quotes 01PW
("By Lemma 01PW the ring map `S_{(s)} → Γ(X_s, O_X)` is an isomorphism").

The two halves of 01PW are formalized in `Stacks01pw` in the
language of tensor sections (`sectionTensor`, `tensorPowSection s n ∈ Γ(X, (L^{⊗e})^{⊗n})`):
* (1) `exists_sectionTensor_tensorPowSection_eq_zero`: `m|_{X_s} = 0 ⟹ ∃ k, m ⊗ s^{⊗k} = 0`;
* (2) `exists_tensorPow_section_restrict_eq`: `t ∈ Γ(X_s, F) ⟹ ∃ n, m ∈ Γ(X, F ⊗ (L^{⊗e})^{⊗n})` with
  `m|_{X_s} = t ⊗ s^{⊗n}`.

The bridge to the section ring is `tensorPowMulIso_hom_app_tensorPowSection`: the rearrangement
isomorphism `(L^{⊗e})^{⊗n} ≅ L^{⊗(e·n)}` (`tensorPowMulIso`, built from `tensorPowAddIso`, which is
also what defines the multiplication of `Γ_*(X, L)`) sends `s^{⊗n}` to the section of `s^n ∈ Γ_*(X, L)`.
Proof by induction on `n`: both recursions are "multiply by `s` on the right" (`tensorIsoTensorObj`,
`whiskerRight_app_tensorSections''`, `gammaStarComponent_mul`); the degree `e·(n+1) = e·n + e` is
definitional. With this bridge:

* `exists_mul_pow_eq_zero_of_res_eq_zero` (injectivity): `a|_{X_s} = 0 ⟹ ∃ k, a · s^k = 0` in
  `Γ_*(X, L)` — apply 01PW(1) and transport `a ⊗ s^{⊗k}` through
  `L^{⊗p} ⊗ (L^{⊗e})^{⊗k} ≅ L^{⊗(p + e·k)}` to the section of `a · s^k`;
* `exists_awayToSections_mk_eq` (surjectivity): 01PW(2) with `F = O_X`, transporting
  `t ⊗ s^{⊗n}` through `O_X ⊗ (L^{⊗e})^{⊗n} ≅ L^{⊗(e·n)}` (`unitTensorLeftIso`, whose action on pure
  tensors is `t ⊗ p ↦ t • p` by `leftUnitor_app_tensorSections`) gives `a ∈ Γ(X, L^{⊗en})` with
  `a|_{X_s} = t • s^n|_{X_s}`, i.e. `ψ(a/s^n) = t`.

Reference: Stacks 01PW (`properties-lemma-invert-s-sections`) and its use in 01Q1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]

/-! ## The bridge `tensorPowMulIso (s^{⊗n}) = (s^n)_{e·n}` -/

/-- `s^n ∈ Γ_*(X, L)_{e·n}` (degree written as `e * n`, matching `tensorPowMulIso`). -/
theorem gammaStarOf_pow_mem_mul {e : ℕ} (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤)) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s ^ n ∈
      AlgebraicGeometry.Scheme.Modules.gammaStarGrading L (e * n) := by
  induction n with
  | zero => rw [pow_zero]; exact SetLike.one_mem_graded (AlgebraicGeometry.Scheme.Modules.gammaStarGrading L)
  | succ n ih =>
    rw [pow_succ]
    exact SetLike.mul_mem_graded ih (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e s)

/-- A homogeneous element with vanishing component is zero. -/
theorem eq_zero_of_gammaStarComponent_eq_zero {x : AlgebraicGeometry.Scheme.Modules.gammaStar L} {m : ℕ}
    (hx : x ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L m)
    (h : AlgebraicGeometry.Scheme.Modules.gammaStarComponent L x m = 0) : x = 0 := by
  rw [← gammaStarOf_gammaStarComponent L hx, h]
  exact map_zero (DirectSum.of ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsPiece ⊤) m)

/-- **The bridge**: the rearrangement isomorphism `(L^{⊗e})^{⊗n} ≅ L^{⊗(e·n)}` sends `s^{⊗n}` to the
section of `s^n ∈ Γ_*(X, L)`. -/
theorem tensorPowMulIso_hom_app_tensorPowSection {e : ℕ}
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤)) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) =
      AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
        (AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s ^ n) (e * n) := by
  induction n with
  | zero =>
    show _ = AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s ^ 0) 0
    rw [pow_zero, gammaStarComponent_one]
    rfl
  | succ n ih =>
    rw [pow_succ]
    show _ = AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s ^ n * AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s)
      (e * n + e)
    rw [gammaStarComponent_mul L (gammaStarOf_pow_mem_mul L s n)
      (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e s), gammaStarComponent_gammaStarOf, ← ih]
    have h1 := whiskerRight_app_tensorSections'' (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) s
    show ((AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L (e * n) e).inv).app ⊤
      (((AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom ▷
        AlgebraicGeometry.Scheme.Modules.tensorPow L e).app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) s)) = _
    rw [h1]
    rfl

/-! ## Injectivity: `a|_{X_s} = 0 ⟹ a · s^k = 0` -/

/-- `X_s`, spelled through the section of `gammaStarOf s`. -/
theorem nonvanishingLocus_le_gammaStarOf {e : ℕ} (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s ≤
      (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s) e) := by
  rw [gammaStarComponent_gammaStarOf]

/-- **Stacks 01PW (1) in the section ring**: if the section of a homogeneous `a ∈ Γ_*(X, L)_p`
vanishes on `X_s`, then `a · s^k = 0` for some `k`. -/
theorem exists_mul_pow_eq_zero_of_res_eq_zero [CompactSpace X] {e : ℕ}
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤))
    {a : AlgebraicGeometry.Scheme.Modules.gammaStar L} {p : ℕ}
    (ha : a ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L p)
    (h : (AlgebraicGeometry.Scheme.Modules.tensorPow L p).res
      (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s ≤ ⊤)
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a p) = 0) :
    ∃ k : ℕ, a * AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s ^ k = 0 := by
  obtain ⟨k, hk⟩ := AlgebraicGeometry.Scheme.Modules.exists_sectionTensor_tensorPowSection_eq_zero
    (AlgebraicGeometry.Scheme.Modules.tensorPow L e) s (AlgebraicGeometry.Scheme.Modules.tensorPow L p)
    (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a p) h
  refine ⟨k, eq_zero_of_gammaStarComponent_eq_zero L
    (SetLike.mul_mem_graded ha (gammaStarOf_pow_mem_mul L s k)) ?_⟩
  -- transport `a ⊗ s^{⊗k} = 0` through `L^{⊗p} ⊗ (L^{⊗e})^{⊗k} ≅ L^{⊗(p + e k)}`
  set Ξ := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (AlgebraicGeometry.Scheme.Modules.tensorPow L p)
      (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L e) k) ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso (AlgebraicGeometry.Scheme.Modules.tensorPow L p)
      (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e k) ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L p (e * k)).symm with hΞ
  have h2 : AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
      (a * AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s ^ k) (p + e * k) =
      Ξ.hom.app ⊤ (sectionTensor (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a p)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k)) := by
    rw [gammaStarComponent_mul L ha (gammaStarOf_pow_mem_mul L s k),
      ← tensorPowMulIso_hom_app_tensorPowSection L s k]
    have h3 := whiskerLeft_app_tensorSections'' (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e k).hom ⊤
      (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a p)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k)
    show _ = ((AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L p (e * k)).inv).app ⊤
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L p ◁
          (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e k).hom).app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤
          (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L a p)
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k)))
    rw [h3]
    rfl
  rw [h2, hk]
  exact (Ξ.hom.app ⊤).hom.map_zero

/-- Injectivity of `awayToSections` on `X_s` (`X` quasi-compact). -/
theorem awayToSections_injective [CompactSpace X] {e : ℕ}
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤)) :
    Function.Injective (awayToSections L (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e s)
      (nonvanishingLocus_le_gammaStarOf L s)) := by
  have hs := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e s
  refine (injective_iff_map_eq_zero _).mpr fun z hz => ?_
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ hs z
  have h1 := awayToSections_mk_smul L hs (nonvanishingLocus_le_gammaStarOf L s) n a ha
  rw [hz, zero_smul] at h1
  obtain ⟨k, hk⟩ := exists_mul_pow_eq_zero_of_res_eq_zero L s ha h1.symm
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.Away.val_mk,
    HomogeneousLocalization.val_zero, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨_, k, rfl⟩, by rw [mul_comm]; exact hk⟩

/-! ## Surjectivity: every function on `X_s` is `a · s^{-n}` -/

/-- The left unitor `O_X ⊗ P ≅ P` on pure tensors: `t ⊗ p ↦ t • p`. -/
theorem unitTensorLeftIso_hom_app_moduleTensorSection (P : X.Modules) (U : X.Opens) (t : Γ(X, U))
    (p : Γ(P, U)) :
    (AlgebraicGeometry.Scheme.Modules.unitTensorLeftIso P).hom.app U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (t : Γ(SheafOfModules.unit X.ringCatSheaf, U)) p) = t • p := by
  have h1 := whiskerRight_app_tensorSections''
    (CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) U
    (t : Γ(SheafOfModules.unit X.ringCatSheaf, U)) p
  show (λ_ P).hom.app U
    ((CategoryTheory.eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X) ▷ P).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (SheafOfModules.unit X.ringCatSheaf) P U
        (t : Γ(SheafOfModules.unit X.ringCatSheaf, U)) p)) = t • p
  rw [h1]
  exact AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections P U t p

/-- **Stacks 01PW (2) in the section ring**: every `t ∈ Γ(X_s, O_X)` is `ψ(a/s^n)` for some `n` and
`a ∈ Γ_*(X, L)_{n e}` (`X` quasi-compact and quasi-separated). -/
theorem exists_awayToSections_mk_eq [CompactSpace X] [QuasiSeparatedSpace X] {e : ℕ}
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤))
    (t : Γ(X, (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s)) :
    ∃ (n : ℕ) (a : AlgebraicGeometry.Scheme.Modules.gammaStar L)
      (ha : a ∈ AlgebraicGeometry.Scheme.Modules.gammaStarGrading L (n • e)),
      awayToSections L (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e s)
        (nonvanishingLocus_le_gammaStarOf L s)
        (HomogeneousLocalization.Away.mk _ (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e s) n a ha) =
      t := by
  have hs := AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e s
  have : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    inferInstanceAs ((AlgebraicGeometry.Scheme.Modules.tensorPow L 0).IsQuasicoherent)
  obtain ⟨n, m, hm⟩ := AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_restrict_eq
    (AlgebraicGeometry.Scheme.Modules.tensorPow L e) s (SheafOfModules.unit X.ringCatSheaf)
    (t : Γ(SheafOfModules.unit X.ringCatSheaf, (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s))
  -- the iso `Ξ : O_X ⊗ (L^{⊗e})^{⊗n} ≅ L^{⊗(e n)}` and `a₀ := Ξ m`
  have key : (AlgebraicGeometry.Scheme.Modules.tensorPow L (e * n)).res
      (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s ≤ ⊤)
      ((AlgebraicGeometry.Scheme.Modules.unitTensorLeftIso
          (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L e) n) ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom.app ⊤ m) =
      t • (AlgebraicGeometry.Scheme.Modules.tensorPow L (e * n)).res
        (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.gammaStarComponent L
          (AlgebraicGeometry.Scheme.Modules.gammaStarOf L e s ^ n) (e * n)) := by
    have e1 := (Hom.app_res (AlgebraicGeometry.Scheme.Modules.unitTensorLeftIso
          (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L e) n) ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom
      (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s ≤ ⊤) m).symm
    have e2 := congrArg (fun w => (AlgebraicGeometry.Scheme.Modules.unitTensorLeftIso
          (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L e) n) ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom.app
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s) w) hm
    have e3 := congrArg (fun w => (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom.app
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s) w)
      (unitTensorLeftIso_hom_app_moduleTensorSection
        (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L e) n)
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s) t
        ((AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L e) n).res
          le_top (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n)))
    have e4 := Hom.app_smul (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom t
      ((AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L e) n).res
        (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s ≤ ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n))
    have e5 := Hom.app_res (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom
      (le_top : (AlgebraicGeometry.Scheme.Modules.tensorPow L e).nonvanishingLocus s ≤ ⊤)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n)
    exact e1.trans (e2.trans (e3.trans (e4.trans (congrArg (fun w => t • w)
      (e5.trans (congrArg _ (tensorPowMulIso_hom_app_tensorPowSection L s n)))))))
  have hne : n • e = e * n := by rw [smul_eq_mul, mul_comm]
  refine ⟨n, AlgebraicGeometry.Scheme.Modules.gammaStarOf L (e * n)
    ((AlgebraicGeometry.Scheme.Modules.unitTensorLeftIso
        (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L e) n) ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L e n).hom.app ⊤ m), ?_, ?_⟩
  · rw [hne]; exact AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L (e * n) _
  · apply awayToSections_mk_unique
    rw [smul_res_gammaStarComponent_congr L hne, gammaStarComponent_gammaStarOf]
    exact key.symm

/-- **Stacks 01PW**: `Γ_*(X, L)_{(s)} → Γ(X_s, O_X)` is bijective for `X` quasi-compact and
quasi-separated. -/
theorem awayToSections_bijective [CompactSpace X] [QuasiSeparatedSpace X] {e : ℕ}
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L e, ⊤)) :
    Function.Bijective (awayToSections L (AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem L e s)
      (nonvanishingLocus_le_gammaStarOf L s)) := by
  refine ⟨awayToSections_injective L s, fun t => ?_⟩
  obtain ⟨n, a, ha, h⟩ := exists_awayToSections_mk_eq L s t
  exact ⟨_, h⟩

end AlgebraicGeometry.Scheme.Modules

end
