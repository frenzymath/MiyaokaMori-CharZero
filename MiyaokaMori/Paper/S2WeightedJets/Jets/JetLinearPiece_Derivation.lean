import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetLinearPiece_Defs
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetLinearPiece_Generation
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaQuasicoherent

/-! # The linear piece of the jet algebra: the local coefficient map `θ_U : Γ(U, sec^*Ω_{Z/C}) → Γ(U, L_{q+1})`

The local coefficient maps feeding the dual of the linear piece (`DeformedJetAlgebraFiberAtZero_LinearPieceDual`).
Notation as in `JetLinearPiece_Defs`: `U ⊆ C` affine, `A := Γ(C, U)`, `B := Γ(Z, π⁻¹U)`, `ε := sec^♯ : B → A`,
`J := J_r(B, ε)`, `d_q b := coeffClass ε r (q+1) b`, `S_{q+1}`, `L := L_{q+1} = S_{q+1}/I^{(2)}_{q+1}`, `π_L := cokernel.π`,
`js := jetSection U (q+1)` with inverse `σ := jetSectionInv` on `grading ε r (q+1)`.

* `jetLinearPiece.coeffSection q U b := σ(d_q b) ∈ Γ(U, S_{q+1})` and `jetLinearPiece.coeffDerivationFun q U b := π_L(σ(d_q b)) ∈ Γ(U, L)`
  ("`[d_q b]`"); `coeffDerivationFun_eq_of_jetSection_eq`: `js x = d_q b → π_L x = [d_q b]`.
* `[d_q -]` is additive (`coeffClass_add`), `A`-linear (`coeffClass_smul`, `jetSection_smul`), kills `1` (`coeffClass_one`) and
  satisfies Leibniz for the `B`-module structure of `Γ(U, L)` through `ε` (`Module.compHom`): by
  `coeffClass_mul_sub_mem_irrPow`, `d_q(bb') − (ε(b) d_q b' + ε(b') d_q b) ∈ (J_+)² ∩ J_{q+1}`, and such chart readings die in
  `Γ(U, L)` (`cokernel_π_app_eq_zero_of_jetSection_mem_irrPow`). Packaged as `jetLinearPiece.coeffDerivation : Derivation A B Γ(U, L)`,
  where `B` is an `A`-algebra through `Z.hom.appLE U (π⁻¹U) le_rfl` (the structure `Omega_appIso` uses; it equals the one of
  `relativeJetScheme.sectionsAlgebra` by `Scheme.Hom.appLE_eq_app`).
* Kähler universal property (Stacks 00RM): `D̄ := coeffDerivation.liftKaehlerDifferential : Ω[B⁄A] →ₗ[B] Γ(U, L)`;
  Stacks 01UT (`Omega_appIso`): `Γ(π⁻¹U, Ω_{Z/C}) ≃ₗ[B] Ω[B⁄A]`, `d_{π⁻¹U} b ↦ D b`; together a `B`-linear
  `g : Γ(π⁻¹U, Ω_{Z/C}) → Γ(U, L)` with `g (d b) = [d_q b]` (`jetLinearPiece.omegaSectionsToLinearPiece`).
* Stacks 01I9 (`isIso_transpose_pullbackSectionsNative`): the transpose `Φ : A ⊗_B Γ(π⁻¹U, Ω_{Z/C}) → Γ(U, sec^*Ω_{Z/C})`,
  `a ⊗ ω ↦ a · (ω|_sec)`, is an isomorphism of `A`-modules; `θ_U := (extension of g to A ⊗_B -) ∘ Φ⁻¹`
  (`jetLinearPiece.coeffMap`), and `θ_U ((db)|_sec) = θ_U (Φ(1 ⊗ db)) = g (db) = [d_q b]` (`coeffMap_omegaSection`).
* `jetLinearPiece.coeffMap_char`: the characterisation in the form of `IsCoefficientHom`: `js x = d_q b → θ_U ((db)|_sec) = π_L x`.

Source: §2 of the paper, eq. (2.7) (the linear part of the `(q+1)`-st jet coefficient is a derivation);
Stacks 00RM, 01UT, 01I9. Edge cases: `U = ⊥` (all zero); `q = 0` (`I^{(2)}_1 = 0`, Leibniz is exact); `r = 0` (no `q`).

Naturality of `θ_U` in `U` is in `JetLinearPiece_Naturality`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-- **Leibniz modulo decomposables** in the based jet algebra `J_r(B, ε)`: for `q < r`,
`D_{q+1}(b b') - (ε(b) D_{q+1} b' + ε(b') D_{q+1} b) ∈ I^{(2)}_{q+1} = (J_+)² ∩ J_{q+1}`
(`ReesAlgebra.irrPow (BasedJetAlgebra.grading ε r) 2 (q+1)`).

Proof: `coeffClass_mul` gives `D_{q+1}(bb') = Σ_{i+j=q+1} D_i b · D_j b'`; the terms `(0, q+1)` and `(q+1, 0)` are
`ε(b) D_{q+1} b'` and `ε(b') D_{q+1} b` (`coeffClass_zero_order`, `D_0 = ε`), and every other term has `i, j ≥ 1`,
so `D_i b ∈ J_i ⊆ J_+` and `D_j b' ∈ J_j ⊆ J_+` (`coeffClass_mem_grading`, `HomogeneousIdeal.mem_irrelevant_of_mem`),
whence `D_i b · D_j b' ∈ (J_+)² ∩ J_{q+1}` (`ReesAlgebra.irrPow_mul`). Source: §2 of the paper, eq. (2.7)
(the linear part of the jet coordinates). (`coeffClass_mul_sub_mem_irrPow` in
`DeformedJetAlgebraFiberAtZero_LinearPieceDual` is an alias.) -/
theorem BasedJetAlgebra.coeffClass_mul_sub_mem_irrPow_two {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r q : ℕ) (hq : q < r) (b b' : B) :
    BasedJetAlgebra.coeffClass ε r (q + 1) (b * b') -
      (algebraMap R (BasedJetAlgebra ε r) (ε b) * BasedJetAlgebra.coeffClass ε r (q + 1) b' +
        algebraMap R (BasedJetAlgebra ε r) (ε b') * BasedJetAlgebra.coeffClass ε r (q + 1) b) ∈
      ReesAlgebra.irrPow (BasedJetAlgebra.grading ε r) 2 (q + 1) := by
  classical
  have hn : q + 1 ≤ r := hq
  set t : ℕ × ℕ → BasedJetAlgebra ε r := fun ij =>
    BasedJetAlgebra.coeffClass ε r ij.1 b * BasedJetAlgebra.coeffClass ε r ij.2 b' with ht
  have hsum : BasedJetAlgebra.coeffClass ε r (q + 1) (b * b') =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q + 1), t ij :=
    BasedJetAlgebra.coeffClass_mul ε r (q + 1) hn b b'
  have h0 : ∀ c : B, BasedJetAlgebra.coeffClass ε r 0 c = algebraMap R (BasedJetAlgebra ε r) (ε c) := by
    intro c
    rw [BasedJetAlgebra.coeffClass_zero_order]
    rfl
  have hmem1 : ((0, q + 1) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q + 1) := by
    rw [Finset.mem_antidiagonal]
    simp
  have hmem2 : ((q + 1, 0) : ℕ × ℕ) ∈
      (Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q + 1)).erase (0, q + 1) := by
    rw [Finset.mem_erase, Finset.mem_antidiagonal]
    exact ⟨fun h => by simp at h, by simp⟩
  have hsplit : ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q + 1), t ij =
      (∑ ij ∈ ((Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q + 1)).erase (0, q + 1)).erase (q + 1, 0),
          t ij) + t (q + 1, 0) + t (0, q + 1) := by
    rw [Finset.sum_erase_add _ _ hmem2, Finset.sum_erase_add _ _ hmem1]
  have hrest : ∑ ij ∈ ((Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q + 1)).erase (0, q + 1)).erase
      (q + 1, 0), t ij ∈ ReesAlgebra.irrPow (BasedJetAlgebra.grading ε r) 2 (q + 1) := by
    refine Submodule.sum_mem _ fun ij hij => ?_
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_antidiagonal] at hij
    obtain ⟨h1, h2, h3⟩ := hij
    have hi : 0 < ij.1 := by
      rcases Nat.eq_zero_or_pos ij.1 with h | h
      · exact absurd (Prod.ext h (by omega)) h2
      · exact h
    have hj : 0 < ij.2 := by
      rcases Nat.eq_zero_or_pos ij.2 with h | h
      · exact absurd (Prod.ext (by omega) h) h1
      · exact h
    have hx : BasedJetAlgebra.coeffClass ε r ij.1 b ∈
        ReesAlgebra.irrPow (BasedJetAlgebra.grading ε r) 1 ij.1 :=
      ⟨by
        rw [pow_one]
        exact HomogeneousIdeal.mem_irrelevant_of_mem _ hi (BasedJetAlgebra.coeffClass_mem_grading ε r ij.1 b),
        BasedJetAlgebra.coeffClass_mem_grading ε r ij.1 b⟩
    have hy : BasedJetAlgebra.coeffClass ε r ij.2 b' ∈
        ReesAlgebra.irrPow (BasedJetAlgebra.grading ε r) 1 ij.2 :=
      ⟨by
        rw [pow_one]
        exact HomogeneousIdeal.mem_irrelevant_of_mem _ hj (BasedJetAlgebra.coeffClass_mem_grading ε r ij.2 b'),
        BasedJetAlgebra.coeffClass_mem_grading ε r ij.2 b'⟩
    have := ReesAlgebra.irrPow_mul (BasedJetAlgebra.grading ε r) hx hy
    rw [h3] at this
    exact this
  have heq : BasedJetAlgebra.coeffClass ε r (q + 1) (b * b') -
      (algebraMap R (BasedJetAlgebra ε r) (ε b) * BasedJetAlgebra.coeffClass ε r (q + 1) b' +
        algebraMap R (BasedJetAlgebra ε r) (ε b') * BasedJetAlgebra.coeffClass ε r (q + 1) b) =
      ∑ ij ∈ ((Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q + 1)).erase (0, q + 1)).erase (q + 1, 0),
        t ij := by
    rw [hsum, hsplit]
    simp only [ht, h0]
    ring
  rw [heq]
  exact hrest

/-- The transpose `S ⊗_R X → Y` of an `R`-linear map `g : X → Y` sends `1 ⊗ x` to `g x`
(`extendRestrictScalarsAdj_homEquiv_apply` read backwards). -/
theorem ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_apply_one_tmul {R : Type u} {S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) {X : ModuleCat.{u} R} {Y : ModuleCat.{u} S}
    (g : X ⟶ (ModuleCat.restrictScalars f).obj Y) (x : X) :
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv X Y).symm g) ((1 : S) ⊗ₜ[R] x) = g x := by
  have h := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply (f := f)
    (((ModuleCat.extendRestrictScalarsAdj f).homEquiv X Y).symm g) x
  have h2 : ((ModuleCat.extendRestrictScalarsAdj f).homEquiv X Y)
      (((ModuleCat.extendRestrictScalarsAdj f).homEquiv X Y).symm g) = g := Equiv.apply_symm_apply _ _
  rw [h2] at h
  exact h.symm

section CoefficientHom

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (r : ℕ)

namespace jetLinearPiece

variable (U : C.toScheme.affineOpens)

/-! ## `σ`: the inverse of the chart reading on `grading ε r m` -/

/-- A chosen section of `S_m` over `U` with prescribed chart reading `z ∈ grading ε_U r m` (`exists_jetSection_eq`). -/
def jetSectionInv (m : ℕ)
    (z : letI := relativeJetScheme.sectionsAlgebra Z U.1
      BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r)
    (hz : letI := relativeJetScheme.sectionsAlgebra Z U.1
      z ∈ BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r m) :
    Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1) :=
  Classical.choose (exists_jetSection_eq Z sec hs r U m z hz)

theorem jetSection_jetSectionInv (m : ℕ)
    (z : letI := relativeJetScheme.sectionsAlgebra Z U.1
      BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r)
    (hz : letI := relativeJetScheme.sectionsAlgebra Z U.1
      z ∈ BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r m) :
    jetSection Z sec hs r U m (jetSectionInv Z sec hs r U m z hz) = z :=
  Classical.choose_spec (exists_jetSection_eq Z sec hs r U m z hz)

theorem eq_jetSectionInv_of_jetSection_eq (m : ℕ)
    (z : letI := relativeJetScheme.sectionsAlgebra Z U.1
      BasedJetAlgebra (relativeJetScheme.augmentation Z sec hs U.1) r)
    (hz : letI := relativeJetScheme.sectionsAlgebra Z U.1
      z ∈ BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r m)
    (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part m, U.1)) (hx : jetSection Z sec hs r U m x = z) :
    x = jetSectionInv Z sec hs r U m z hz :=
  jetSection_injective Z sec hs r U m (hx.trans (jetSection_jetSectionInv Z sec hs r U m z hz).symm)

/-! ## The coefficient derivation `b ↦ [d_q b]` -/

variable (q : Fin r)

/-- `σ(d_q b) ∈ Γ(U, S_{q+1})`: the section whose chart reading is the `(q+1)`-st jet coefficient of `b`. -/
def coeffSection (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1), U.1) :=
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  jetSectionInv Z sec hs r U (q.1 + 1)
    (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z sec hs U.1) r (q.1 + 1) b)
    (BasedJetAlgebra.coeffClass_mem_grading _ r (q.1 + 1) b)

theorem jetSection_coeffSection (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    jetSection Z sec hs r U (q.1 + 1) (coeffSection Z sec hs r U q b) =
      BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z sec hs U.1) r (q.1 + 1) b :=
  jetSection_jetSectionInv Z sec hs r U (q.1 + 1) _ _

/-- `[d_q b] := π_L(σ(d_q b)) ∈ Γ(U, L_{q+1})`. -/
def coeffDerivationFun (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1) :=
  ((CategoryTheory.Limits.cokernel.π ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom
    (coeffSection Z sec hs r U q b)

/-- Any section reading as `d_q b` in the chart has class `[d_q b]`. -/
theorem coeffDerivationFun_eq_of_jetSection_eq (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
    (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1), U.1))
    (hx : letI := relativeJetScheme.sectionsAlgebra Z U.1
      jetSection Z sec hs r U (q.1 + 1) x =
        BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z sec hs U.1) r (q.1 + 1) b) :
    ((CategoryTheory.Limits.cokernel.π
      ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom x =
      coeffDerivationFun Z sec hs r U q b :=
  congrArg _ (eq_jetSectionInv_of_jetSection_eq Z sec hs r U (q.1 + 1) _ _ x hx)

theorem coeffDerivationFun_add (b b' : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    coeffDerivationFun Z sec hs r U q (b + b') =
      coeffDerivationFun Z sec hs r U q b + coeffDerivationFun Z sec hs r U q b' := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have h := coeffDerivationFun_eq_of_jetSection_eq Z sec hs r U q (b + b')
    (coeffSection Z sec hs r U q b + coeffSection Z sec hs r U q b') (by
      rw [jetSection_add, jetSection_coeffSection, jetSection_coeffSection,
        BasedJetAlgebra.coeffClass_add _ r (q.1 + 1) q.2 b b'])
  rw [← h, map_add]
  rfl

theorem coeffDerivationFun_smul (a : Γ(C.toScheme, U.1)) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    coeffDerivationFun Z sec hs r U q (((Z.hom.app U.1).hom a) * b) =
      a • coeffDerivationFun Z sec hs r U q b := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have h2 : ((Z.hom.app U.1).hom a) * b = a • b := rfl
  have h := coeffDerivationFun_eq_of_jetSection_eq Z sec hs r U q (((Z.hom.app U.1).hom a) * b)
    (a • coeffSection Z sec hs r U q b) (by
      rw [jetSection_smul, jetSection_coeffSection, h2, BasedJetAlgebra.coeffClass_smul _ r (q.1 + 1) q.2 a b]
      rfl)
  rw [← h, AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
  rfl

theorem coeffDerivationFun_one : coeffDerivationFun Z sec hs r U q 1 = 0 := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have h := coeffDerivationFun_eq_of_jetSection_eq Z sec hs r U q 1 0 (by
    rw [jetSection_zero, BasedJetAlgebra.coeffClass_one _ r (q.1 + 1) q.2, if_neg (Nat.succ_ne_zero _)])
  rw [← h, map_zero]

/-- **Leibniz modulo decomposables** for `[d_q -]`: `[d_q(bb')] = ε(b) • [d_q b'] + ε(b') • [d_q b]`. -/
theorem coeffDerivationFun_mul (b b' : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    coeffDerivationFun Z sec hs r U q (b * b') =
      relativeJetScheme.augmentation Z sec hs U.1 b • coeffDerivationFun Z sec hs r U q b' +
        relativeJetScheme.augmentation Z sec hs U.1 b' • coeffDerivationFun Z sec hs r U q b := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  have hmem : jetSection Z sec hs r U (q.1 + 1)
      (coeffSection Z sec hs r U q (b * b') -
        (relativeJetScheme.augmentation Z sec hs U.1 b • coeffSection Z sec hs r U q b' +
          relativeJetScheme.augmentation Z sec hs U.1 b' • coeffSection Z sec hs r U q b)) ∈
      ReesAlgebra.irrPow (BasedJetAlgebra.grading (relativeJetScheme.augmentation Z sec hs U.1) r) 2 (q.1 + 1) := by
    have hsub := map_sub (jetSectionLin Z sec hs r U (q.1 + 1)) (coeffSection Z sec hs r U q (b * b'))
      (relativeJetScheme.augmentation Z sec hs U.1 b • coeffSection Z sec hs r U q b' +
        relativeJetScheme.augmentation Z sec hs U.1 b' • coeffSection Z sec hs r U q b)
    simp only [jetSectionLin_apply] at hsub
    rw [hsub, jetSection_add, jetSection_smul, jetSection_smul, jetSection_coeffSection,
      jetSection_coeffSection, jetSection_coeffSection]
    exact BasedJetAlgebra.coeffClass_mul_sub_mem_irrPow_two _ r q.1 q.2 b b'
  have h0 := cokernel_π_app_eq_zero_of_jetSection_mem_irrPow Z sec hs r q U _ hmem
  have h1 : ((CategoryTheory.Limits.cokernel.π
      ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom
        (coeffSection Z sec hs r U q (b * b')) =
      ((CategoryTheory.Limits.cokernel.π
        ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom
        (relativeJetScheme.augmentation Z sec hs U.1 b • coeffSection Z sec hs r U q b' +
          relativeJetScheme.augmentation Z sec hs U.1 b' • coeffSection Z sec hs r U q b) :=
    sub_eq_zero.mp ((map_sub _ _ _).symm.trans h0)
  show ((CategoryTheory.Limits.cokernel.π
      ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom
        (coeffSection Z sec hs r U q (b * b')) = _
  rw [h1, map_add, AlgebraicGeometry.Scheme.Modules.Hom.app_smul, AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
  rfl

/-! ## The derivation and the local coefficient map -/

/-- The `A`-algebra structure on `B = Γ(Z, π⁻¹U)` used by `Omega_appIso` (through `Z.hom.appLE U (π⁻¹U) le_rfl`); it is
the one of `relativeJetScheme.sectionsAlgebra` (`appLE_eq_app`). -/
abbrev chartAlgebra : Algebra Γ(C.toScheme, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1) :=
  (Z.hom.appLE U.1 (Z.hom ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra

theorem chartAlgebra_algebraMap (a : Γ(C.toScheme, U.1)) :
    letI := chartAlgebra Z U
    algebraMap Γ(C.toScheme, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1) a = (Z.hom.app U.1).hom a := by
  show (Z.hom.appLE U.1 (Z.hom ⁻¹ᵁ U.1) le_rfl).hom a = (Z.hom.app U.1).hom a
  rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app]

/-- The augmentation `ε = sec^♯ : B → A` as a ring homomorphism (the underlying ring homomorphism of
`relativeJetScheme.augmentation`). -/
abbrev augRingHom : Γ(Z.left, Z.hom ⁻¹ᵁ U.1) →+* Γ(C.toScheme, U.1) :=
  (sec.appLE (Z.hom ⁻¹ᵁ U.1) U.1 (relativeJetScheme.section_preimage_le Z sec hs U.1)).hom

theorem augRingHom_app (a : Γ(C.toScheme, U.1)) : augRingHom Z sec hs U ((Z.hom.app U.1).hom a) = a :=
  relativeJetScheme.augmentation_commutes Z sec hs U.1 a

/-- The `B`-module structure of `Γ(U, L_{q+1})` through `ε`. -/
abbrev linearPieceModuleB :
    Module Γ(Z.left, Z.hom ⁻¹ᵁ U.1)
      Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1) :=
  Module.compHom _ (augRingHom Z sec hs U)

theorem linearPieceModuleB_smul (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
    (m : Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1)) :
    letI := linearPieceModuleB Z sec hs r U q
    b • m = augRingHom Z sec hs U b • m := rfl

theorem linearPieceIsScalarTower :
    letI := chartAlgebra Z U
    letI := linearPieceModuleB Z sec hs r U q
    IsScalarTower Γ(C.toScheme, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1)
      Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1) := by
  letI := chartAlgebra Z U
  letI := linearPieceModuleB Z sec hs r U q
  refine IsScalarTower.of_algebraMap_smul fun a m => ?_
  show augRingHom Z sec hs U (algebraMap Γ(C.toScheme, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1) a) • m = a • m
  rw [chartAlgebra_algebraMap, augRingHom_app]

/-- **The coefficient derivation** `b ↦ [d_q b]`, an `A`-derivation `B → Γ(U, L_{q+1})`. -/
def coeffDerivation :
    letI := chartAlgebra Z U
    letI := linearPieceModuleB Z sec hs r U q
    Derivation Γ(C.toScheme, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1)
      Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1) :=
  letI := chartAlgebra Z U
  letI := linearPieceModuleB Z sec hs r U q
  { toFun := coeffDerivationFun Z sec hs r U q
    map_add' := coeffDerivationFun_add Z sec hs r U q
    map_smul' := fun a b => by
      have h : a • b = ((Z.hom.app U.1).hom a) * b := by
        rw [Algebra.smul_def, chartAlgebra_algebraMap]
      rw [RingHom.id_apply, h]
      exact coeffDerivationFun_smul Z sec hs r U q a b
    map_one_eq_zero' := coeffDerivationFun_one Z sec hs r U q
    leibniz' := fun b b' => coeffDerivationFun_mul Z sec hs r U q b b' }

theorem coeffDerivation_toLinearMap_apply (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI := chartAlgebra Z U
    letI := linearPieceModuleB Z sec hs r U q
    (coeffDerivation Z sec hs r U q).toLinearMap b = coeffDerivationFun Z sec hs r U q b := rfl

theorem coeffDerivation_apply (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI := chartAlgebra Z U
    letI := linearPieceModuleB Z sec hs r U q
    coeffDerivation Z sec hs r U q b = coeffDerivationFun Z sec hs r U q b := by
  letI := chartAlgebra Z U
  letI := linearPieceModuleB Z sec hs r U q
  exact coeffDerivation_toLinearMap_apply Z sec hs r U q b

/-- `Γ(π⁻¹U, Ω_{Z/C}) → Γ(U, L_{q+1})`, `B`-linear, `d_{π⁻¹U} b ↦ [d_q b]`: the Kähler lift of the coefficient derivation
composed with `Omega_appIso` (01UT). -/
def omegaSectionsToLinearPiece :
    letI := linearPieceModuleB Z sec hs r U q
    Γ(AlgebraicGeometry.Omega Z.hom, Z.hom ⁻¹ᵁ U.1) →ₗ[Γ(Z.left, Z.hom ⁻¹ᵁ U.1)]
      Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1) :=
  letI := chartAlgebra Z U
  letI := linearPieceModuleB Z sec hs r U q
  haveI := linearPieceIsScalarTower Z sec hs r U q
  (coeffDerivation Z sec hs r U q).liftKaehlerDifferential ∘ₗ
    (AlgebraicGeometry.Omega_appIso Z.hom U.2 (U.2.preimage Z.hom) le_rfl).toLinearMap

theorem omegaSectionsToLinearPiece_d (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    omegaSectionsToLinearPiece Z sec hs r U q
        ((AlgebraicGeometry.Omega.universalDerivation Z.hom).d (X := Opposite.op (Z.hom ⁻¹ᵁ U.1)) b) =
      coeffDerivationFun Z sec hs r U q b := by
  letI := chartAlgebra Z U
  letI := linearPieceModuleB Z sec hs r U q
  haveI := linearPieceIsScalarTower Z sec hs r U q
  show (coeffDerivation Z sec hs r U q).liftKaehlerDifferential
    (AlgebraicGeometry.Omega_appIso Z.hom U.2 (U.2.preimage Z.hom) le_rfl
      ((AlgebraicGeometry.Omega.universalDerivation Z.hom).d (X := Opposite.op (Z.hom ⁻¹ᵁ U.1)) b)) = _
  have h := AlgebraicGeometry.Omega_appIso_d Z.hom U.2 (U.2.preimage Z.hom) le_rfl b
  exact (congrArg (coeffDerivation Z sec hs r U q).liftKaehlerDifferential h).trans
    (((coeffDerivation Z sec hs r U q).liftKaehlerDifferential_comp_D b).trans
      (coeffDerivation_apply Z sec hs r U q b))

/-- The transpose `Φ : A ⊗_B Γ(π⁻¹U, Ω_{Z/C}) → Γ(U, sec^*Ω_{Z/C})`, `a ⊗ ω ↦ a • (ω|_sec)` (in `ModuleCat A`); an isomorphism by
Stacks 01I9 (`isIso_transpose_pullbackSectionsNative`, `baseChangeHom_isIso` — a theorem, supplied by `haveI` where needed;
no global instance). -/
def baseChangeHom :
    (ModuleCat.extendScalars (augRingHom Z sec hs U)).obj
        (ModuleCat.of Γ(Z.left, Z.hom ⁻¹ᵁ U.1) Γ(AlgebraicGeometry.Omega Z.hom, Z.hom ⁻¹ᵁ U.1)) ⟶
      ModuleCat.of Γ(C.toScheme, U.1)
        Γ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom), U.1) :=
  ((ModuleCat.extendRestrictScalarsAdj (augRingHom Z sec hs U)).homEquiv _ _).symm
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsNative sec (AlgebraicGeometry.Omega Z.hom) (Z.hom ⁻¹ᵁ U.1) U.1
      (relativeJetScheme.section_preimage_le Z sec hs U.1))

theorem baseChangeHom_isIso : IsIso (baseChangeHom Z sec hs U) := by
  haveI := AlgebraicGeometry.Omega_isQuasicoherent Z.hom
  exact AlgebraicGeometry.Scheme.Modules.isIso_transpose_pullbackSectionsNative sec (AlgebraicGeometry.Omega Z.hom)
    (Z.hom ⁻¹ᵁ U.1) (U.2.preimage Z.hom) U.1 U.2 (relativeJetScheme.section_preimage_le Z sec hs U.1)

theorem baseChangeHom_one_tmul (ω : Γ(AlgebraicGeometry.Omega Z.hom, Z.hom ⁻¹ᵁ U.1)) :
    (baseChangeHom Z sec hs U).hom ((1 : Γ(C.toScheme, U.1)) ⊗ₜ[Γ(Z.left, Z.hom ⁻¹ᵁ U.1)] ω) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn sec (AlgebraicGeometry.Omega Z.hom) (Z.hom ⁻¹ᵁ U.1) U.1
        (relativeJetScheme.section_preimage_le Z sec hs U.1) ω := by
  exact ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_apply_one_tmul (augRingHom Z sec hs U) _ ω

/-- The extension of `omegaSectionsToLinearPiece` to `A ⊗_B Γ(π⁻¹U, Ω_{Z/C})` (in `ModuleCat A`). -/
def baseChangeToLinearPiece :
    (ModuleCat.extendScalars (augRingHom Z sec hs U)).obj
        (ModuleCat.of Γ(Z.left, Z.hom ⁻¹ᵁ U.1) Γ(AlgebraicGeometry.Omega Z.hom, Z.hom ⁻¹ᵁ U.1)) ⟶
      ModuleCat.of Γ(C.toScheme, U.1)
        Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1) :=
  ((ModuleCat.extendRestrictScalarsAdj (augRingHom Z sec hs U)).homEquiv _ _).symm
    (ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (augRingHom Z sec hs U)).obj (ModuleCat.of Γ(C.toScheme, U.1)
        Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1)))
      (omegaSectionsToLinearPiece Z sec hs r U q))

theorem baseChangeToLinearPiece_one_tmul (ω : Γ(AlgebraicGeometry.Omega Z.hom, Z.hom ⁻¹ᵁ U.1)) :
    (baseChangeToLinearPiece Z sec hs r U q).hom ((1 : Γ(C.toScheme, U.1)) ⊗ₜ[Γ(Z.left, Z.hom ⁻¹ᵁ U.1)] ω) =
      omegaSectionsToLinearPiece Z sec hs r U q ω := by
  exact ModuleCat.extendRestrictScalarsAdj_homEquiv_symm_apply_one_tmul (augRingHom Z sec hs U) _ ω

/-- **The local coefficient map** `θ_U : Γ(U, sec^*Ω_{Z/C}) →ₗ[A] Γ(U, L_{q+1})`, `(db)|_sec ↦ [d_q b]`. -/
def coeffMap :
    Γ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom), U.1) →ₗ[Γ(C.toScheme, U.1)]
      Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1) :=
  haveI := baseChangeHom_isIso Z sec hs U
  (CategoryTheory.inv (baseChangeHom Z sec hs U) ≫ baseChangeToLinearPiece Z sec hs r U q).hom

theorem coeffMap_omegaSection (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    coeffMap Z sec hs r U q (omegaSection Z sec hs U.1 b) = coeffDerivationFun Z sec hs r U q b := by
  haveI := baseChangeHom_isIso Z sec hs U
  have h1 : omegaSection Z sec hs U.1 b = (baseChangeHom Z sec hs U).hom
      ((1 : Γ(C.toScheme, U.1)) ⊗ₜ[Γ(Z.left, Z.hom ⁻¹ᵁ U.1)]
        (AlgebraicGeometry.Omega.universalDerivation Z.hom).d (X := Opposite.op (Z.hom ⁻¹ᵁ U.1)) b) :=
    (baseChangeHom_one_tmul Z sec hs U _).symm
  rw [h1]
  have h2 := congrArg (fun φ => φ.hom ((1 : Γ(C.toScheme, U.1)) ⊗ₜ[Γ(Z.left, Z.hom ⁻¹ᵁ U.1)]
      (AlgebraicGeometry.Omega.universalDerivation Z.hom).d (X := Opposite.op (Z.hom ⁻¹ᵁ U.1)) b))
    (CategoryTheory.IsIso.hom_inv_id_assoc (baseChangeHom Z sec hs U) (baseChangeToLinearPiece Z sec hs r U q))
  exact h2.trans ((baseChangeToLinearPiece_one_tmul Z sec hs r U q _).trans
    (omegaSectionsToLinearPiece_d Z sec hs r U q b))

/-- **The characterisation** in the form used by `IsCoefficientHom`: if `x ∈ Γ(U, S_{q+1})` reads as `d_q b`, then
`θ_U ((db)|_sec) = π_L x`. -/
theorem coeffMap_char (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
    (x : Γ((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1), U.1))
    (hx : letI := relativeJetScheme.sectionsAlgebra Z U.1
      jetSection Z sec hs r U (q.1 + 1) x =
        BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z sec hs U.1) r (q.1 + 1) b) :
    coeffMap Z sec hs r U q (omegaSection Z sec hs U.1 b) =
      ((CategoryTheory.Limits.cokernel.π
        ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom x := by
  rw [coeffMap_omegaSection, coeffDerivationFun_eq_of_jetSection_eq Z sec hs r U q b x hx]

end jetLinearPiece

end CoefficientHom

end
