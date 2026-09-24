import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_Construction
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentAffineLocal
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualCoevZigzag
import MiyaokaMori.RingTheory.GradedRing.ReesAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradingSubmodule
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.BiproductSections
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsHomBijectiveAffine

/-! # Sections of the irrelevant-ideal powers on an affine open (sheaf ↔ ring)

Proves both directions of `irrelevantPow_app_range_iff` (`DeformedJetAlgebraLocallyWeightedPolynomial`):
for `U` affine, `x ∈ Γ(U, S_j)` is in the image of `Γ(U, I^{(p)}_j) → Γ(U, S_j)` iff `of_j x ∈ (S(U)_+)^p ∩ S(U)_j`.

* §1 pure algebra (`ReesAlgebra.irrPow_succ_le`): for a graded ring `𝒜` and a family of additive subgroups `N j` with
  `𝒜_d · (𝒜₊^p ∩ 𝒜_e) ⊆ N (d+e)` for all `d ≥ 1`, one has `𝒜₊^{p+1} ∩ 𝒜_j ⊆ N j`. Proof: `𝒜₊^{p+1} = 𝒜₊ · 𝒜₊^p`
  (`pow_succ'`); for a product `a · b` the degree-`j` component is `Σ_{d+e=j} a_d b_e` (`decompose_mul`,
  `coe_mul_apply_eq_sum_antidiagonal`), `a_0 = 0` since `a ∈ 𝒜₊`, and `b_e ∈ 𝒜₊^p` since `𝒜₊^p` is a homogeneous ideal
  (`Ideal.IsHomogeneous.mul` inductively); sums by `Submodule.mul_induction_on`; finally `x = x_j` for `x ∈ 𝒜_j`.
* §2 (⇒) `ofPiece_irrelevantPow_app_mem_irrPow`: induction on `p`; for `p+1`, `I^{(p+1)}_j = Im(gen)`, sections of the
  image over affine `U` are the image of sections (`gammaAffine_exact_iff` on `⊕ → Im → 0`), sections of the biproduct are
  sums of components (`biproduct_sections_total`), sections of `S_{a+1} ⊗ I^{(p)}_m` over affine `U` are sums of
  `tensorSections` (`tensorSectionsHom_app_bijective_of_isAffineOpen`, surjectivity half), and on `tensorSections s t`
  the generator is
  `of_{a+1} s · of_m (ι_p t)` (`ι_gen`, `whiskerLeft_app_tensorSections'`, `mk_eqToHom_app`, `of_mul_of`), a product of an
  element of `𝒜₊` and an element of `𝒜₊^p` (induction hypothesis).
* §3 (⇐) `exists_irrelevantPow_app_eq_of_mem_irrPow`: induction on `p`; for `p+1` apply §1 to
  `N n := of_n '' range Γ(U, ι_{p+1,n})`: for `a = of_d s` (`d ≥ 1`) and `b ∈ 𝒜₊^p ∩ 𝒜_e`, `b = of_e (ι_p t)` by the induction
  hypothesis, and `a · b = of_{d+e} (((S_d ◁ ι_p) ≫ mul).app U (tensorSections s t))`, where `(S_d ◁ ι_p) ≫ mul` factors
  through `ι_{p+1}` (`landsIn_whiskerLeft_irrelevantPow_mul_succ`, `landsIn_iff_exists`). No affineness is needed here.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory ZeroObject

noncomputable section

/-! ## §1 Pure algebra -/

namespace ReesAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- Powers of the irrelevant ideal are homogeneous ideals. -/
theorem irrelevant_pow_isHomogeneous (p : ℕ) : (irrelevant 𝒜 ^ p).IsHomogeneous 𝒜 := by
  induction p with
  | zero => rw [pow_zero, Ideal.one_eq_top]; exact Ideal.IsHomogeneous.top 𝒜
  | succ p ih => rw [pow_succ]; exact Ideal.IsHomogeneous.mul ih (HomogeneousIdeal.irrelevant 𝒜).isHomogeneous

/-- The degree-`0` component of an element of the irrelevant ideal vanishes. -/
theorem decompose_zero_of_mem_irrelevant {a : A} (ha : a ∈ irrelevant 𝒜) :
    (DirectSum.decompose 𝒜 a 0 : A) = 0 := by
  have h := (HomogeneousIdeal.mem_irrelevant_iff 𝒜 a).1 ha
  rwa [GradedRing.proj_apply] at h

/-- **`𝒜₊^{p+1} ∩ 𝒜_j` is contained in any family `N` with `𝒜_d · (𝒜₊^p ∩ 𝒜_e) ⊆ N (d+e)` for `d ≥ 1`.** -/
theorem irrPow_succ_le (p : ℕ) (N : ℕ → AddSubgroup A)
    (hN : ∀ d e : ℕ, 0 < d → ∀ a ∈ 𝒜 d, ∀ b ∈ irrPow 𝒜 p e, a * b ∈ N (d + e)) (j : ℕ) {x : A}
    (hx : x ∈ irrPow 𝒜 (p + 1) j) : x ∈ N j := by
  obtain ⟨hx1, hx2⟩ := (mem_irrPow 𝒜).1 hx
  rw [pow_succ'] at hx1
  have hhom := irrelevant_pow_isHomogeneous 𝒜 p
  have key : ∀ z ∈ irrelevant 𝒜 * irrelevant 𝒜 ^ p, (DirectSum.decompose 𝒜 z j : A) ∈ N j := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro a ha b hb
      rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply_eq_sum_antidiagonal]
      refine AddSubgroup.sum_mem _ fun ij hij => ?_
      rcases Nat.eq_zero_or_pos ij.1 with h0 | hpos
      · rw [h0, decompose_zero_of_mem_irrelevant 𝒜 ha, zero_mul]
        exact zero_mem _
      · rw [← Finset.mem_antidiagonal.1 hij]
        exact hN _ _ hpos _ (DirectSum.decompose 𝒜 a ij.1).2 _
          ⟨hhom ij.2 hb, (DirectSum.decompose 𝒜 b ij.2).2⟩
    · intro x y hx hy
      rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add]
      exact add_mem hx hy
  have := key x hx1
  rwa [DirectSum.decompose_of_mem_same 𝒜 hx2] at this

end ReesAlgebra

/-! ## §2, §3 Sheaf ↔ ring -/

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- `ofPiece` turns graded multiplication into ring multiplication (local copy of `ofPiece_sectionsGMul`). -/
private theorem ofPiece_sectionsGMul_lwp (U : X.Opens) {m n : ℕ} (a : S.sectionsPiece U m) (b : S.sectionsPiece U n) :
    S.ofPiece U (m + n) (S.sectionsGMul U a b) = S.ofPiece U m a * S.ofPiece U n b :=
  (DirectSum.of_mul_of (A := S.sectionsPiece U) a b).symm

/-- `ofPiece` is compatible with `eqToHom` index transport. -/
private theorem ofPiece_eqToHom_app (U : X.Opens) {m n : ℕ} (e : m = n) (x : S.sectionsPiece U m) :
    S.ofPiece U n ((CategoryTheory.eqToHom (congrArg S.part e)).app U x) = S.ofPiece U m x :=
  DirectSum.of_eq_of_gradedMonoid_eq (S.mk_eqToHom_app U e x)

/-- `(S_d ◁ ι) ≫ mul` on a pure tensor section is the graded product with `ι t`. -/
private theorem whiskerLeft_comp_mul_app_tensorSections (U : X.Opens) {A : X.Modules} {d m : ℕ} (f : A ⟶ S.part m)
    (s : Γ(S.part d, U)) (t : Γ(A, U)) :
    ((S.part d ◁ f) ≫ S.mul d m).app U (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part d) A U s t) =
      S.sectionsGMul U s (f.app U t) := by
  show (S.mul d m).app U ((S.part d ◁ f).app U _) = _
  rw [AlgebraicGeometry.Scheme.Modules.DualZigzag.whiskerLeft_app_tensorSections']
  rfl

/-- **(a4, ⇒)** On an affine open, the image of `Γ(U, I^{(p)}_j) → Γ(U, S_j)`, placed in the section ring, lies in
`(S(U)_+)^p ∩ S(U)_j`. Uses `tensorSectionsHom_app_bijective_of_isAffineOpen` (surjectivity half). -/
theorem ofPiece_irrelevantPow_app_mem_irrPow (U : X.AffineZariskiSite) :
    ∀ (p j : ℕ) (y : Γ((S.irrelevantPow p j).1, U.toOpens)),
      (S.ofPiece U.toOpens j ((S.irrelevantPow p j).2.app U.toOpens y) :
          S.toGradedAffineAlgebra.toAffineAlgebra.sections U) ∈
        ReesAlgebra.irrPow (S.toGradedAffineAlgebra.gradingSubmodule U) p j
  | 0, j, y => by
    rw [ReesAlgebra.irrPow_zero]
    exact ⟨y, rfl⟩
  | p + 1, j, y => by
    classical
    set g := irrelevantPow.gen S p j with hg
    -- sections of the image are the image of sections (exactness of `Γ(U, ·)` on quasi-coherent modules)
    have hsurj : Function.Surjective ((CategoryTheory.Limits.factorThruImage g).app U.toOpens) := by
      have hqc1 : (CategoryTheory.Limits.biproduct
          (fun a : Fin j => S.part (a.1 + 1) ⊗ (S.irrelevantPow p (j - (a.1 + 1))).1)).IsQuasicoherent := by
        refine AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct _ fun a => ?_
        have := S.irrelevantPow_isQuasicoherent p (j - (a.1 + 1))
        have := S.quasicoherent (a.1 + 1)
        exact AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj _ _
      have hqc2 : (CategoryTheory.Limits.image g).IsQuasicoherent := S.irrelevantPow_isQuasicoherent (p + 1) j
      have hqc3 : (0 : X.Modules).IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.isQuasicoherent_zero _
      let C : CategoryTheory.ShortComplex X.Modules :=
        CategoryTheory.ShortComplex.mk (CategoryTheory.Limits.factorThruImage g)
          (0 : CategoryTheory.Limits.image g ⟶ 0) CategoryTheory.Limits.comp_zero
      have hC : C.Exact := (CategoryTheory.ShortComplex.exact_iff_epi C rfl).mpr inferInstance
      have hex := (AlgebraicGeometry.Scheme.Modules.gammaAffine_exact_iff C).mp hC ⟨U.toOpens, U.2⟩
      intro y
      have h0 : (C.g.app U.toOpens).hom y = 0 := by
        show ((0 : CategoryTheory.Limits.image g ⟶ 0).app U.toOpens).hom y = 0
        rw [AlgebraicGeometry.Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply]
      obtain ⟨x, hx⟩ := (hex y).mp h0
      exact ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := hsurj y
    have hfac : (S.irrelevantPow (p + 1) j).2.app U.toOpens ((CategoryTheory.Limits.factorThruImage g).app U.toOpens z) =
        g.app U.toOpens z :=
      congrArg (fun ψ : _ ⟶ S.part j => ψ.app U.toOpens z) (CategoryTheory.Limits.image.fac g)
    -- work in the preimage subgroup `Q ⊆ Γ(U, S_j)` of `𝒜₊^{p+1} ∩ 𝒜_j` (uniform types for rewriting)
    let Q : AddSubgroup Γ(S.part j, U.toOpens) :=
      AddSubgroup.comap (DirectSum.of (S.sectionsPiece U.toOpens) j)
        (ReesAlgebra.irrPow (S.toGradedAffineAlgebra.gradingSubmodule U) (p + 1) j).toAddSubgroup
    show (S.irrelevantPow (p + 1) j).2.app U.toOpens ((CategoryTheory.Limits.factorThruImage g).app U.toOpens z) ∈ Q
    rw [hfac]
    -- decompose `z` into its biproduct components
    rw [AlgebraicGeometry.Scheme.Modules.biproduct_sections_total _ U.toOpens z, map_sum]
    refine AddSubgroup.sum_mem _ fun a _ => ?_
    -- the `a`-th component: a section of `S_{a+1} ⊗ I^{(p)}_m`, `m = j - (a+1)`
    set za := (CategoryTheory.Limits.biproduct.π
      (fun a : Fin j => S.part (a.1 + 1) ⊗ (S.irrelevantPow p (j - (a.1 + 1))).1) a).app U.toOpens z
    have hcomp : ∀ w, g.app U.toOpens ((CategoryTheory.Limits.biproduct.ι
        (fun a : Fin j => S.part (a.1 + 1) ⊗ (S.irrelevantPow p (j - (a.1 + 1))).1) a).app U.toOpens w) =
        ((S.part (a.1 + 1) ◁ (S.irrelevantPow p (j - (a.1 + 1))).2) ≫ S.mul _ _ ≫
          CategoryTheory.eqToHom (congrArg S.part (by have := a.2; omega))).app U.toOpens w := fun w =>
      congrArg (fun ψ : _ ⟶ S.part j => ψ.app U.toOpens w) (S.ι_gen p j a)
    have hIsQc : (S.irrelevantPow p (j - (a.1 + 1))).1.IsQuasicoherent := S.irrelevantPow_isQuasicoherent _ _
    have hSqc := S.quasicoherent (a.1 + 1)
    clear_value za
    -- sections of the tensor product over the affine `U` are sums of `tensorSections` (01I8 for `⊗`)
    let F₀ : TensorProduct Γ(X, U.toOpens) Γ(S.part (a.1 + 1), U.toOpens) Γ((S.irrelevantPow p (j - (a.1 + 1))).1, U.toOpens) →+
        Γ(S.part (a.1 + 1) ⊗ (S.irrelevantPow p (j - (a.1 + 1))).1, U.toOpens) :=
      { toFun := fun t => (AlgebraicGeometry.Scheme.Modules.tensorSectionsHom (S.part (a.1 + 1))
          (S.irrelevantPow p (j - (a.1 + 1))).1).app (op U.toOpens) t
        map_zero' := map_zero _
        map_add' := fun x y => map_add _ x y }
    have hF₀ : Function.Surjective F₀ := (AlgebraicGeometry.Scheme.Modules.tensorSectionsHom_app_bijective_of_isAffineOpen
      (S.part (a.1 + 1)) (S.irrelevantPow p (j - (a.1 + 1))).1 U.2).2
    have hF₀tmul : ∀ (s : Γ(S.part (a.1 + 1), U.toOpens)) (t : Γ((S.irrelevantPow p (j - (a.1 + 1))).1, U.toOpens)),
        F₀ (s ⊗ₜ t) = AlgebraicGeometry.Scheme.Modules.tensorSections (S.part (a.1 + 1))
          (S.irrelevantPow p (j - (a.1 + 1))).1 U.toOpens s t := fun s t =>
      AlgebraicGeometry.Scheme.Modules.tensorSectionsHom_app _ _ U.toOpens s t
    obtain ⟨t, rfl⟩ := hF₀ za
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add, map_add, map_add]; exact add_mem hx hy
    | tmul s t =>
      rw [hF₀tmul]
      erw [hcomp]
      have e : a.1 + 1 + (j - (a.1 + 1)) = j := by have := a.2; omega
      have hval : S.ofPiece U.toOpens j ((CategoryTheory.eqToHom (congrArg S.part e)).app U.toOpens
          (((S.part (a.1 + 1) ◁ (S.irrelevantPow p (j - (a.1 + 1))).2) ≫ S.mul _ _).app U.toOpens
            (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part (a.1 + 1))
              (S.irrelevantPow p (j - (a.1 + 1))).1 U.toOpens s t))) =
          S.ofPiece U.toOpens (a.1 + 1) s *
            S.ofPiece U.toOpens (j - (a.1 + 1)) ((S.irrelevantPow p (j - (a.1 + 1))).2.app U.toOpens t) :=
        (ofPiece_eqToHom_app S U.toOpens e _).trans
          ((congrArg (S.ofPiece U.toOpens _) (whiskerLeft_comp_mul_app_tensorSections S U.toOpens _ s t)).trans
            (ofPiece_sectionsGMul_lwp S U.toOpens s _))
      have h2 : S.ofPiece U.toOpens (a.1 + 1) s *
          S.ofPiece U.toOpens (j - (a.1 + 1)) ((S.irrelevantPow p (j - (a.1 + 1))).2.app U.toOpens t) ∈
            ReesAlgebra.irrelevant (S.toGradedAffineAlgebra.gradingSubmodule U) *
              ReesAlgebra.irrelevant (S.toGradedAffineAlgebra.gradingSubmodule U) ^ p :=
        Ideal.mul_mem_mul
          (HomogeneousIdeal.mem_irrelevant_of_mem (S.toGradedAffineAlgebra.gradingSubmodule U) (Nat.succ_pos a.1)
            ⟨s, rfl⟩)
          (ofPiece_irrelevantPow_app_mem_irrPow U p _ t).1
      rw [← pow_succ'] at h2
      show S.ofPiece U.toOpens j _ ∈ ReesAlgebra.irrPow (S.toGradedAffineAlgebra.gradingSubmodule U) (p + 1) j
      refine (ReesAlgebra.mem_irrPow (S.toGradedAffineAlgebra.gradingSubmodule U)).2 ⟨?_, ⟨_, rfl⟩⟩
      erw [hval]
      exact h2

/-- **(a4, ⇐)** An element of `(S(U)_+)^p ∩ S(U)_j` of the form `of_j x` comes from `Γ(U, I^{(p)}_j)`. No affineness
is used. -/
theorem exists_irrelevantPow_app_eq_of_mem_irrPow (U : X.AffineZariskiSite) :
    ∀ (p j : ℕ) (x : S.sectionsPiece U.toOpens j),
      (S.ofPiece U.toOpens j x : S.toGradedAffineAlgebra.toAffineAlgebra.sections U) ∈
        ReesAlgebra.irrPow (S.toGradedAffineAlgebra.gradingSubmodule U) p j →
      ∃ y, (S.irrelevantPow p j).2.app U.toOpens y = x
  | 0, j, x, _ => ⟨x, rfl⟩
  | p + 1, j, x, hx => by
    let N : ℕ → AddSubgroup (S.sectionsRing U.toOpens) := fun n =>
      (AddMonoidHom.range ((S.irrelevantPow (p + 1) n).2.app U.toOpens).hom).map
        (DirectSum.of (S.sectionsPiece U.toOpens) n)
    have key := ReesAlgebra.irrPow_succ_le (S.toGradedAffineAlgebra.gradingSubmodule U) p N ?_ j hx
    · obtain ⟨_, ⟨y, rfl⟩, hxy⟩ := key
      exact ⟨y, DirectSum.of_injective j hxy⟩
    intro d e hd a ha b hb
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t', rfl⟩ := hb.2
    obtain ⟨t, rfl⟩ := exists_irrelevantPow_app_eq_of_mem_irrPow U p e t' hb
    have hl := S.landsIn_whiskerLeft_irrelevantPow_mul_succ p d e (d + e) hd rfl
    rw [eqToHom_refl, Category.comp_id] at hl
    obtain ⟨g, hg⟩ := (S.landsIn_iff_exists _ _).1 hl
    refine ⟨_, ⟨g.app U.toOpens (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part d) _ U.toOpens s t), rfl⟩, ?_⟩
    refine Eq.trans ?_ (ofPiece_sectionsGMul_lwp S U.toOpens s ((S.irrelevantPow p e).2.app U.toOpens t))
    apply congrArg
    show (g ≫ (S.irrelevantPow (p + 1) (d + e)).2).app U.toOpens _ = S.sectionsGMul U.toOpens s _
    rw [← hg]
    exact whiskerLeft_comp_mul_app_tensorSections S U.toOpens _ s t

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
