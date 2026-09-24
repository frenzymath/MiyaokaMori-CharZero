import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalZero
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalComponent
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSectionOne
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowLineBundle
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra

/-! # Auxiliary lemmas for the closed immersion of the jet neighbourhood into the total space

Auxiliary lemmas for `JetNeighborhoodToTotalSpace`:
1. Composition of algebra maps (`QCAlgebra.IsAlgebraMapToPushforward.comp_of_mul_one`): if `φ : A → B` preserves
   multiplication and unit and `ψ : B → g_*O_T` is an algebra map, then `φ ≫ ψ` is an algebra map; the structure map
   `structureHom` is an algebra map (the second component of the universal property `relativeSpecHomEquiv` at the
   identity, `relativeSpec.structureHom_isAlgebraMap_jnl`).
2. A morphism out of `(∐ F) ⊗ (∐ G)` is determined by its composites with `ι_i ⊗ₘ ι_j` (naturality of the
   tensor-Hom adjunction in the first variable + braiding; index types in an arbitrary universe). The component
   formula for the total multiplication `totalMul` reuses `GradedAlgebraTotalComponent.totalMul_component`.
3. On a line bundle `W`, `symGradedAlgebra W = symGradedAlgebraOfQC W _`, whence three computation rules for
   `symPartToMonoidalPow`: composition with the unit is the identity, compatibility with multiplication (the
   inverse of `tensorHom_symPowπ_symPowMul`), and it is an isomorphism; moreover
   `symPartToMonoidalPow W 0 = symAugmentationZero W` (both are the inverse of `S.one`).
4. The formula for the multiplication `mulHom` of the truncated jet algebra on the biproduct component `(a, b)`
   (`Preadditive.comp_sum` + `Finset.sum_eq_single`; the off-diagonal terms vanish by `ι_a ≫ π_a' = 0` and
   `0 ⊗ₘ g = 0`).
5. Two variable-level monoidal lemmas (the induction step of `pieceIso`, and the assembly of the multiplicative
   compatibility).

Source: §3 of the paper; Stacks 01LQ (universal property of the relative Spec).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Composition of algebra maps. -/
theorem QCAlgebra.IsAlgebraMapToPushforward.comp_of_mul_one {X T : AlgebraicGeometry.Scheme.{u}}
    {A B : X.QCAlgebra} (g : T ⟶ X) (φ : A.carrier ⟶ B.carrier)
    (hmul : A.mul ≫ φ = (φ ⊗ₘ φ) ≫ B.mul) (hone : A.one ≫ φ = B.one)
    (ψ : B.carrier ⟶ (Modules.pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    (hψ : B.IsAlgebraMapToPushforward g ψ) : A.IsAlgebraMapToPushforward g (φ ≫ ψ) := by
  constructor
  · intro U a b
    have h1 : φ.app U (A.mul.app U (Modules.tensorSections A.carrier A.carrier U a b)) =
        B.mul.app U ((φ ⊗ₘ φ).app U (Modules.tensorSections A.carrier A.carrier U a b)) :=
      congrArg (fun f => f.app U (Modules.tensorSections A.carrier A.carrier U a b)) hmul
    have h2 := Modules.tensorHom_tensorSections φ φ U a b
    have h3 := hψ.1 U (φ.app U a) (φ.app U b)
    exact (congrArg (fun x => (show Γ(T, g ⁻¹ᵁ U) from ψ.app U x))
      (h1.trans (congrArg (B.mul.app U) h2))).trans h3
  · intro U
    have h1 : φ.app U (A.one.app U (show Γ(X, U) from 1)) = B.one.app U (show Γ(X, U) from 1) :=
      congrArg (fun f => f.app U (show Γ(X, U) from 1)) hone
    exact (congrArg (fun x => (show Γ(T, g ⁻¹ᵁ U) from ψ.app U x)) h1).trans (hψ.2 U)

/-- The structure map is an algebra map (the second component of the universal property at the identity). -/
theorem relativeSpec.structureHom_isAlgebraMap_jnl {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) :
    A.IsAlgebraMapToPushforward (relativeSpec A).hom (relativeSpec.structureHom A) :=
  (relativeSpecHomEquiv A (relativeSpec A) (CategoryTheory.CategoryStruct.id _)).2

namespace Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- A morphism out of `(∐ F) ⊗ (∐ G)` is determined by its composites with `ι_i ⊗ₘ ι_j`.
(`GradedAlgebraTotalComponent.tensorObj_sigma_hom_ext` restricts the index type to `Type u` (the universe of the
scheme) and does not apply to the `ℕ`-indexed `∐ S.part` over a general `Scheme.{u}`; this version allows an index
type in any universe.) -/
theorem tensorHom_sigma_hom_ext {ι : Type v} (F G : ι → X.Modules) [HasCoproduct F] [HasCoproduct G]
    {T : X.Modules} (f g : (∐ F) ⊗ (∐ G) ⟶ T)
    (h : ∀ i j, (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ f = (Sigma.ι F i ⊗ₘ Sigma.ι G j) ≫ g) : f = g := by
  apply (tensorObjHomEquiv _ _ _).injective
  apply Sigma.hom_ext
  intro i
  rw [tensorObjHomEquiv_naturality_left, tensorObjHomEquiv_naturality_left]
  congr 1
  rw [← cancel_epi (β_ (∐ G) (F i)).hom]
  apply (tensorObjHomEquiv _ _ _).injective
  apply Sigma.hom_ext
  intro j
  rw [tensorObjHomEquiv_naturality_left, tensorObjHomEquiv_naturality_left]
  congr 1
  rw [BraidedCategory.braiding_naturality_left_assoc, BraidedCategory.braiding_naturality_left_assoc,
    ← MonoidalCategory.tensorHom_def'_assoc, ← MonoidalCategory.tensorHom_def'_assoc, h i j]

end Modules

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

theorem GradedQCAlgebra.mul_eq_of_eq {S S' : X.GradedQCAlgebra} (h : S = S') (m n : ℕ) :
    S.mul m n = (eqToHom (congrArg (fun T : X.GradedQCAlgebra => T.part m) h) ⊗ₘ
        eqToHom (congrArg (fun T : X.GradedQCAlgebra => T.part n) h)) ≫ S'.mul m n ≫
      eqToHom (congrArg (fun T : X.GradedQCAlgebra => T.part (m + n)) h).symm := by
  subst h; simp

theorem GradedQCAlgebra.one_eq_of_eq {S S' : X.GradedQCAlgebra} (h : S = S') :
    S.one = S'.one ≫ eqToHom (congrArg (fun T : X.GradedQCAlgebra => T.part 0) h).symm := by
  subst h; simp

/-- On a line bundle, `symGradedAlgebra W` takes the quasi-coherent branch. This is the special case of
`Modules.symGradedAlgebra_eq_ofQC V h` (explicit `h`) of `SymGradedAlgebraCongr.lean`; it is reproved here under a
different name to keep the import closure small. -/
theorem Modules.symGradedAlgebra_eq_ofQC_of_isLineBundle (W : X.Modules) [W.IsLineBundle] :
    Modules.symGradedAlgebra W = Modules.symGradedAlgebraOfQC W (Modules.IsLineBundle.isQuasicoherent W) := by
  delta Modules.symGradedAlgebra; exact dif_pos _

theorem Modules.symPartToMonoidalPow_eq (W : X.Modules) [W.IsLineBundle] (m : ℕ) :
    Modules.symPartToMonoidalPow W m =
      eqToHom (congrArg (fun T : X.GradedQCAlgebra => T.part m) (Modules.symGradedAlgebra_eq_ofQC_of_isLineBundle W)) ≫
        @inv _ _ _ _ (Modules.symPowπ W m) (Modules.symPowπ_isIso_of_isLineBundle W m) := by
  have hS := Modules.symGradedAlgebra_eq_ofQC_of_isLineBundle W
  unfold Modules.symPartToMonoidalPow
  generalize_proofs _ _ hq pfT _ pfP _
  change (pfT hq).mpr (@inv _ _ _ _ (Modules.symPowπ W m) (Modules.symPowπ_isIso_of_isLineBundle W m)) =
    eqToHom pfP ≫ @inv _ _ _ _ (Modules.symPowπ W m) (Modules.symPowπ_isIso_of_isLineBundle W m)
  generalize Modules.symGradedAlgebra W = S at hS pfT pfP ⊢
  subst hS
  exact (Category.id_comp _).symm

/-- The formula for the multiplication on the biproduct component `(a, b)`. -/
theorem truncatedJetAlgebra.tensorHom_ι_mulHom {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : _root_.LineBundle Ct.toVariety) (κ : ℕ) (a b : Fin (κ + 1)) :
    (biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) a ⊗ₘ
        biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) b) ≫
      truncatedJetAlgebra.mulHom L κ =
    if h : a.val + b.val ≤ κ then
      truncatedJetAlgebra.pieceMul L a b ≫
        biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟨a.val + b.val, Nat.lt_succ_of_le h⟩
    else 0 := by
  unfold truncatedJetAlgebra.mulHom
  rw [Preadditive.comp_sum, Finset.sum_eq_single a]
  · rw [Preadditive.comp_sum, Finset.sum_eq_single b]
    · split_ifs with h
      · rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, biproduct.ι_π_self, biproduct.ι_π_self,
          MonoidalCategory.id_tensorHom_id, Category.id_comp]
      · exact comp_zero
    · intro b' _ hb
      split_ifs with h
      · rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, biproduct.ι_π_ne _ (Ne.symm hb),
          Modules.tensorHom_zeroMorphism, zero_comp]
      · exact comp_zero
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ ha
    rw [Preadditive.comp_sum]
    refine Finset.sum_eq_zero (fun b' _ => ?_)
    split_ifs with h
    · rw [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, biproduct.ι_π_ne _ (Ne.symm ha),
        Modules.zeroMorphism_tensorHom, zero_comp]
    · exact comp_zero
  · intro h; exact absurd (Finset.mem_univ _) h

section general
variable {C : Type*} [Category C] [MonoidalCategory C]

/-- The monoidal lemma used in the induction step of `pieceIso`. -/
theorem tensorHom_assoc_inv_whiskerRight_of_eq {A B A' B' Q Q' M W : C} (f : A ⟶ A') (g : B ⟶ B')
    (h : M ⟶ W) (mul : A ⊗ B ⟶ Q) (cat : A' ⊗ B' ⟶ Q') (e : Q ⟶ Q')
    (ih : (f ⊗ₘ g) ≫ cat = mul ≫ e) :
    (f ⊗ₘ (g ⊗ₘ h)) ≫ (α_ A' B' W).inv ≫ (cat ▷ W) = (α_ A B M).inv ≫ (mul ▷ M) ≫ (e ⊗ₘ h) := by
  rw [MonoidalCategory.associator_inv_naturality_assoc, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, ih, Category.comp_id, ← MonoidalCategory.tensorHom_id,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- Assembly lemma: `mul ≫ smn ≫ imn ≫ ι = ((sm ≫ im) ⊗ₘ (sn ≫ in')) ≫ pmul ≫ ι`. -/
theorem mul_comp_eq_tensorHom_comp_of_eq {Sm Sn Smn Pm Pn Pmn Qm Qn Qmn T : C}
    (mul : Sm ⊗ Sn ⟶ Smn) (sm : Sm ⟶ Pm) (sn : Sn ⟶ Pn) (smn : Smn ⟶ Pmn) (cat : Pm ⊗ Pn ⟶ Pmn)
    (hA : mul ≫ smn = (sm ⊗ₘ sn) ≫ cat) (im : Pm ⟶ Qm) (in' : Pn ⟶ Qn) (imn : Pmn ⟶ Qmn)
    (pmul : Qm ⊗ Qn ⟶ Qmn) (hB : cat ≫ imn = (im ⊗ₘ in') ≫ pmul) (ι : Qmn ⟶ T) :
    mul ≫ smn ≫ imn ≫ ι = ((sm ≫ im) ⊗ₘ (sn ≫ in')) ≫ pmul ≫ ι := by
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, ← reassoc_of% hB, reassoc_of% hA]

end general

end AlgebraicGeometry.Scheme


namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Not registered as a global instance; introduce it with `haveI` where needed. -/
theorem symPartToMonoidalPow_isIso (W : X.Modules) [W.IsLineBundle] (m : ℕ) :
    IsIso (symPartToMonoidalPow W m) := by
  rw [symPartToMonoidalPow_eq]
  exact IsIso.comp_isIso' inferInstance
    (@IsIso.inv_isIso _ _ _ _ (symPowπ W m) (symPowπ_isIso_of_isLineBundle W m))

/-- Not registered as a global instance; introduce it with `haveI` where needed. -/
theorem symGradedAlgebra_one_isIso (W : X.Modules) [W.IsLineBundle] :
    IsIso (symGradedAlgebra W).one := by
  rw [GradedQCAlgebra.one_eq_of_eq (symGradedAlgebra_eq_ofQC_of_isLineBundle W)]
  have : IsIso (symGradedAlgebraOfQC W (IsLineBundle.isQuasicoherent W)).one :=
    symPowπ_isIso_of_isLineBundle W 0
  infer_instance

/-- The unit composed with `symPartToMonoidalPow 0` is the identity. -/
theorem one_comp_symPartToMonoidalPow (W : X.Modules) [W.IsLineBundle] :
    (symGradedAlgebra W).one ≫ symPartToMonoidalPow W 0 = 𝟙 (𝟙_ X.Modules) := by
  rw [GradedQCAlgebra.one_eq_of_eq (symGradedAlgebra_eq_ofQC_of_isLineBundle W), symPartToMonoidalPow_eq,
    Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  exact IsIso.hom_inv_id (symPowπ W 0)

/-- `symPartToMonoidalPow 0 = symAugmentationZero` (both are the inverse of `S.one`). -/
theorem symPartToMonoidalPow_zero_eq_symAugmentationZero (W : X.Modules) [W.IsLineBundle] :
    symPartToMonoidalPow W 0 = symAugmentationZero W := by
  have := symGradedAlgebra_one_isIso W
  exact (cancel_epi (symGradedAlgebra W).one).mp
    ((one_comp_symPartToMonoidalPow W).trans (one_comp_symAugmentationZero W).symm)

/-- Under `symPartToMonoidalPow`, the multiplication of `Sym` corresponds to concatenation of tensor powers. -/
theorem mul_comp_symPartToMonoidalPow (W : X.Modules) [W.IsLineBundle] (m n : ℕ) :
    (symGradedAlgebra W).mul m n ≫ symPartToMonoidalPow W (m + n) =
      (symPartToMonoidalPow W m ⊗ₘ symPartToMonoidalPow W n) ≫ (monoidalPowCat W m n).hom := by
  have key : symPowMul W m n ≫ inv (symPowπ W (m + n)) =
      (inv (symPowπ W m) ⊗ₘ inv (symPowπ W n)) ≫ (monoidalPowCat W m n).hom := by
    have := epi_tensorHom_of_epi (symPowπ W m) (symPowπ W n)
    rw [← cancel_epi (symPowπ W m ⊗ₘ symPowπ W n), ← Category.assoc, tensorHom_symPowπ_symPowMul,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, IsIso.hom_inv_id, IsIso.hom_inv_id,
      MonoidalCategory.id_tensorHom_id, Category.id_comp]
  rw [GradedQCAlgebra.mul_eq_of_eq (symGradedAlgebra_eq_ofQC_of_isLineBundle W), symPartToMonoidalPow_eq,
    symPartToMonoidalPow_eq, symPartToMonoidalPow_eq]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc]
  exact congrArg (fun t => _ ≫ t) key

end AlgebraicGeometry.Scheme.Modules

end
