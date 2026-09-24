import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowGradedMonoid
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc

/-! # The section ring of a line bundle

The graded ring `Γ_*(X, L) = ⊕_{n≥0} Γ(X, L^{⊗n})` (multiplication: tensor of sections followed by the
additive isomorphism of tensor powers).

References: Stacks 01MM (`Γ_*(X, L) = ⊕_{n≥0} Γ(X, L^{⊗n})`, the `Γ_*` of modules/constructions); the `S`
of 01PZ, 01Q1.

The three graded-algebra axioms `tensorPowAlgebra.one_mul / mul_assoc / mul_comm` are
proved by instantiating the abstract `MiyaokaMori.IsTensorPowMul.isGradedMonoid`
(pure monoidal coherence + naturality, by induction on the tensor exponent) at `P = tensorPow L`,
`c e = tensorIsoTensorObj (tensorPow L e) L`, `μ = mulHom L` (the two recursion equations are the
definition of `tensorPowAddIso` read backwards), together with `Modules.braiding_hom_eq_id_of_isLineBundle`
(`β_{L,L} = 𝟙` for a line bundle, Stacks 01CR), which is the only place `[L.IsLineBundle]` is used.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- The additive isomorphism of tensor powers `L^{⊗(m+n)} ≅ L^{⊗m} ⊗ L^{⊗n}` (`tensorPow` is right-recursive:
   `tensorPow (e+1) = Modules.tensor (tensorPow e) L`; recursion on `n`: `n = 0` uses the right unitor (the
   monoidal unit `𝟙_` and `SheafOfModules.unit` agree by construction; transported by `eqToIso`, the equality
   being `rfl`), `n + 1` uses the comparison isomorphism `tensorIsoTensorObj` between `Modules.tensor` and `⊗`
   and the associator. Built entirely from genuine isomorphisms.) -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowAddIso {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) (m : ℕ) : (n : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow L m ⊗ AlgebraicGeometry.Scheme.Modules.tensorPow L n)
  | 0 =>
    (ρ_ (AlgebraicGeometry.Scheme.Modules.tensorPow L m)).symm ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
        (CategoryTheory.eqToIso (show 𝟙_ X.Modules = (show X.Modules from SheafOfModules.unit X.ringCatSheaf) by
          with_unfolding_all rfl))
  | n + 1 =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.whiskerRightIso (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m n) L ≪≫
      α_ _ _ _ ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.tensorPow L n) L).symm

/- The graded quasi-coherent algebra `⊕_{n≥0} L^{⊗n}` of tensor powers of a line bundle: `part n = tensorPow L n`,
   multiplication the inverse of `tensorPowAddIso`, unit `𝟙_ = SheafOfModules.unit = tensorPow L 0` (`eqToHom`,
   the equality being `rfl`). Quasi-coherence (line bundles are locally free) and the associativity, unit and
   commutativity laws (for invertible `L` the permutation action on `L^{⊗n}` is trivial) are proof obligations. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (m n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPow L m ⊗ AlgebraicGeometry.Scheme.Modules.tensorPow L n ⟶ AlgebraicGeometry.Scheme.Modules.tensorPow L (m + n) :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m n).inv

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.oneHom {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] : 𝟙_ X.Modules ⟶ AlgebraicGeometry.Scheme.Modules.tensorPow L 0 :=
  CategoryTheory.eqToHom (show 𝟙_ X.Modules = AlgebraicGeometry.Scheme.Modules.tensorPow L 0 by with_unfolding_all rfl)

/- The following four statements are the proof obligations of `tensorPowAlgebra`. -/

/-- Tensor powers of a line bundle are line bundles, and line bundles are locally free, hence quasi-coherent. -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.part_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (n : ℕ) : (AlgebraicGeometry.Scheme.Modules.tensorPow L n).IsQuasicoherent :=
  -- tensor powers are line bundles; locally free ⇒ quasi-coherent
  have := SheafOfModules.IsLineBundle.tensorPow L n
  AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _

/-- The recursion equations of `mulHom L m n = (tensorPowAddIso L m n).inv`: these are the two
defining clauses of `tensorPowAddIso` read backwards (`mul_zero` is definitional; `mul_succ` is
the same composite reassociated). -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.isTensorPowMul {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    MiyaokaMori.IsTensorPowMul L (AlgebraicGeometry.Scheme.Modules.tensorPow L)
      (fun e => AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (AlgebraicGeometry.Scheme.Modules.tensorPow L e) L)
      (CategoryTheory.eqToIso (show 𝟙_ X.Modules = AlgebraicGeometry.Scheme.Modules.tensorPow L 0 by
        with_unfolding_all rfl))
      (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L) where
  mul_zero m := rfl
  mul_succ m n := by
    -- `(a ≪≫ b ≪≫ c ≪≫ d).inv` is definitionally `((d.inv ≫ c.inv) ≫ b.inv) ≫ a.inv`; reassociate.
    show ((_ ≫ _) ≫ _) ≫ _ = _ ≫ _ ≫ _ ≫ _
    simp only [Category.assoc]
    rfl

/-- The tensor powers of a line bundle form a graded commutative monoid in `X.Modules`
(`MiyaokaMori.IsGradedMonoid`): abstract coherence (`IsTensorPowMul.isGradedMonoid`) plus
`β_{L,L} = 𝟙` for a line bundle (`braiding_hom_eq_id_of_isLineBundle`, Stacks 01CR). -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.isGradedMonoid {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] :
    MiyaokaMori.IsGradedMonoid (AlgebraicGeometry.Scheme.Modules.tensorPow L)
      (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L)
      (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.oneHom L) :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.isTensorPowMul L).isGradedMonoid
    (AlgebraicGeometry.Scheme.Modules.braiding_hom_eq_id_of_isLineBundle L)

/-- Unit law of `tensorPowAlgebra` (from `tensorPowAlgebra.isGradedMonoid`). -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.one_mul {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.oneHom L ▷ AlgebraicGeometry.Scheme.Modules.tensorPow L m) ≫ AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L 0 m =
      (λ_ (AlgebraicGeometry.Scheme.Modules.tensorPow L m)).hom ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.tensorPow L) (Nat.zero_add m).symm) :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.isGradedMonoid L).one_mul m

/-- Associativity of `tensorPowAlgebra` (from `tensorPowAlgebra.isGradedMonoid`). -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mul_assoc {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (m n p : ℕ) :
    (α_ (AlgebraicGeometry.Scheme.Modules.tensorPow L m) (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (AlgebraicGeometry.Scheme.Modules.tensorPow L p)).hom ≫ (AlgebraicGeometry.Scheme.Modules.tensorPow L m ◁ AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L n p) ≫ AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L m (n + p) =
      (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L m n ▷ AlgebraicGeometry.Scheme.Modules.tensorPow L p) ≫ AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L (m + n) p ≫
        eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.tensorPow L) (Nat.add_assoc m n p)) :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.isGradedMonoid L).mul_assoc m n p

/-- Commutativity of `tensorPowAlgebra`; this is where `L` being a line bundle is used
(`β_{L,L} = 𝟙`, so the symmetric group acts trivially on `L^{⊗n}`; false for e.g. `O ⊕ O`). -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mul_comm {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (m n : ℕ) :
    (β_ (AlgebraicGeometry.Scheme.Modules.tensorPow L m) (AlgebraicGeometry.Scheme.Modules.tensorPow L n)).hom ≫ AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L n m =
      AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L m n ≫ eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.tensorPow L) (Nat.add_comm m n)) :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.isGradedMonoid L).mul_comm m n

noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] : X.GradedQCAlgebra where
  part n := AlgebraicGeometry.Scheme.Modules.tensorPow L n
  quasicoherent := AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.part_isQuasicoherent L
  mul m n := AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mulHom L m n
  one := AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.oneHom L
  one_mul := AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.one_mul L
  mul_assoc := AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mul_assoc L
  mul_comm := AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra.mul_comm L

/- `Γ_*(X, L) = ⊕_{n≥0} Γ(X, L^{⊗n})` (the `Γ_*` of Stacks 01MM, the `S` of 01PZ/01Q1): the ring of global
   sections over `X` of the graded algebra above (the `CommRing` structure comes from `DirectSum.GCommRing`;
   multiplication = tensor of sections followed by the multiplication morphism). -/

noncomputable abbrev AlgebraicGeometry.Scheme.Modules.gammaStar {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] : Type u :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsRing ⊤

/- Grading: the `n`-th piece = the image of `DirectSum.of n` `≅ Γ(X, L^{⊗n})`; the `GradedRing` instance comes
   from the instance of `sectionsGrading`. -/

noncomputable abbrev AlgebraicGeometry.Scheme.Modules.gammaStarGrading {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] : ℕ → AddSubgroup (AlgebraicGeometry.Scheme.Modules.gammaStar L) :=
  (AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsGrading ⊤

/- A degree-`n` section `s ∈ Γ(X, L^{⊗n})` as a homogeneous element of degree `n` of `Γ_*(X, L)`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.gammaStarOf {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (n : ℕ)
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.gammaStar L :=
  DirectSum.of ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsPiece ⊤) n s

theorem AlgebraicGeometry.Scheme.Modules.gammaStarOf_mem {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (n : ℕ)
    (s : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.gammaStarOf L n s ∈
      AlgebraicGeometry.Scheme.Modules.gammaStarGrading L n :=
  ⟨s, rfl⟩

/- The `n`-th component `∈ Γ(X, L^{⊗n})` of an element of `Γ_*(X, L)`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.gammaStarComponent {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (x : AlgebraicGeometry.Scheme.Modules.gammaStar L) (n : ℕ) :
    Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤) :=
  (show DirectSum ℕ ((AlgebraicGeometry.Scheme.Modules.tensorPowAlgebra L).sectionsPiece ⊤) from x) n

end
