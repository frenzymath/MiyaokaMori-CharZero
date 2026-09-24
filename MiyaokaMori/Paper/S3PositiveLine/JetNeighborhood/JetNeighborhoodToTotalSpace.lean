import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecOfAlgebraMapSections
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotal
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpaceLemmas
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymPowLineBundle
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra

/-! # The closed immersion of the jet neighbourhood into the total space

The closed immersion `C̃_(κ)(L) ↪ Tot(L)` (a morphism over `C̃`), given through the universal property of the
relative Spec by the truncation map `Sym(L^∨) → ⊕_{q≤κ} L^{-q}`; it is compatible with the zero sections
(§3 of the paper: `C̃_(k)(L) ⊂ Tot(L)` is the `k`-th infinitesimal neighbourhood of the zero section).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- Comparison of the `q`-th piece `(L^{-1})^{⊗q}` of the truncated jet algebra with `(L^∨)^{⊗q}` (both are defined by
recursion multiplying on the right in the monoidal structure; factorwise `zpowNegOneIso`). -/

noncomputable def truncatedJetAlgebra.pieceIso {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) : (q : ℕ) →
    (truncatedJetAlgebra.piece L q ≅
      AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q)
  | 0 => CategoryTheory.Iso.refl _
  | q + 1 => CategoryTheory.MonoidalCategory.tensorIso (truncatedJetAlgebra.pieceIso L q) L.zpowNegOneIso

/-- The truncation map `⊕_m Sym^m(L^∨) → ⊕_{q ≤ κ} (L^{-1})^{⊗q}`: the component `m ≤ κ` is sent to the `m`-th piece
through `Sym^m ≅ (L^∨)^{⊗m} ≅ (L^{-1})^{⊗m}`, the components `m > κ` to `0`. The type is written
`(∐ S.part) ⟶ truncatedJetAlgebra.obj L κ` (a reducible spelling of
`S.total.carrier ⟶ (truncatedJetAlgebra L κ).carrier`). -/

noncomputable def truncatedJetAlgebra.truncation {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (∐ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part) ⟶
      truncatedJetAlgebra.obj L κ :=
  CategoryTheory.Limits.Sigma.desc fun m =>
    if h : m ≤ κ then
      AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m ≫
        (truncatedJetAlgebra.pieceIso L m).inv ≫
        CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨m, Nat.lt_succ_of_le h⟩
    else 0

/-- The formula for the truncation map on the `m`-th component (`Sigma.ι_desc`). -/
theorem truncatedJetAlgebra.ι_truncation {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) (m : ℕ) :
    CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part m ≫ truncatedJetAlgebra.truncation L κ =
      if h : m ≤ κ then
        AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m ≫
          (truncatedJetAlgebra.pieceIso L m).inv ≫
          CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨m, Nat.lt_succ_of_le h⟩
      else 0 :=
  CategoryTheory.Limits.Sigma.ι_desc _ _

/-- `pieceIso` is compatible with the multiplications on both sides:
`(pieceIso m ⊗ pieceIso n) ≫ monoidalPowCat m n = pieceMul m n ≫ pieceIso (m+n)` (induction on `n`: `n = 0` is the
naturality of the right unitor, `n + 1` the naturality of the associator plus the induction hypothesis). -/
theorem truncatedJetAlgebra.pieceIso_mul {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (m : ℕ) : ∀ n : ℕ,
    ((truncatedJetAlgebra.pieceIso L m).hom ⊗ₘ (truncatedJetAlgebra.pieceIso L n).hom) ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom =
      truncatedJetAlgebra.pieceMul L m n ≫ (truncatedJetAlgebra.pieceIso L (m + n)).hom
  | 0 => by
    show ((truncatedJetAlgebra.pieceIso L m).hom ⊗ₘ 𝟙 (𝟙_ Ct.toScheme.Modules)) ≫
        (ρ_ (AlgebraicGeometry.Scheme.Modules.monoidalPow
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m)).hom =
      (ρ_ (truncatedJetAlgebra.piece L m)).hom ≫ (truncatedJetAlgebra.pieceIso L m).hom
    rw [CategoryTheory.MonoidalCategory.tensorHom_id, CategoryTheory.MonoidalCategory.rightUnitor_naturality]
  | n + 1 => by
    show ((truncatedJetAlgebra.pieceIso L m).hom ⊗ₘ
          ((truncatedJetAlgebra.pieceIso L n).hom ⊗ₘ L.zpowNegOneIso.hom)) ≫
        (α_ _ _ _).inv ≫ ((AlgebraicGeometry.Scheme.Modules.monoidalPowCat
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom ▷
            AlgebraicGeometry.Scheme.Modules.dual L.toModules) =
      (α_ _ _ _).inv ≫ (truncatedJetAlgebra.pieceMul L m n ▷ (L.zpow (-1)).toModules) ≫
        ((truncatedJetAlgebra.pieceIso L (m + n)).hom ⊗ₘ L.zpowNegOneIso.hom)
    exact AlgebraicGeometry.Scheme.tensorHom_assoc_inv_whiskerRight_of_eq _ _ _ _ _ _
      (truncatedJetAlgebra.pieceIso_mul L m n)

/-- The inverse form of the previous lemma:
`monoidalPowCat m n ≫ (pieceIso (m+n))⁻¹ = ((pieceIso m)⁻¹ ⊗ (pieceIso n)⁻¹) ≫ pieceMul m n`. -/
theorem truncatedJetAlgebra.monoidalPowCat_comp_pieceIso_inv {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPowCat
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m n).hom ≫
        (truncatedJetAlgebra.pieceIso L (m + n)).inv =
      ((truncatedJetAlgebra.pieceIso L m).inv ⊗ₘ (truncatedJetAlgebra.pieceIso L n).inv) ≫
        truncatedJetAlgebra.pieceMul L m n := by
  rw [CategoryTheory.Iso.comp_inv_eq, CategoryTheory.Category.assoc, ← truncatedJetAlgebra.pieceIso_mul,
    ← CategoryTheory.Category.assoc, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
    CategoryTheory.Iso.inv_hom_id, CategoryTheory.Iso.inv_hom_id,
    CategoryTheory.MonoidalCategory.id_tensorHom_id, CategoryTheory.Category.id_comp]

/-- The reassociated form of `one_comp_symPartToMonoidalPow` (avoids mixing the spellings `𝟙_` and `monoidalPow W 0`). -/
theorem truncatedJetAlgebra.one_comp_symPartToMonoidalPow_assoc {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) {T : Ct.toScheme.Modules}
    (g : AlgebraicGeometry.Scheme.Modules.monoidalPow
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) 0 ⟶ T) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).one ≫
      AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) 0 ≫ g = g :=
  (CategoryTheory.Category.assoc _ _ _).symm.trans
    ((congrArg (fun x : 𝟙_ Ct.toScheme.Modules ⟶ AlgebraicGeometry.Scheme.Modules.monoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) 0 => x ≫ g)
      (AlgebraicGeometry.Scheme.Modules.one_comp_symPartToMonoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules))).trans (CategoryTheory.Category.id_comp g))

/-- **`τ` preserves the unit** (reducible spelling): `(S.one ≫ ι_0) ≫ τ = oneHom`. -/
theorem truncatedJetAlgebra.one_comp_truncation {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).one ≫
      CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part 0) ≫
        truncatedJetAlgebra.truncation L κ =
      truncatedJetAlgebra.oneHom L κ := by
  rw [CategoryTheory.Category.assoc, truncatedJetAlgebra.ι_truncation, dif_pos (Nat.zero_le κ),
    truncatedJetAlgebra.one_comp_symPartToMonoidalPow_assoc]
  exact CategoryTheory.Category.id_comp _

/-- **`τ` preserves multiplication** (reducible spelling): `totalMul S ≫ τ = (τ ⊗ τ) ≫ mulHom`. Componentwise in
`(m, n)` (`tensorHom_sigma_hom_ext`): for `m + n ≤ κ` both sides land in the `(m + n)`-th piece and the claim reduces
to `mul_comp_symPartToMonoidalPow` and `monoidalPowCat_comp_pieceIso_inv`; for `m + n > κ` both sides are `0` (this
is exactly the paper's "products of weight greater than `κ` are zero"). -/
theorem truncatedJetAlgebra.totalMul_comp_truncation {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)) ≫
        truncatedJetAlgebra.truncation L κ =
      (truncatedJetAlgebra.truncation L κ ⊗ₘ truncatedJetAlgebra.truncation L κ) ≫
        truncatedJetAlgebra.mulHom L κ := by
  apply AlgebraicGeometry.Scheme.Modules.tensorHom_sigma_hom_ext
  intro m n
  rw [← CategoryTheory.Category.assoc, AlgebraicGeometry.Scheme.GradedQCAlgebra.totalMul_component,
    CategoryTheory.Category.assoc, truncatedJetAlgebra.ι_truncation, ← CategoryTheory.Category.assoc,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, truncatedJetAlgebra.ι_truncation,
    truncatedJetAlgebra.ι_truncation]
  by_cases hmn : m + n ≤ κ
  · have hm : m ≤ κ := le_trans (Nat.le_add_right m n) hmn
    have hn : n ≤ κ := le_trans (Nat.le_add_left n m) hmn
    rw [dif_pos hmn, dif_pos hm, dif_pos hn]
    have hG := AlgebraicGeometry.Scheme.truncatedJetAlgebra.tensorHom_ι_mulHom L κ
      ⟨m, Nat.lt_succ_of_le hm⟩ ⟨n, Nat.lt_succ_of_le hn⟩
    rw [dif_pos (show ((⟨m, Nat.lt_succ_of_le hm⟩ : Fin (κ + 1)) : ℕ) +
        ((⟨n, Nat.lt_succ_of_le hn⟩ : Fin (κ + 1)) : ℕ) ≤ κ from hmn)] at hG
    refine (AlgebraicGeometry.Scheme.mul_comp_eq_tensorHom_comp_of_eq _ _ _ _ _
      (AlgebraicGeometry.Scheme.Modules.mul_comp_symPartToMonoidalPow _ m n) _ _ _ _
      (truncatedJetAlgebra.monoidalPowCat_comp_pieceIso_inv L m n) _).trans ?_
    rw [← hG, ← CategoryTheory.Category.assoc, CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [CategoryTheory.Category.assoc]
  · rw [dif_neg hmn, CategoryTheory.Limits.comp_zero]
    by_cases hm : m ≤ κ
    · by_cases hn : n ≤ κ
      · rw [dif_pos hm, dif_pos hn]
        have hG := AlgebraicGeometry.Scheme.truncatedJetAlgebra.tensorHom_ι_mulHom L κ
          ⟨m, Nat.lt_succ_of_le hm⟩ ⟨n, Nat.lt_succ_of_le hn⟩
        rw [dif_neg (show ¬ (((⟨m, Nat.lt_succ_of_le hm⟩ : Fin (κ + 1)) : ℕ) +
            ((⟨n, Nat.lt_succ_of_le hn⟩ : Fin (κ + 1)) : ℕ) ≤ κ) from hmn)] at hG
        rw [← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom,
          ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom, CategoryTheory.Category.assoc,
          CategoryTheory.Category.assoc, hG, CategoryTheory.Limits.comp_zero,
          CategoryTheory.Limits.comp_zero]
      · rw [dif_neg hn, AlgebraicGeometry.Scheme.Modules.tensorHom_zeroMorphism, CategoryTheory.Limits.zero_comp]
    · rw [dif_neg hm, AlgebraicGeometry.Scheme.Modules.zeroMorphism_tensorHom, CategoryTheory.Limits.zero_comp]

/- The closed immersion `C̃_(κ)(L) ↪ Tot(L)` (a morphism over `C̃`) is obtained from the universal property of the
   relative Spec applied to `Sym(L^∨) → ⊕_{q ≤ κ} L^{-q} → (p_κ)_*O` (truncation followed by the structure map);
   the next theorem shows that this composite is an algebra map. -/
/-- The truncation followed by the structure map, `Sym(L^∨) → ⊕_{q ≤ κ} L^{-q} → (p_κ)_*O`, is an algebra map.

Source: §3 of the paper (`C̃_{(k)}(L) = Spec_{C̃}(⊕_{q=0}^k L^{-q})`, "where products of degree greater than k are
zero"; it is the `k`-th infinitesimal neighbourhood of the zero section in `Tot(L)`). Stacks 01LQ/01S5 (relative
Spec and quasi-coherent algebras).

Proof. Write `S = symGradedAlgebra (dual L)` (`Sym(L^∨)`), `A = truncatedJetAlgebra L κ`,
`τ = truncatedJetAlgebra.truncation L κ : S.total.carrier ⟶ A.carrier` and
`σ = relativeSpec.structureHom A : A.carrier ⟶ (p_κ)_*O`. The structure map `σ` is an algebra map (it is the second
component of the universal property `relativeSpecHomEquiv A (relativeSpec A) (𝟙 _)`,
`relativeSpec.structureHom_isAlgebraMap_jnl`), and a composite `τ ≫ σ` with `τ` preserving unit and multiplication
is an algebra map (`IsAlgebraMapToPushforward.comp_of_mul_one`). It remains to see that `τ` preserves the unit
(`one_comp_truncation`) and the multiplication (`totalMul_comp_truncation`): componentwise in `(m, n)`, for
`m + n ≤ κ` both sides land in the `(m+n)`-th piece and one uses (a) the compatibility of the multiplication of
`Sym` with `symPartToMonoidalPow` (`Modules.mul_comp_symPartToMonoidalPow`) and (b) the compatibility of `pieceIso`
with `pieceMul`/`monoidalPowCat` (`pieceIso_mul`, induction on `n`); for `m + n > κ` both sides are `0` by the
definitions of `mulHom` and `truncation` (the formal content of "products of weight greater than `κ` are zero").
The type of `truncation` is spelled `(∐ S.part) ⟶ truncatedJetAlgebra.obj L κ` (definitionally equal to
`S.total.carrier ⟶ A.carrier`) so that composites with `Sigma.ι`/`biproduct.ι` can be matched by `rw`. -/
theorem jetNeighborhood.truncation_structureHom_isAlgebraMap {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total.IsAlgebraMapToPushforward
      (jetNeighborhood L κ).hom
      (truncatedJetAlgebra.truncation L κ ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)) :=
  AlgebraicGeometry.Scheme.QCAlgebra.IsAlgebraMapToPushforward.comp_of_mul_one
    (A := (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total)
    (B := truncatedJetAlgebra L κ) (jetNeighborhood L κ).hom
    (truncatedJetAlgebra.truncation L κ)
    (truncatedJetAlgebra.totalMul_comp_truncation L κ) (truncatedJetAlgebra.one_comp_truncation L κ)
    (AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ))
    (AlgebraicGeometry.Scheme.relativeSpec.structureHom_isAlgebraMap_jnl (truncatedJetAlgebra L κ))

/-- The closed immersion `C̃_(κ)(L) ↪ Tot(L)` over `C̃`, corresponding under the universal property of the relative
Spec to the algebra map `τ ≫ σ : Sym(L^∨) → ⊕_{q ≤ κ} L^{-q} → (p_κ)_*O`. -/
noncomputable def jetNeighborhood.toTotalSpace {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    jetNeighborhood L κ ⟶ AlgebraicGeometry.Scheme.totalSpace L.toModules :=
  (AlgebraicGeometry.Scheme.relativeSpecHomEquiv
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total (jetNeighborhood L κ)).symm
    ⟨truncatedJetAlgebra.truncation L κ ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ),
      jetNeighborhood.truncation_structureHom_isAlgebraMap L κ⟩

/-- `C̃_(κ)(L) ↪ Tot(L)` is a morphism over `C̃`: composed with `Tot(L) → C̃` it is `p_κ`. -/
theorem jetNeighborhood.toTotalSpace_proj {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (jetNeighborhood.toTotalSpace L κ).left ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom =
      jetNeighborhood.proj L κ :=
  CategoryTheory.Over.w _

/-- A section of `τ`: the `q`-th piece goes back to `Sym^q ↪ Sym` through `pieceIso` and `(symPartToMonoidalPow q)⁻¹`. -/
noncomputable def truncatedJetAlgebra.truncationSection {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    truncatedJetAlgebra.obj L κ ⟶
      (∐ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part) :=
  CategoryTheory.Limits.biproduct.desc fun q : Fin (κ + 1) =>
    -- `symPartToMonoidalPow_isIso` is a theorem, not a global instance; introduce it locally.
    haveI := AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow_isIso
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q
    (truncatedJetAlgebra.pieceIso L q).hom ≫
      CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q) ≫
      CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part q

/-- `truncationSection ≫ truncation = 𝟙`: `τ` is a split epimorphism. -/
theorem truncatedJetAlgebra.truncationSection_comp_truncation {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    truncatedJetAlgebra.truncationSection L κ ≫ truncatedJetAlgebra.truncation L κ =
      CategoryTheory.CategoryStruct.id _ := by
  apply CategoryTheory.Limits.biproduct.hom_ext'
  intro q
  unfold truncatedJetAlgebra.truncationSection
  haveI := AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow_isIso
    (AlgebraicGeometry.Scheme.Modules.dual L.toModules) q
  rw [CategoryTheory.Limits.biproduct.ι_desc_assoc, CategoryTheory.Category.comp_id,
    CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, truncatedJetAlgebra.ι_truncation,
    dif_pos (Nat.le_of_lt_succ q.2), CategoryTheory.IsIso.inv_hom_id_assoc,
    CategoryTheory.Iso.hom_inv_id_assoc]

/-- The section map of `τ` on every open set is surjective. -/
theorem truncatedJetAlgebra.truncation_app_surjective {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) (V : Ct.toScheme.Opens) :
    Function.Surjective ((truncatedJetAlgebra.truncation L κ).app V) := fun y =>
  ⟨(truncatedJetAlgebra.truncationSection L κ).app V y,
    congrArg (fun g => g.app V y) (truncatedJetAlgebra.truncationSection_comp_truncation L κ)⟩

/-- **`C̃_(κ)(L) ↪ Tot(L)` is a closed immersion.**

Source: §3 of the paper ("This is the k-th infinitesimal neighborhood of the zero section in Tot(L); a frame of L on
an affine open V ⊆ C̃ identifies its restriction to V with Spec(O_{C̃}(V)[t]/(t^{k+1}))"); Stacks 01QP / 01SG (a
surjection of quasi-coherent algebras induces a closed immersion of relative Specs).

Proof. Being a closed immersion is local on the target (`IsZariskiLocalAtTarget.of_iSup_eq_top`); take the cover by
the preimages `π⁻¹U` of the affine opens `U` of `C̃`. Both `π⁻¹U` and `f⁻¹π⁻¹U = p⁻¹U` are affine (a relative Spec is
an affine morphism), so it suffices that the section map of `f` on `π⁻¹U` is surjective (Mathlib
`IsClosedImmersion.of_surjective_of_isAffine`). Now `f^♯(structureHom_S c) = (τ ≫ structureHom_A)(c)`
(`ofAlgebraMap_appLE_structureHom`), the structure maps are bijective on affine opens (Stacks 01LQ(2)), and `τ` has
the section `truncationSection` (it is a split epimorphism), hence is surjective on sections. No local model
`O(V)[t]/(t^{κ+1})` is needed. -/
instance jetNeighborhood.toTotalSpace_isClosedImmersion {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    AlgebraicGeometry.IsClosedImmersion (jetNeighborhood.toTotalSpace L κ).left := by
  have hw : (jetNeighborhood.toTotalSpace L κ).left ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom =
      (jetNeighborhood L κ).hom := CategoryTheory.Over.w _
  have hπ : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom :=
    AlgebraicGeometry.Scheme.relativeSpec_isAffineHom _
  have hp : AlgebraicGeometry.IsAffineHom (jetNeighborhood L κ).hom :=
    AlgebraicGeometry.Scheme.relativeSpec_isAffineHom _
  apply AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top (P := @AlgebraicGeometry.IsClosedImmersion)
    (fun U : Ct.toScheme.AffineZariskiSite =>
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens)
    (AlgebraicGeometry.Scheme.isOpenCover_preimage_affineZariski _)
  intro U
  have hU : AlgebraicGeometry.IsAffineOpen U.toOpens := U.2
  have h1 : AlgebraicGeometry.IsAffine
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens : _) := hU.preimage _
  have h2 : AlgebraicGeometry.IsAffine ((jetNeighborhood.toTotalSpace L κ).left ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens) : _) := by
    have h : AlgebraicGeometry.IsAffineOpen (((jetNeighborhood.toTotalSpace L κ).left ≫
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) ⁻¹ᵁ U.toOpens) := by
      rw [hw]; exact hU.preimage _
    exact h
  apply AlgebraicGeometry.IsClosedImmersion.of_surjective_of_isAffine
  rw [AlgebraicGeometry.morphismRestrict_appTop]
  -- the section map of `f` on `π⁻¹U` is surjective (first replace the open `ι ''ᵁ ⊤` by `π⁻¹U`)
  suffices hsurj₀ : ∀ (W : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
      (hW : W = (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens),
      Function.Surjective ((jetNeighborhood.toTotalSpace L κ).left.app W) by
    have hb : Function.Surjective ((jetNeighborhood L κ).left.presheaf.map
        (CategoryTheory.eqToHom (AlgebraicGeometry.image_morphismRestrict_preimage
          (jetNeighborhood.toTotalSpace L κ).left
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens) ⊤)).op) :=
      (CategoryTheory.ConcreteCategory.bijective_of_isIso _).2
    have ha := hsurj₀ _ (AlgebraicGeometry.Scheme.Opens.ι_image_top _)
    exact hb.comp ha
  intro W hW
  subst hW
  have hsurj : ∀ (V : (jetNeighborhood L κ).left.Opens)
      (hV : V = (jetNeighborhood.toTotalSpace L κ).left ⁻¹ᵁ
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens))
      (e : V ≤ (jetNeighborhood.toTotalSpace L κ).left ⁻¹ᵁ
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens)),
      Function.Surjective ((jetNeighborhood.toTotalSpace L κ).left.appLE
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens) V e) →
      Function.Surjective ((jetNeighborhood.toTotalSpace L κ).left.app
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens)) := by
    intro V hV e h
    subst hV
    rwa [AlgebraicGeometry.Scheme.Hom.app_eq_appLE]
  have hle : (jetNeighborhood L κ).hom ⁻¹ᵁ U.toOpens ≤ (jetNeighborhood.toTotalSpace L κ).left ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U.toOpens) :=
    le_of_eq (by rw [← hw]; rfl)
  refine hsurj ((jetNeighborhood L κ).hom ⁻¹ᵁ U.toOpens) (by rw [← hw]; rfl) hle ?_
  intro y
  obtain ⟨a, ha⟩ := (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_bijective
    (truncatedJetAlgebra L κ) ⟨U.toOpens, U.2⟩).2 y
  obtain ⟨x, hx⟩ := truncatedJetAlgebra.truncation_app_surjective L κ U.toOpens a
  refine ⟨(AlgebraicGeometry.Scheme.relativeSpec.structureHom
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).app U.toOpens x, ?_⟩
  have hC := AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total (jetNeighborhood L κ)
    (truncatedJetAlgebra.truncation L κ ≫
      AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ))
    (jetNeighborhood.truncation_structureHom_isAlgebraMap L κ) U.toOpens x hle
  refine hC.trans ?_
  show (AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app U.toOpens
    ((truncatedJetAlgebra.truncation L κ).app U.toOpens x) = y
  rw [hx]
  exact ha

/-- `τ` followed by the projection onto the `0`-th piece is the augmentation of `Sym`: `τ ≫ π₀ = symAugmentation`
(componentwise: `m = 0` by `symPartToMonoidalPow_zero_eq_symAugmentationZero`, `1 ≤ m ≤ κ` by `biproduct.ι_π_ne`,
`m > κ` both sides are `0`). -/
theorem truncatedJetAlgebra.truncation_comp_π₀ {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    truncatedJetAlgebra.truncation L κ ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩ =
      AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual L.toModules) := by
  refine CategoryTheory.Limits.Sigma.hom_ext _ _ (fun m => ?_)
  have hR := CategoryTheory.Limits.Sigma.ι_desc
    (f := (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part)
    (fun m => match m with
      | 0 => AlgebraicGeometry.Scheme.Modules.symAugmentationZero
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)
      | _ + 1 => (0 : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part _ ⟶ 𝟙_ Ct.toScheme.Modules)) m
  refine Eq.trans ?_ hR.symm
  rw [← CategoryTheory.Category.assoc, truncatedJetAlgebra.ι_truncation]
  cases m with
  | zero =>
    rw [dif_pos (Nat.zero_le κ), CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
      CategoryTheory.Limits.biproduct.ι_π_self, CategoryTheory.Category.comp_id]
    exact (CategoryTheory.Category.comp_id _).trans
      (AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow_zero_eq_symAugmentationZero _)
  | succ m =>
    split_ifs with h
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
        CategoryTheory.Limits.biproduct.ι_π_ne _ (Fin.ne_of_val_ne (Nat.succ_ne_zero m)),
        CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.comp_zero]
      rfl
    · rw [CategoryTheory.Limits.zero_comp]
      rfl

/- Compatibility with the zero sections: `C̃ → C̃_(κ)(L) → Tot(L)` is the zero section of `Tot(L)`. Proof: move to the
   algebra side (the universal property is an `Equiv`, hence injective) and use `ofAlgebraMap_appLE_structureHom`
   twice on sections (for `f`, then for the zero section `ι`), reducing to
   `truncation_comp_π₀ : τ ≫ π₀ = symAugmentation`; Mathlib's `Scheme.Hom.appLE_comp_appLE` splits `(ι ≫ f)^♯`. -/
/-- **Compatibility with the zero sections**: `C̃ →(zero section of the jet neighbourhood) C̃_(κ)(L) →(closed
immersion) Tot(L)` is the zero section of `Tot(L)`.

Source: §3 of the paper (`C̃_(k)(L)` is the `k`-th infinitesimal neighbourhood of the **zero section**; this lemma
formalizes "the two zero sections are the same").

Proof. All three morphisms are over `C̃` and are given by the universal property of the relative Spec, so the
equation can be checked on the side of algebra maps: `relativeSpecHomEquiv (S := Sym(L^∨).total) (T := Over.mk (𝟙 C̃))`
is an `Equiv`, hence injective. The zero section `AlgebraicGeometry.Scheme.zeroSection L.toModules` is by definition
`relativeSpecHomEquiv.symm ⟨symAugmentation, _⟩`, where `symAugmentation` is the augmentation of `Sym` (identity in
degree `0`, zero in positive degrees). The left-hand side is `relativeSpecHomEquiv(A).symm ⟨augmentation, _⟩` followed
by `relativeSpecHomEquiv(S.total).symm ⟨τ ≫ σ_A, _⟩`; by naturality of the universal property in `T`, the composite
corresponds to `τ ≫ augmentation` with `augmentation = biproduct.π ⟨0,_⟩ ≫ (pushforwardId C̃).inv`. Finally
`τ ≫ augmentation = symAugmentation` componentwise (`truncation_comp_π₀`): for `m = 0` the component is
`symPartToMonoidalPow _ 0 ≫ (pieceIso L 0).inv`, which is `symAugmentationZero` since `pieceIso L 0 = Iso.refl` and
`monoidalPow W 0 = 𝟙_`; for `1 ≤ m ≤ κ` both sides vanish by `biproduct.ι_π` (`dif_neg`); for `m > κ` both sides
are `0` by definition. -/
theorem jetNeighborhood.zeroSection_toTotalSpace {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k}
    (L : LineBundle Ct.toVariety) (κ : ℕ) :
    jetNeighborhood.zeroSection L κ ≫ (jetNeighborhood.toTotalSpace L κ).left =
      AlgebraicGeometry.Scheme.zeroSection L.toModules := by
  have hw : (jetNeighborhood.zeroSection L κ ≫ (jetNeighborhood.toTotalSpace L κ).left) ≫
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom =
      (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom := by
    rw [CategoryTheory.Category.assoc, jetNeighborhood.toTotalSpace_proj]
    exact jetNeighborhood.zeroSection_proj L κ
  let h₁ : CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme) ⟶
      AlgebraicGeometry.Scheme.totalSpace L.toModules :=
    CategoryTheory.Over.homMk (jetNeighborhood.zeroSection L κ ≫ (jetNeighborhood.toTotalSpace L κ).left) hw
  have key : h₁ = (AlgebraicGeometry.Scheme.relativeSpecHomEquiv
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total
      (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme))).symm
    ⟨AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual L.toModules) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardId Ct.toScheme).inv.app
          (SheafOfModules.unit Ct.toScheme.ringCatSheaf),
      AlgebraicGeometry.Scheme.Modules.symAugmentation_isAlgebraMap
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)⟩ := by
    apply (AlgebraicGeometry.Scheme.relativeSpecHomEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ (fun U => ?_)
    ext c
    have hle₁ : (jetNeighborhood L κ).hom ⁻¹ᵁ U ≤ (jetNeighborhood.toTotalSpace L κ).left ⁻¹ᵁ
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U) :=
      le_of_eq (by rw [← CategoryTheory.Over.w (jetNeighborhood.toTotalSpace L κ)]; rfl)
    have hle₂ : (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom ⁻¹ᵁ U ≤
        jetNeighborhood.zeroSection L κ ⁻¹ᵁ ((jetNeighborhood L κ).hom ⁻¹ᵁ U) :=
      le_of_eq (by
        show (CategoryTheory.CategoryStruct.id Ct.toScheme) ⁻¹ᵁ U = _
        rw [← jetNeighborhood.zeroSection_proj L κ]; rfl)
    have hB := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (jetNeighborhood.zeroSection L κ)
      (jetNeighborhood.toTotalSpace L κ).left
      ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U) ((jetNeighborhood L κ).hom ⁻¹ᵁ U)
      ((CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom ⁻¹ᵁ U) hle₁ hle₂
    have hC := AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total (jetNeighborhood L κ)
      (truncatedJetAlgebra.truncation L κ ≫
        AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ))
      (jetNeighborhood.truncation_structureHom_isAlgebraMap L κ) U c hle₁
    have hD := AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom
      (truncatedJetAlgebra L κ) (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme))
      (jetNeighborhood.augmentation L κ) (jetNeighborhood.augmentation_isAlgebraMap L κ) U
      ((truncatedJetAlgebra.truncation L κ).app U c) hle₂
    have hE : (jetNeighborhood.augmentation L κ).app U ((truncatedJetAlgebra.truncation L κ).app U c) =
        (AlgebraicGeometry.Scheme.Modules.symAugmentation
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).app U c :=
      congrArg (fun g => g.app U c) (truncatedJetAlgebra.truncation_comp_π₀ L κ)
    -- the left-hand side is by definition `pullbackSections`; split it into `structureRingMap` followed by `(ι ≫ f)^♯`
    have hA0 : CommRingCat.ofHom (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total
        (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)) h₁ U) =
        (AlgebraicGeometry.Scheme.relativeSpec.structureRingMap
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).app (Opposite.op U) ≫
        (jetNeighborhood.zeroSection L κ ≫ (jetNeighborhood.toTotalSpace L κ).left).appLE
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U)
          ((CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom ⁻¹ᵁ U)
          (hle₂.trans ((TopologicalSpace.Opens.map (jetNeighborhood.zeroSection L κ).base).map
            (CategoryTheory.homOfLE hle₁)).le) := rfl
    have hA1 := congrArg (fun ψ : CommRingCat.of ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total.sectionsRing U) ⟶
        CommRingCat.of Γ(Ct.toScheme, (CategoryTheory.Over.mk
          (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom ⁻¹ᵁ U) => ψ.hom c) hA0
    have hS : ((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).app (Opposite.op U)).hom c =
        (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U) from
          (AlgebraicGeometry.Scheme.relativeSpec.structureHom
            (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).app U c) :=
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_apply _ U c).symm
    refine hA1.trans ?_
    refine (congrArg (fun x : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U) =>
        ((jetNeighborhood.zeroSection L κ ≫ (jetNeighborhood.toTotalSpace L κ).left).appLE
          ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U)
          ((CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom ⁻¹ᵁ U)
          (hle₂.trans ((TopologicalSpace.Opens.map (jetNeighborhood.zeroSection L κ).base).map
            (CategoryTheory.homOfLE hle₁)).le)).hom x) hS).trans ?_
    refine (congrArg (fun ψ => ψ.hom (show Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ U) from
        (AlgebraicGeometry.Scheme.relativeSpec.structureHom
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).app U c)) hB.symm).trans ?_
    refine (congrArg (fun x => ((jetNeighborhood.zeroSection L κ).appLE ((jetNeighborhood L κ).hom ⁻¹ᵁ U)
        ((CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom ⁻¹ᵁ U) hle₂).hom x)
        hC).trans ?_
    exact hD.trans hE
  exact congrArg CategoryTheory.CommaMorphism.left key

end
