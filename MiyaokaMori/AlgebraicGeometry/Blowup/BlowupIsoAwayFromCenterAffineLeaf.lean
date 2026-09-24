import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjToSpecZeroIsoOfDegreeOneGenerator

/-! # The chart of the blowup over an affine open where the ideal is trivial

The affine-local form of Stacks 02OS(1) (the blowup is an isomorphism away from the centre): on an
affine open `U` on which the ideal sheaf is the unit ideal, the chart structure map `Proj S(U) → U` of
the relative Proj of the Rees algebra `S = ⊕ Iⁿ` is an isomorphism.

Source: Stacks 02OS(1) (proof: "the first statement just means that X' = X if Z = ∅"), via
Stacks 01MI (`Proj A[T] = Spec A`).

Route: instead of building the graded ring isomorphism `S(U) ≅ Γ(X,U)[T]`, we use the abstract form of
01MI (`Proj.isIso_toSpecZero_of_degreeOne_generator`: `Proj.toSpecZero 𝒜` is an isomorphism as soon as
some `t ∈ 𝒜 1` multiplies `𝒜 n` bijectively onto `𝒜 (n+1)`), applied to `t := 1 ∈ I(U)^1 = Γ(X,U)`.
The only Rees-specific input is the multiplication formula `coe_reesAlgebra_sectionsGMul`: the graded
multiplication of `I.reesAlgebra` on sections is the multiplication of `Γ(X,U)` (this unwinds
`powMul = liftPow (powMulToUnit)` on `tensorSections` through `Modules.tensorHom_tensorSections` and
`Modules.leftUnitor_app_tensorSections`).

Also here: two lemmas about `IdealSheafData.ideal` being the unit ideal on affine opens disjoint from
the support, used both by this proof and by the locality argument in `BlowupIsoAwayFromCenter`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

/-- On an affine open `U` disjoint from the support of `I`, `I(U)` is the unit ideal.
Proof: `I.support ∩ U = V(I(U)) ∩ U` (`coe_support_inter`), and `hU.fromSpec` maps
`PrimeSpectrum.zeroLocus (I(U))` onto `V(I(U)) ∩ U` (`fromSpec_image_zeroLocus`); if the latter is
empty so is the former, and `PrimeSpectrum.zeroLocus_empty_iff_eq_top` finishes. -/
theorem Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens)
    (hU : Disjoint (U.1 : Set X) (I.support : Set X)) : I.ideal U = ⊤ := by
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  have h := I.coe_support_inter U
  rw [Set.disjoint_iff_inter_eq_empty.mp hU.symm] at h
  have h2 := U.2.fromSpec_image_zeroLocus (I.ideal U : Set Γ(X, U.1))
  rw [← h] at h2
  exact Set.image_eq_empty.mp h2

/-- If `I(U) = ⊤` on an affine open `U`, then `U` is disjoint from the support of `I`
(`coe_support_inter` with `V(⊤) = ∅`). -/
theorem Scheme.IdealSheafData.disjoint_support_of_ideal_eq_top {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (hU : I.ideal U = ⊤) :
    Disjoint (U.1 : Set X) (I.support : Set X) := by
  rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm, I.coe_support_inter U, hU,
    Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hxU⟩
  have h1 := (X.mem_zeroLocus_iff _ x).mp hx 1 Submodule.mem_top
  rw [X.basicOpen_of_isUnit isUnit_one] at h1
  exact h1 hxU

/-- If `I(U) = ⊤` on an affine open `U`, then `I(V) = ⊤` for every affine open `V ≤ U`. -/
theorem Scheme.IdealSheafData.ideal_eq_top_of_le_of_ideal_eq_top {X : Scheme.{u}}
    (I : X.IdealSheafData) {U V : X.affineOpens} (hV : V.1 ≤ U.1) (hU : I.ideal U = ⊤) :
    I.ideal V = ⊤ :=
  I.ideal_eq_top_of_disjoint_support V
    ((I.disjoint_support_of_ideal_eq_top U hU).mono_left (fun _ h => hV h))

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The monoidal unit of `X.Modules` on sections

`monoidalUnitIso X : 𝟙_ X.Modules ≅ SheafOfModules.unit X.ringCatSheaf` is `eqToIso` of a
definitional equality (`ReesAlgebraSheaf.lean`), so on sections both directions are the identity
of `Γ(X, U)` and the scalar action of `Γ(X, U)` on `Γ(𝟙_ X.Modules, U)` is the ring
multiplication. All three are `rfl` after unfolding everything (K-like reduction of `Eq.rec`). -/

theorem monoidalUnitIso_hom_app (U : X.Opens) (x : Γ(𝟙_ X.Modules, U)) :
    ((monoidalUnitIso X).hom.val.app (op U) x : Γ(X, U)) = x := by
  with_unfolding_all rfl

theorem monoidalUnitIso_inv_app (U : X.Opens) (x : Γ(X, U)) :
    ((monoidalUnitIso X).inv.val.app (op U) x : Γ(X, U)) = x := by
  with_unfolding_all rfl

theorem smul_monoidalUnit_eq_mul (U : X.Opens) (r : Γ(X, U)) (a : Γ(𝟙_ X.Modules, U)) :
    ((r • a : Γ(𝟙_ X.Modules, U)) : Γ(X, U)) = r * (show Γ(X, U) from a) := by
  with_unfolding_all rfl

/-! ### The Rees algebra on sections -/

/-- If `I(U) = ⊤` on the affine open `U`, every section of `O_X` over `U` lies in `Γ(U, Iᵐ)`:
by `ideal_eq_top_of_le_of_ideal_eq_top` all `I(V)`, `V ≤ U` affine, are the unit ideal, so the
defining condition of `powSubmodule m` is vacuous. -/
theorem mem_powSubmodule_of_ideal_eq_top (U : X.AffineZariskiSite)
    (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) (m : ℕ) (s : Γ(X, U.toOpens)) :
    s ∈ (I.powSubmodule m).obj (op U.toOpens) := by
  intro V hV
  have h : I.ideal V = ⊤ := I.ideal_eq_top_of_le_of_ideal_eq_top (U := ⟨U.toOpens, U.2⟩) hV hU
  rw [h, Ideal.top_pow]
  exact Submodule.mem_top

/-- The inclusion `Iᵐ ↪ O_X` on sections is the subtype inclusion. -/
theorem powι_app (U : X.Opens) (m : ℕ) (a : I.reesAlgebra.sectionsPiece U m) :
    ((I.powι m).val.app (op U) a : Γ(X, U)) = a.1 := rfl

/-- **The graded multiplication of the Rees algebra is the ring multiplication.** For
`a ∈ Γ(U, Iᵐ)`, `b ∈ Γ(U, Iⁿ)` the product `sectionsGMul a b ∈ Γ(U, Iᵐ⁺ⁿ)` has underlying section
`a · b`. Proof: `sectionsGMul a b = (powMul m n).app U (a ⊗ b)`, `powMul = liftPow (powMulToUnit)`,
so the underlying section is `powMulToUnit m n (a ⊗ b)`; unwind
`powMulToUnit = (powι ⊗ powι) ≫ (ε⁻¹ ⊗ ε⁻¹) ≫ (λ_ 𝟙_).hom ≫ ε` on the pure tensor with
`Modules.tensorHom_tensorSections` (twice), `Modules.leftUnitor_app_tensorSections`
(`r ⊗ a ↦ r • a`), and the three lemmas above on `ε = monoidalUnitIso X`. -/
theorem coe_reesAlgebra_sectionsGMul (U : X.Opens) (m n : ℕ)
    (a : I.reesAlgebra.sectionsPiece U m) (b : I.reesAlgebra.sectionsPiece U n) :
    ((I.reesAlgebra.sectionsGMul U a b).1 : Γ(X, U)) =
      (show Γ(X, U) from a.1) * (show Γ(X, U) from b.1) := by
  have e1 := Modules.tensorHom_tensorSections (I.powι m) (I.powι n) U a b
  have e2 := Modules.tensorHom_tensorSections (monoidalUnitIso X).inv (monoidalUnitIso X).inv U
    ((I.powι m).val.app (op U) a) ((I.powι n).val.app (op U) b)
  have e3 := Modules.leftUnitor_app_tensorSections (𝟙_ X.Modules) U
    ((monoidalUnitIso X).inv.val.app (op U) ((I.powι m).val.app (op U) a))
    ((monoidalUnitIso X).inv.val.app (op U) ((I.powι n).val.app (op U) b))
  have h0 : ((I.reesAlgebra.sectionsGMul U a b).1 : Γ(X, U)) =
      (I.powMulToUnit m n).val.app (op U) (Modules.tensorSections (I.pow m) (I.pow n) U a b) := rfl
  have h1 : (I.powMulToUnit m n).val.app (op U) (Modules.tensorSections (I.pow m) (I.pow n) U a b) =
      (monoidalUnitIso X).hom.val.app (op U) ((λ_ (𝟙_ X.Modules)).hom.val.app (op U)
        (((monoidalUnitIso X).inv ⊗ₘ (monoidalUnitIso X).inv).val.app (op U)
          ((I.powι m ⊗ₘ I.powι n).val.app (op U)
            (Modules.tensorSections (I.pow m) (I.pow n) U a b)))) := rfl
  rw [h0, h1, e1, e2]
  have e3' : (λ_ (𝟙_ X.Modules)).hom.val.app (op U)
      (Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) U
        ((monoidalUnitIso X).inv.val.app (op U) ((I.powι m).val.app (op U) a))
        ((monoidalUnitIso X).inv.val.app (op U) ((I.powι n).val.app (op U) b))) =
      (show Γ(X, U) from (monoidalUnitIso X).inv.val.app (op U) ((I.powι m).val.app (op U) a)) •
        (show Γ(𝟙_ X.Modules, U) from
          (monoidalUnitIso X).inv.val.app (op U) ((I.powι n).val.app (op U) b)) := e3
  rw [e3']
  refine (monoidalUnitIso_hom_app U _).trans ?_
  refine (smul_monoidalUnit_eq_mul U _ _).trans ?_
  exact congrArg₂ (fun x y : Γ(X, U) => x * y)
    ((monoidalUnitIso_inv_app U ((I.powι m).val.app (op U) a)).trans (I.powι_app U m a))
    ((monoidalUnitIso_inv_app U ((I.powι n).val.app (op U) b)).trans (I.powι_app U n b))

/-! ### `S(U) = Γ(X,U)[T]` when `I(U) = ⊤` -/

/-- The element of the `m`-th Rees piece `Γ(U, Iᵐ)` with a prescribed underlying section
(every section qualifies when `I(U) = ⊤`). -/
def reesPieceMk (U : X.AffineZariskiSite) (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) (m : ℕ)
    (s : Γ(X, U.toOpens)) : I.reesAlgebra.sectionsPiece U.toOpens m :=
  ⟨s, I.mem_powSubmodule_of_ideal_eq_top U hU m s⟩

/-- The degree-one generator `T := 1 ∈ Γ(U, I¹) = Γ(X, U)` of `S(U) = ⊕ₙ Γ(U, Iⁿ)`. -/
def reesGen (U : X.AffineZariskiSite) (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) :
    I.reesAlgebra.sectionsRing U.toOpens :=
  I.reesAlgebra.ofPiece U.toOpens 1 (I.reesPieceMk U hU 1 1)

theorem reesGen_mem (U : X.AffineZariskiSite) (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) :
    I.reesGen U hU ∈ I.reesAlgebra.toGradedAffineAlgebra.grading U 1 :=
  ⟨_, rfl⟩

/-- `(a Tᵐ) · T = a Tᵐ⁺¹` (`DirectSum.of_mul_of` + `coe_reesAlgebra_sectionsGMul`). -/
theorem reesAlgebra_ofPiece_mul_reesGen (U : X.AffineZariskiSite)
    (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) (m : ℕ) (a : I.reesAlgebra.sectionsPiece U.toOpens m) :
    I.reesAlgebra.ofPiece U.toOpens m a * I.reesGen U hU =
      I.reesAlgebra.ofPiece U.toOpens (m + 1) (I.reesPieceMk U hU (m + 1) a.1) := by
  refine (DirectSum.of_mul_of (A := I.reesAlgebra.sectionsPiece U.toOpens) a _).trans ?_
  refine congrArg (DirectSum.of _ (m + 1)) ?_
  apply Subtype.ext
  refine (I.coe_reesAlgebra_sectionsGMul U.toOpens m 1 a _).trans ?_
  exact mul_one (show Γ(X, U.toOpens) from a.1)

/-- Multiplication by `T` is injective on `S(U)ₙ`. -/
theorem reesAlgebra_mul_reesGen_injective (U : X.AffineZariskiSite)
    (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) (n : ℕ) (x : I.reesAlgebra.sectionsRing U.toOpens)
    (hx : x ∈ I.reesAlgebra.sectionsGrading U.toOpens n) (h : x * I.reesGen U hU = 0) : x = 0 := by
  obtain ⟨a, rfl⟩ := hx
  have h' : I.reesAlgebra.ofPiece U.toOpens (n + 1) (I.reesPieceMk U hU (n + 1) a.1) = 0 :=
    (I.reesAlgebra_ofPiece_mul_reesGen U hU n a).symm.trans h
  have ha : I.reesPieceMk U hU (n + 1) a.1 = 0 := by
    apply DirectSum.of_injective (β := I.reesAlgebra.sectionsPiece U.toOpens) (n + 1)
    rw [map_zero]; exact h'
  have ha0 : (a.1 : Γ(X, U.toOpens)) = 0 := congrArg Subtype.val ha
  have ha1 : a = 0 := Subtype.ext ha0
  rw [ha1]; exact map_zero _

/-- Multiplication by `T` maps `S(U)ₙ` onto `S(U)ₙ₊₁`. -/
theorem reesAlgebra_mul_reesGen_surjective (U : X.AffineZariskiSite)
    (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) (n : ℕ) (y : I.reesAlgebra.sectionsRing U.toOpens)
    (hy : y ∈ I.reesAlgebra.sectionsGrading U.toOpens (n + 1)) :
    ∃ x ∈ I.reesAlgebra.sectionsGrading U.toOpens n, x * I.reesGen U hU = y := by
  obtain ⟨c, rfl⟩ := hy
  refine ⟨I.reesAlgebra.ofPiece U.toOpens n (I.reesPieceMk U hU n c.1), ⟨_, rfl⟩, ?_⟩
  refine (I.reesAlgebra_ofPiece_mul_reesGen U hU n _).trans ?_
  refine congrArg (DirectSum.of _ (n + 1)) ?_
  exact Subtype.ext rfl

/-- The structure map `Γ(X, U) → S(U)₀` is `r ↦ r T⁰` (the unit `powOne = liftPow 0 ε.hom` is the
identity on sections by `monoidalUnitIso_hom_app`). -/
theorem coe_reesAlgebra_unitZero (U : X.AffineZariskiSite) (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤)
    (r : Γ(X, U.toOpens)) :
    (I.reesAlgebra.toGradedAffineAlgebra.unitZero U r).1 =
      DirectSum.of (I.reesAlgebra.sectionsPiece U.toOpens) 0 (I.reesPieceMk U hU 0 r) := by
  refine congrArg (DirectSum.of _ 0) ?_
  exact Subtype.ext (monoidalUnitIso_hom_app U.toOpens r)

/-- `Γ(X, U) → S(U)₀` is bijective when `I(U) = ⊤` (`n = 0` needs no hypothesis in fact, but the
statement is only used under `hU`). -/
theorem reesAlgebra_unitZero_bijective (U : X.AffineZariskiSite)
    (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) :
    Function.Bijective (I.reesAlgebra.toGradedAffineAlgebra.unitZero U) := by
  constructor
  · intro r s hrs
    have h := congrArg Subtype.val hrs
    rw [I.coe_reesAlgebra_unitZero U hU, I.coe_reesAlgebra_unitZero U hU] at h
    exact congrArg Subtype.val
      (DirectSum.of_injective (β := I.reesAlgebra.sectionsPiece U.toOpens) 0 h)
  · rintro ⟨y, c, rfl⟩
    refine ⟨c.1, Subtype.ext ?_⟩
    exact (I.coe_reesAlgebra_unitZero U hU c.1).trans
      (congrArg (DirectSum.of (I.reesAlgebra.sectionsPiece U.toOpens) 0)
        (Subtype.ext rfl : I.reesPieceMk U hU 0 c.1 = c))

end Scheme.IdealSheafData

/-- **Leaf** (Stacks 02OS(1) on an affine chart, via Stacks 01MI). Let `I` be an ideal sheaf on `X`
and `U` an affine open with `I(U) = ⊤`. Then the chart structure map
`projToOpen U : Proj S(U) ⟶ U` of the relative Proj of the Rees algebra `S = I.reesAlgebra`
(so `S.toGradedAffineAlgebra.relativeProj = Scheme.blowup I`, by definition) is an isomorphism.

Here `projToOpen U = Proj.toSpecZero (S(U)) ≫ Spec.map (unitZero U) ≫ U.isoSpec.inv`,
`S(U) = I.reesAlgebra.sectionsRing U = ⊕ₙ Γ(U, I.pow n)` with grading `sectionsGrading U`, and
`Γ(U, I.pow n) = { s ∈ Γ(X, U) | ∀ affine V ≤ U, s|_V ∈ I(V)^n }` (`powSubmodule` in
`ReesAlgebraSheaf`).

**Proof.**
1. *All `I(V)` are the unit ideal.* For every affine `V ≤ U`, `I(V) = ⊤`
   (`ideal_eq_top_of_le_of_ideal_eq_top`), hence `I(V)^n = ⊤`, hence every section of `O_X` over
   `U` lies in every `Γ(U, I.pow n)` (`mem_powSubmodule_of_ideal_eq_top`).
2. *The multiplication is the ring multiplication* (`coe_reesAlgebra_sectionsGMul`). Therefore,
   with `T := 1 ∈ Γ(U, I.pow 1)` (`reesGen`), multiplication by `T` maps `S(U)ₙ = Γ(U, I.pow n)`
   bijectively onto `S(U)ₙ₊₁` (`reesAlgebra_mul_reesGen_injective/surjective`): `S(U) = Γ(X,U)[T]`.
3. *Stacks 01MI in abstract form* (`Proj.isIso_toSpecZero_of_degreeOne_generator`): `D₊(T) = Proj S(U)` and
   `(S(U)_T)₀ = S(U)₀`, so `Proj.toSpecZero (S(U))` is an isomorphism.
4. `unitZero U : Γ(X, U) → S(U)₀` is bijective (`reesAlgebra_unitZero_bijective`), so
   `Spec.map (unitZero U)` is an isomorphism; `U.isoSpec.inv` is one; hence so is `projToOpen U`.

Edge cases: `U = ∅` (zero ring): both `Proj` and `Spec` are empty, the statement holds; `I = ⊤`
globally: every chart is covered. -/
theorem Scheme.IdealSheafData.isIso_reesAlgebra_projToOpen_of_ideal_eq_top {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.AffineZariskiSite) (hU : I.ideal ⟨U.toOpens, U.2⟩ = ⊤) :
    IsIso (I.reesAlgebra.toGradedAffineAlgebra.projToOpen U) := by
  have h1 : IsIso (Proj.toSpecZero (I.reesAlgebra.toGradedAffineAlgebra.grading U)) :=
    Proj.isIso_toSpecZero_of_degreeOne_generator _ (I.reesGen_mem U hU)
      (I.reesAlgebra_mul_reesGen_injective U hU) (I.reesAlgebra_mul_reesGen_surjective U hU)
  have h2 : IsIso (CommRingCat.ofHom (I.reesAlgebra.toGradedAffineAlgebra.unitZero U)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (I.reesAlgebra_unitZero_bijective U hU)
  unfold GradedAffineAlgebra.projToOpen
  infer_instance


end AlgebraicGeometry

end
