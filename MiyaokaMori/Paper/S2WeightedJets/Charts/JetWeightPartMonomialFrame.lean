import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfFreeAffineSections
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetGradedAlgebraLocalWeightedChart
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra

/-! # The monomial frame of a graded piece of the jet algebra

On an affine open `U` on which `s^*T_{Z/C}` is trivialized as `O_U^{n+1}`, the pullback of the
graded piece `weightPart j` of the jet algebra is isomorphic to the free sheaf with the monomials of
weight `j` as basis (§2.2 of the paper: "each `(𝒮_k)_m` is locally free, with local basis the
monomials of weight `m`"; Demailly, *Holomorphic Morse inequalities and the Green–Griffiths–Lang
conjecture*, (0.3)).

Proof:
1. `jetGradedAlgebra_localWeightedChart_of_smooth` (which needs `s` to land in an open `Zx ⊆ Z`
   smooth of relative dimension `n+1` over `C` — without this hypothesis the statement is false, see
   the cusp counterexample in that module) gives a ring isomorphism `e` from the sections ring
   `⊕_m Γ(U, S_m)` of the graded algebra on `U` to the weighted polynomial ring `Γ(U,O)[x_(i,q)]`
   (`x_(i,q)` of weight `q+1`), the `m`-th piece corresponding to the homogeneous polynomials of
   weight `m` and the structure map to `MvPolynomial.C`.
2. `GradedQCAlgebra.pieceLinearEquivOfChart` (this file): `Γ(U, S_j) ≃ₗ[Γ(U,O)] weightedHomogeneousSubmodule j`.
   The map `Γ(U, S_j) → ⊕_m Γ(U, S_m)` is `DirectSum.of` (`ofPiece`), whose image is exactly the `j`-th
   piece `sectionsGrading U j` (`sectionsPieceEquivGrading`); `Γ(U,O)`-linearity follows from
   `sectionsUnitHom_mul_ofPiece` (`r • a ↦ unit(r) * a`), `e (unit r) = C r` and `r • p = C r * p`.
3. `MvPolynomial.weightedHomogeneousBasis` (this file): `weightedHomogeneousSubmodule R w j` has the
   monomial basis indexed by `{d | weight w d = j}` (Mathlib's
   `weightedHomogeneousSubmodule_eq_finsupp_supported` + `basisRestrictSupport`). Composing gives a
   basis of `Γ(U, S_j)`; `Finsupp.weightIndexULiftEquiv` changes the index set from
   `ULift (Fin(n+1) × Fin r) →₀ ℕ` to the `ULift {m : (Fin(n+1) × Fin r) →₀ ℕ | weight m = j}` of the
   statement.
4. `Scheme.Modules.pullback_iso_free_of_basis` (this file): if `Γ(U, M)` has a basis `ι` for a
   quasi-coherent sheaf on an affine open `U`, then `U.ι^* M ≅ O_U^{(ι)}`
   (Stacks 01IB: `M|_{Spec Γ(U,O)} ≅ (Γ(U,M))~`, then `tildeFinsupp`). Quasi-coherence of `S_j` is a
   field of `GradedQCAlgebra`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The monomials of weight `j` form a basis of `weightedHomogeneousSubmodule R w j`. -/
def MvPolynomial.weightedHomogeneousBasis (R : Type*) [CommRing R] {σ : Type*} (w : σ → ℕ) (j : ℕ) :
    Module.Basis {d : σ →₀ ℕ | Finsupp.weight w d = j} R
      (MvPolynomial.weightedHomogeneousSubmodule R w j) :=
  (MvPolynomial.basisRestrictSupport R {d | Finsupp.weight w d = j}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported R w j).symm)

theorem Finsupp.weight_equivMapDomain {α β M : Type*} [AddCommMonoid M] (f : α ≃ β) (w : β → M)
    (d : α →₀ ℕ) :
    Finsupp.weight w (Finsupp.equivMapDomain f d) = Finsupp.weight (w ∘ f) d :=
  Finsupp.linearCombination_equivMapDomain (R := ℕ) f d

/-- Transport the index set from weight-`j` exponents on `ULift τ` to those on `τ` (lifted once more
with `ULift`, to match the universe of the statement). -/
def Finsupp.weightIndexULiftEquiv {τ : Type v} (w : τ → ℕ) (j : ℕ) :
    {d : ULift.{u} τ →₀ ℕ | Finsupp.weight (fun i : ULift.{u} τ => w i.down) d = j} ≃
      ULift.{u} {m : τ →₀ ℕ | Finsupp.weight w m = j} :=
  (Equiv.subtypeEquiv (Finsupp.domCongr (M := ℕ) Equiv.ulift).toEquiv (fun d => by
    show Finsupp.weight (fun i : ULift.{u} τ => w i.down) d = j ↔
      Finsupp.weight w (Finsupp.equivMapDomain Equiv.ulift d) = j
    rw [Finsupp.weight_equivMapDomain]
    rfl)).trans Equiv.ulift.symm

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

attribute [local instance] AlgebraicGeometry.Scheme.GradedQCAlgebra.sectionsPieceModule_ofGradedQCAlgebra


/-- The sections of the `j`-th piece are the homogeneous polynomials of weight `j`
(`Γ(X,U)`-linearly). -/
def pieceLinearEquivOfChart (U : X.Opens) {σ : Type u} (w : σ → ℕ)
    (e : S.sectionsRing U ≃+* MvPolynomial σ Γ(X, U))
    (hgr : ∀ (m : ℕ) (a : S.sectionsRing U),
      a ∈ S.sectionsGrading U m ↔ (e a).IsWeightedHomogeneous w m)
    (hunit : ∀ a : Γ(X, U), e (S.sectionsUnitHom U a) = MvPolynomial.C a)
    (j : ℕ) :
    S.sectionsPiece U j ≃ₗ[Γ(X, U)] MvPolynomial.weightedHomogeneousSubmodule Γ(X, U) w j where
  toFun a := ⟨e (S.ofPiece U j a), (hgr j _).1 (S.ofPiece_mem_sectionsGrading U j a)⟩
  invFun p := S.component U j (e.symm p.1)
  left_inv a := by
    show S.component U j (e.symm (e (S.ofPiece U j a))) = a
    rw [RingEquiv.symm_apply_apply]
    exact S.component_ofPiece U j a
  right_inv p := by
    apply Subtype.ext
    show e (S.ofPiece U j (S.component U j (e.symm p.1))) = p.1
    have hmem : e.symm p.1 ∈ S.sectionsGrading U j := by
      refine (hgr j (e.symm p.1)).2 ?_
      rw [RingEquiv.apply_symm_apply]
      exact p.2
    rw [(S.mem_sectionsGrading_iff U j (e.symm p.1)).1 hmem, RingEquiv.apply_symm_apply]
  map_add' a b := by
    apply Subtype.ext
    show e (S.ofPiece U j (a + b)) = e (S.ofPiece U j a) + e (S.ofPiece U j b)
    exact (congrArg e (map_add (DirectSum.of (S.sectionsPiece U) j) a b)).trans (map_add e _ _)
  map_smul' r a := by
    apply Subtype.ext
    show e (S.ofPiece U j (r • a)) = r • e (S.ofPiece U j a)
    have h1 : S.ofPiece U j (r • a) = S.sectionsUnitHom U r * S.ofPiece U j a :=
      (S.sectionsUnitHom_mul_ofPiece U r a).symm
    calc e (S.ofPiece U j (r • a)) = e (S.sectionsUnitHom U r * S.ofPiece U j a) := congrArg e h1
      _ = e (S.sectionsUnitHom U r) * e (S.ofPiece U j a) := map_mul e _ _
      _ = MvPolynomial.C r * e (S.ofPiece U j a) := congrArg (· * e (S.ofPiece U j a)) (hunit r)
      _ = r • e (S.ofPiece U j a) := (MvPolynomial.smul_eq_C_mul _ _).symm

/-- The monomial basis of the sections of the `j`-th piece. -/
def pieceBasisOfChart (U : X.Opens) {σ : Type u} (w : σ → ℕ)
    (e : S.sectionsRing U ≃+* MvPolynomial σ Γ(X, U))
    (hgr : ∀ (m : ℕ) (a : S.sectionsRing U),
      a ∈ S.sectionsGrading U m ↔ (e a).IsWeightedHomogeneous w m)
    (hunit : ∀ a : Γ(X, U), e (S.sectionsUnitHom U a) = MvPolynomial.C a)
    (j : ℕ) :
    Module.Basis {d : σ →₀ ℕ | Finsupp.weight w d = j} Γ(X, U) Γ(S.part j, U) :=
  (MvPolynomial.weightedHomogeneousBasis Γ(X, U) w j).map (S.pieceLinearEquivOfChart U w e hgr hunit j).symm

/-- Conversion from the chart data (the types are definitionally equal; only the spelling changes). -/
def pieceBasisOfAffineChart (U : X.affineOpens) {σ : Type u} (w : σ → ℕ)
    (e : S.toGradedAffineAlgebra.toAffineAlgebra.sections (AlgebraicGeometry.Scheme.affineSite U) ≃+*
      MvPolynomial σ Γ(X, U.1))
    (hgr : ∀ (m : ℕ) (a : S.toGradedAffineAlgebra.toAffineAlgebra.sections (AlgebraicGeometry.Scheme.affineSite U)),
      a ∈ S.toGradedAffineAlgebra.grading (AlgebraicGeometry.Scheme.affineSite U) m ↔
        (e a).IsWeightedHomogeneous w m)
    (hunit : ∀ a : Γ(X, U.1),
      e (S.toGradedAffineAlgebra.toAffineAlgebra.unitHom (AlgebraicGeometry.Scheme.affineSite U) a) =
        MvPolynomial.C a)
    (j : ℕ) :
    Module.Basis {d : σ →₀ ℕ | Finsupp.weight w d = j} Γ(X, U.1) Γ(S.part j, U.1) :=
  S.pieceBasisOfChart U.1 w (show S.sectionsRing U.1 ≃+* MvPolynomial σ Γ(X, U.1) from e) hgr hunit j

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-! ## A basis of the sections on an affine open gives a free pullback -/

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry

theorem spec_iso_free_of_basis {R : CommRingCat.{u}} (N : (Spec R).Modules) [N.IsQuasicoherent]
    (ι : Type u) (b : Module.Basis ι R ((modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤))) :
    Nonempty (N ≅ SheafOfModules.free (R := (Spec R).ringCatSheaf) ι) := by
  have : IsIso N.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let P := (modulesSpecToSheaf.obj N).presheaf.obj (.op ⊤)
  let l : P ≅ ModuleCat.of R (ι →₀ R) := b.repr.toModuleIso
  exact ⟨(asIso N.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso l ≪≫ tildeFinsupp ι⟩

theorem basis_restrict_fromSpec {X : Scheme.{u}} (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (ι : Type u) (b : Module.Basis ι Γ(X, U) Γ(M, U)) :
    Nonempty (Module.Basis ι Γ(X, U) Γ(M.restrict hU.fromSpec, ⊤)) := by
  have hV : hU.fromSpec ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let e : Γ(X, U) ≃+* Γ(X, U) :=
    ((X.presheaf.mapIso (eqToIso hV).op) ≪≫ (hU.fromSpec.appIso ⊤) ≪≫
      Scheme.ΓSpecIso Γ(X, U)).commRingCatIsoToRingEquiv
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  have key : ∀ (r : Γ(X, hU.fromSpec ''ᵁ ⊤)) (y : Γ(M, hU.fromSpec ''ᵁ ⊤)),
      (M.restrictAppIso hU.fromSpec ⊤).inv (r • y) =
        ((hU.fromSpec.appIso ⊤).hom r) • (M.restrictAppIso hU.fromSpec ⊤).inv y := fun r y => by
    have := Scheme.Modules.smul_restrictAppIso_inv_apply hU.fromSpec M ⊤ r y
    exact this
  let g : Γ(M, U) →ₛₗ[(e : Γ(X, U) →+* Γ(X, U))] Γ(M.restrict hU.fromSpec, ⊤) :=
    { toFun := fun m => (M.restrictAppIso hU.fromSpec ⊤).inv (M.presheaf.map (eqToHom hV).op m)
      map_add' := fun a b => by simp
      map_smul' := fun a m => by
        rw [Scheme.Modules.map_smul, key, Scheme.Modules.smul_Spec_def]
        congr 1
        simp only [e]
        have h1 : (TopologicalSpace.Opens.leTop (⊤ : (Spec Γ(X, U)).Opens)).op = 𝟙 _ := Subsingleton.elim _ _
        rw [h1, CategoryTheory.Functor.map_id]
        simp [Iso.commRingCatIsoToRingEquiv] }
  have hg : Function.Bijective g :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hU.fromSpec ⊤).inv).comp
      (ConcreteCategory.bijective_of_isIso (M.presheaf.map (eqToHom hV).op))
  exact MiyaokaMori.basis_of_semilinearEquiv (LinearEquiv.ofBijective g hg) b

theorem restrict_fromSpec_iso_free_of_basis {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (ι : Type u) (b : Module.Basis ι Γ(X, U) Γ(M, U)) :
    Nonempty (M.restrict hU.fromSpec ≅ SheafOfModules.free (R := (Spec Γ(X, U)).ringCatSheaf) ι) := by
  obtain ⟨b'⟩ := basis_restrict_fromSpec M hU ι b
  exact spec_iso_free_of_basis (M.restrict hU.fromSpec) ι b'

theorem pullback_iso_free_of_basis {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (ι : Type u) (b : Module.Basis ι Γ(X, U) Γ(M, U)) :
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) ι) := by
  obtain ⟨ψ⟩ := restrict_fromSpec_iso_free_of_basis M hU ι b
  let F : SheafOfModules.{u} (Spec Γ(X, U)).ringCatSheaf ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor hU.isoSpec.hom
  have hF : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction hU.isoSpec.hom).leftAdjoint_preservesColimits.{u, u}
  have : Limits.PreservesColimitsOfShape (Discrete ι) F := hF.preservesColimitsOfShape
  exact ⟨((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).symm.app M ≪≫
    (Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M ≪≫
    F.mapIso ψ ≪≫
    (SheafOfModules.mapFreeIso F ι (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm).symm⟩

end AlgebraicGeometry.Scheme.Modules

/-! ## The main theorem -/

theorem jetWeightPart_pullback_iso_free_of_trivial
    {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) (s : C.toScheme ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s] [AlgebraicGeometry.IsAffineHom Z.hom]
    (Zx : Z.left.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)]
    (r j : ℕ) (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj
      (coneTangentBundle Z.hom s hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
        (ULift.{u} (Fin (n + 1))))) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj
        ((jetGradedAlgebra (k := k) Z s hs r).1.part j) ≅
      AlgebraicGeometry.Scheme.Modules.free
        (ULift.{u} {m : (Fin (n + 1) × Fin r) →₀ ℕ |
          Finsupp.weight (fun iq ↦ ((iq.2 : ℕ) + 1)) m = j})) := by
  obtain ⟨e, hgr, hunit⟩ :=
    jetGradedAlgebra_localWeightedChart_of_smooth (k := k) Z s hs Zx hsZx n r U htriv
  let S : C.toScheme.GradedQCAlgebra := (jetGradedAlgebra (k := k) Z s hs r).1
  have : (S.part j).IsQuasicoherent := S.quasicoherent j
  let b := S.pieceBasisOfAffineChart U (fun iq : ULift.{u} (Fin (n + 1) × Fin r) ↦ (iq.down.2 : ℕ) + 1)
    e hgr hunit j
  exact AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_basis (S.part j) U.2 _
    (b.reindex (Finsupp.weightIndexULiftEquiv.{u} (fun iq : Fin (n + 1) × Fin r ↦ ((iq.2 : ℕ) + 1)) j))

end
