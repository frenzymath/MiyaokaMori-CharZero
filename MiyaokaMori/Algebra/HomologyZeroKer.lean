import MiyaokaMori.Prelude
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.HomologySequence

/-! # The zeroth cohomology of a cochain complex vanishing in degree `-1`

Let `R` be a ring and `K` a `ℤ`-graded cochain complex of `R`-modules with `K^{-1} = 0`. Then
`H^0(K) ≃ ker (d^0 : K^0 → K^1)` (`R`-linearly), naturally in chain maps `f : K → L` with
`L^{-1} = 0`: `H^0(f)` corresponds to the restriction of `f^0` to the kernels.

The file also contains a purely linear-algebraic "cokernel comparison" lemma,
`LinearMap.nonempty_equiv_quotient_of_exact`.

Reference: standard homological algebra (Weibel, *An introduction to homological algebra*, 1.1;
Mathlib's `HomologicalComplex.isoHomologyπ` and `ShortComplex.moduleCatCyclesIso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- For a cochain complex with `K^{-1} = 0`, `H^0(K)` is `ker d^0`, naturally in chain maps.

Proof sketch: since `K^{-1}` is a zero object, `K.d (-1) 0 = 0` and `K.homologyπ 0 : K.cycles 0 → K.homology 0`
is an isomorphism (`isoHomologyπ`); `K.cycles 0` is identified with the kernel of `K.d 0 1` through
`ShortComplex.moduleCatCyclesIso`. Naturality follows from `homologyπ_naturality` and `cyclesMap_i`.
No assumption on `K^1` is needed (if `K^1 = 0` the kernel is all of `K^0`). -/
theorem CochainComplex.exists_homologyZero_equiv_ker {R : Type u} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℤ} (f : K ⟶ L)
    (hK : IsZero (K.X (-1))) (hL : IsZero (L.X (-1))) :
    ∃ (e : K.homology 0 ≃ₗ[R] LinearMap.ker (K.d 0 1).hom)
      (e' : L.homology 0 ≃ₗ[R] LinearMap.ker (L.d 0 1).hom),
      ∀ x : K.homology 0,
        ((e' ((HomologicalComplex.homologyMap f 0).hom x) : LinearMap.ker (L.d 0 1).hom) : L.X 0) =
          (f.f 0).hom ((e x : LinearMap.ker (K.d 0 1).hom) : K.X 0) := by
  have hp : (ComplexShape.up ℤ).prev 0 = -1 := by simp
  have hn : (ComplexShape.up ℤ).next 0 = 1 := by simp
  -- for any such complex: the isomorphism `E` and its image in `K^0`
  have key : ∀ (M : CochainComplex (ModuleCat.{v} R) ℤ) (hM : IsZero (M.X (-1))),
      ∃ E : M.homology 0 ≅ ModuleCat.of R (LinearMap.ker (M.d 0 1).hom),
        ∀ c : M.cycles 0,
          ((E.hom.hom ((M.homologyπ 0).hom c) : LinearMap.ker (M.d 0 1).hom) : M.X 0) =
            (M.iCycles 0).hom c := by
    intro M hM
    let I := M.isoHomologyπ (-1) 0 hp (hM.eq_of_src _ _)
    let J := M.cyclesIsoSc' (-1) 0 1 hp hn ≪≫ (M.sc' (-1) 0 1).moduleCatCyclesIso
    refine ⟨I.symm ≪≫ J, fun c => ?_⟩
    have h1 : M.homologyπ 0 ≫ I.inv = 𝟙 _ := M.isoHomologyπ_hom_inv_id (-1) 0 hp _
    have h2 : J.hom ≫ (M.sc' (-1) 0 1).moduleCatLeftHomologyData.i = M.iCycles 0 := by
      rw [Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
        HomologicalComplex.cyclesIsoSc'_hom_iCycles]
    have h3 : M.homologyπ 0 ≫ (I.symm ≪≫ J).hom ≫
        (M.sc' (-1) 0 1).moduleCatLeftHomologyData.i = M.iCycles 0 := by
      rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← Category.assoc (M.homologyπ 0), h1,
        Category.id_comp, h2]
    exact congrArg (fun ψ => ψ.hom c) h3
  obtain ⟨EK, hEK⟩ := key K hK
  obtain ⟨EL, hEL⟩ := key L hL
  refine ⟨EK.toLinearEquiv, EL.toLinearEquiv, fun x => ?_⟩
  have hsurj : Function.Surjective (K.homologyπ 0).hom := by
    haveI : IsIso (K.homologyπ 0) := K.isIso_homologyπ (-1) 0 hp (hK.eq_of_src _ _)
    exact (ConcreteCategory.bijective_of_isIso (K.homologyπ 0)).2
  obtain ⟨c, rfl⟩ := hsurj x
  have hnat := congrArg (fun ψ => ψ.hom c) (HomologicalComplex.homologyπ_naturality f 0)
  have hi := congrArg (fun ψ => ψ.hom c) (HomologicalComplex.cyclesMap_i f 0)
  show ((EL.hom.hom ((HomologicalComplex.homologyMap f 0).hom ((K.homologyπ 0).hom c)) :
      LinearMap.ker (L.d 0 1).hom) : L.X 0) = (f.f 0).hom ((EK.hom.hom ((K.homologyπ 0).hom c) :
      LinearMap.ker (K.d 0 1).hom) : K.X 0)
  rw [hEK c]
  refine Eq.trans ?_ hi
  refine Eq.trans ?_ (hEL ((HomologicalComplex.cyclesMap f 0).hom c))
  exact congrArg (fun y => ((EL.hom.hom y : LinearMap.ker (L.d 0 1).hom) : L.X 0)) hnat

/-- Cokernel comparison (pure linear algebra): given `A₂ --a--> A₃ --δ--> B` with `δ` surjective and
`im a = ker δ`, and isomorphisms `e₂ : A₂ ≃ C₂`, `e₃ : A₃ ≃ C₃` transporting `a` to `c`, one has
`B ≃ C₃ / im c`. -/
theorem LinearMap.nonempty_equiv_quotient_of_exact {R : Type*} [Ring R]
    {A₂ A₃ B C₂ C₃ : Type*} [AddCommGroup A₂] [AddCommGroup A₃] [AddCommGroup B]
    [AddCommGroup C₂] [AddCommGroup C₃] [Module R A₂] [Module R A₃] [Module R B] [Module R C₂]
    [Module R C₃] (a : A₂ →ₗ[R] A₃) (δ : A₃ →ₗ[R] B) (hδ : Function.Surjective δ)
    (hex : LinearMap.range a = LinearMap.ker δ) (e₂ : A₂ ≃ₗ[R] C₂) (e₃ : A₃ ≃ₗ[R] C₃)
    (c : C₂ →ₗ[R] C₃) (hc : ∀ x, e₃ (a x) = c (e₂ x)) :
    Nonempty (B ≃ₗ[R] (C₃ ⧸ LinearMap.range c)) := by
  let d : C₃ →ₗ[R] B := δ.comp e₃.symm.toLinearMap
  have hd : Function.Surjective d := hδ.comp e₃.symm.surjective
  have hker : LinearMap.ker d = LinearMap.range c := by
    ext t
    rw [LinearMap.mem_ker, LinearMap.mem_range]
    show δ (e₃.symm t) = 0 ↔ _
    rw [← LinearMap.mem_ker, ← hex, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨e₂ y, by rw [← hc, hy, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨s, hs⟩
      exact ⟨e₂.symm s, e₃.injective (by rw [hc, LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply, hs])⟩
  exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans (d.quotKerEquivOfSurjective hd)).symm⟩

end
