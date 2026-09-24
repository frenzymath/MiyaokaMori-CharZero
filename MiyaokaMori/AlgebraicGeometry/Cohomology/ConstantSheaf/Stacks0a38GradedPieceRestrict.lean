import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.Stacks0a38GradedPieceStalk

/-! # The restriction maps `j_!ℤ_W ⟶ j_!ℤ_V` (`W ≤ V`) and gluing along covers

For opens `W ≤ V` of `X`, the canonical inclusions `c_W : j_!ℤ_W ⟶ ℤ_X` and `c_V : j_!ℤ_V ⟶ ℤ_X`
(`constantInclusion`) are monomorphisms and `c_W` factors through `c_V`: the restriction map
`ρ_{W,V} := extendByZeroConstantRestrict h : j_!ℤ_W ⟶ j_!ℤ_V` is the unique morphism with
`ρ_{W,V} ≫ c_V = c_W` (`extendByZeroConstantRestrict_comp_constantInclusion`). It is defined as the lift
through the kernel of `cokernel.π c_V` (in an abelian category a monomorphism is the kernel of its
cokernel, `Abelian.monoIsKernelOfCokernel`); the existence of the lift, `c_W ≫ cokernel.π c_V = 0`, is
checked on stalks: off `W` the source has zero stalks, and at `x ∈ W ⊆ V` the stalk of `c_V` is an isomorphism
(`isIso_stalkFunctor_map_constantInclusion_hom_of_mem`), so the stalk of `cokernel c_V` vanishes.

Consequences:
* `ρ_{W,V}` is a monomorphism and an isomorphism on stalks at points of `W`;
* `hom_ext_of_cover`: if `W = ⋃ W_α` then morphisms out of `j_!ℤ_W` are determined by their restrictions
  `ρ_{W_α,W} ≫ -` (stalkwise: at `x ∈ W_α` the stalk of `ρ_{W_α,W}` is an isomorphism, off `W` the stalk of
  `j_!ℤ_W` is zero);
* `exists_comp_eq_of_cover`: a morphism `f : j_!ℤ_W ⟶ T` factors through a monomorphism `μ : K' ⟶ T` as soon as
  each restriction `ρ_{W_α,W} ≫ f` does (`f ≫ cokernel.π μ` vanishes on the cover, hence vanishes, hence `f`
  factors through `ker (cokernel.π μ) = K'`).

Source: Stacks 0A38 (cohomology-lemma-subsheaf-of-constant-sheaf), proof, paragraph 3 ("the section `n` of
`ℤ_X` over `U` lies in `K_n`" is a local statement); Stacks 00A5 (3). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- The stalk of `j_!ℤ_U` at `x ∉ U` is zero (`isZero_extendByZero_stalk_of_notMem`, specialised to `ℤ_U`). -/
theorem isZero_stalk_extendByZeroConstant_of_notMem (U : Opens X) (x : X) (hx : x ∉ U) :
    IsZero ((stalkFunctor AddCommGrpCat.{u} x).obj (extendByZeroConstant U).obj) :=
  isZero_extendByZero_stalk_of_notMem U _ x hx

/-- If the stalk of `f : F ⟶ G` at `x` is an isomorphism, the stalk of `cokernel f` at `x` is zero
(the stalk functor preserves cokernels, and the cokernel of an isomorphism is zero). -/
theorem isZero_stalk_cokernel_of_isIso_stalkFunctor_map
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (f : F ⟶ G) (x : X)
    (h : IsIso ((stalkFunctor AddCommGrpCat.{u} x).map f.hom)) :
    IsZero ((stalkFunctor AddCommGrpCat.{u} x).obj (cokernel f).obj) := by
  have hepi : Epi ((TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalkFunctor AddCommGrpCat.{u} x).map f) :=
    @IsIso.epi_of_iso _ _ _ _ _ h
  have e := PreservesCokernel.iso (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalkFunctor AddCommGrpCat.{u} x) f
  exact (isZero_zero _).of_iso (e ≪≫ cokernel.ofEpi _)

/-- `c_W ≫ cokernel.π c_V = 0` for `W ≤ V`: checked on stalks (zero source off `W`; at `x ∈ W ⊆ V` the stalk
of `cokernel c_V` is zero because the stalk of `c_V` is an isomorphism). -/
theorem constantInclusion_comp_cokernelπ_constantInclusion {W V : Opens X} (h : W ≤ V) :
    constantInclusion W ≫ cokernel.π (constantInclusion V) = 0 := by
  apply eq_zero_of_stalkFunctor_map
  intro x
  by_cases hx : x ∈ W
  · have hz := isZero_stalk_cokernel_of_isIso_stalkFunctor_map (constantInclusion V) x
      (isIso_stalkFunctor_map_constantInclusion_hom_of_mem V x (h hx))
    exact hz.eq_zero_of_tgt _
  · exact (isZero_stalk_extendByZeroConstant_of_notMem W x hx).eq_zero_of_src _

/-- **The restriction map** `ρ_{W,V} : j_!ℤ_W ⟶ j_!ℤ_V` for `W ≤ V`: the unique morphism with
`ρ_{W,V} ≫ c_V = c_W` (lift through the kernel of `cokernel.π c_V`, which is `c_V` since `c_V` is a
monomorphism in an abelian category). -/
def extendByZeroConstantRestrict {W V : Opens X} (h : W ≤ V) :
    extendByZeroConstant W ⟶ extendByZeroConstant V :=
  haveI := constantInclusion_mono V
  (Abelian.monoIsKernelOfCokernel
    (CokernelCofork.ofπ (cokernel.π (constantInclusion V)) (cokernel.condition (constantInclusion V)))
    (cokernelIsCokernel (constantInclusion V))).lift
    (KernelFork.ofι (constantInclusion W) (constantInclusion_comp_cokernelπ_constantInclusion h))

theorem extendByZeroConstantRestrict_comp_constantInclusion {W V : Opens X} (h : W ≤ V) :
    extendByZeroConstantRestrict h ≫ constantInclusion V = constantInclusion W := by
  have := constantInclusion_mono V
  exact Fork.IsLimit.lift_ι (Abelian.monoIsKernelOfCokernel
    (CokernelCofork.ofπ (cokernel.π (constantInclusion V)) (cokernel.condition (constantInclusion V)))
    (cokernelIsCokernel (constantInclusion V)))
    (t := KernelFork.ofι (constantInclusion W) (constantInclusion_comp_cokernelπ_constantInclusion h))

/-- `ρ_{W,V}` is a monomorphism (stated as a theorem, not an instance). -/
theorem extendByZeroConstantRestrict_mono {W V : Opens X} (h : W ≤ V) :
    Mono (extendByZeroConstantRestrict h) := by
  have := constantInclusion_mono W
  exact mono_of_mono_fac (extendByZeroConstantRestrict_comp_constantInclusion h)

/-- `ρ_{W,V}` is an isomorphism on stalks at every point of `W` (both `c_W` and `c_V` are). -/
theorem isIso_stalkFunctor_map_extendByZeroConstantRestrict_hom_of_mem {W V : Opens X} (h : W ≤ V)
    (x : X) (hx : x ∈ W) :
    IsIso ((stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroConstantRestrict h).hom) := by
  have hfac : (stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroConstantRestrict h).hom ≫
      (stalkFunctor AddCommGrpCat.{u} x).map (constantInclusion V).hom =
      (stalkFunctor AddCommGrpCat.{u} x).map (constantInclusion W).hom := by
    rw [← CategoryTheory.Functor.map_comp]
    exact congrArg (fun f => (stalkFunctor AddCommGrpCat.{u} x).map f.hom)
      (extendByZeroConstantRestrict_comp_constantInclusion h)
  have h1 := isIso_stalkFunctor_map_constantInclusion_hom_of_mem V x (h hx)
  have h2 := isIso_stalkFunctor_map_constantInclusion_hom_of_mem W x hx
  exact IsIso.of_isIso_fac_right hfac

/-- Morphisms out of `j_!ℤ_W` are determined by their restrictions to the members of an open cover of `W`. -/
theorem hom_ext_of_cover {W : Opens X} {ι : Type*} (Wc : ι → Opens X) (hle : ∀ α, Wc α ≤ W)
    (hcov : ∀ x ∈ W, ∃ α, x ∈ Wc α)
    {T : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (f g : extendByZeroConstant W ⟶ T)
    (h : ∀ α, extendByZeroConstantRestrict (hle α) ≫ f = extendByZeroConstantRestrict (hle α) ≫ g) : f = g := by
  apply hom_ext_of_stalkFunctor_map
  intro x
  by_cases hx : x ∈ W
  · obtain ⟨α, hα⟩ := hcov x hx
    have hiso := isIso_stalkFunctor_map_extendByZeroConstantRestrict_hom_of_mem (hle α) x hα
    have hα' : (stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroConstantRestrict (hle α)).hom ≫
        (stalkFunctor AddCommGrpCat.{u} x).map f.hom =
        (stalkFunctor AddCommGrpCat.{u} x).map (extendByZeroConstantRestrict (hle α)).hom ≫
          (stalkFunctor AddCommGrpCat.{u} x).map g.hom := by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
      exact congrArg (fun m => (stalkFunctor AddCommGrpCat.{u} x).map m.hom) (h α)
    exact (cancel_epi _).mp hα'
  · exact (isZero_stalk_extendByZeroConstant_of_notMem W x hx).eq_of_src _ _

/-- A morphism `f : j_!ℤ_W ⟶ T` factors through a monomorphism `μ : K' ⟶ T` as soon as each restriction
`ρ_{W_α,W} ≫ f` to the members of an open cover of `W` does: `f ≫ cokernel.π μ` vanishes on the cover, hence
vanishes (`hom_ext_of_cover`), so `f` factors through `ker (cokernel.π μ) = K'`. -/
theorem exists_comp_eq_of_cover {W : Opens X} {ι : Type*} (Wc : ι → Opens X) (hle : ∀ α, Wc α ≤ W)
    (hcov : ∀ x ∈ W, ∃ α, x ∈ Wc α)
    {T K' : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (μ : K' ⟶ T) [Mono μ]
    (f : extendByZeroConstant W ⟶ T) (g : ∀ α, extendByZeroConstant (Wc α) ⟶ K')
    (hg : ∀ α, g α ≫ μ = extendByZeroConstantRestrict (hle α) ≫ f) :
    ∃ q : extendByZeroConstant W ⟶ K', q ≫ μ = f := by
  have hzero : f ≫ cokernel.π μ = 0 := by
    apply hom_ext_of_cover Wc hle hcov
    intro α
    rw [← Category.assoc, ← hg α, Category.assoc, cokernel.condition, comp_zero, comp_zero]
  refine ⟨(Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ (cokernel.π μ) (cokernel.condition μ))
    (cokernelIsCokernel μ)).lift (KernelFork.ofι f hzero), ?_⟩
  exact Fork.IsLimit.lift_ι (Abelian.monoIsKernelOfCokernel (CokernelCofork.ofπ (cokernel.π μ) (cokernel.condition μ))
    (cokernelIsCokernel μ)) (t := KernelFork.ofι f hzero)

end TopCat.Sheaf

end
