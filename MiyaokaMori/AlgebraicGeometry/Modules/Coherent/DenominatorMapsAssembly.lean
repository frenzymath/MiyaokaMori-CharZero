import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorTensorStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkCriteria
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics

/-! # Assembly of the denominator maps

The categorical assembly step of the denominator-ideal trick (Stacks 02P2, 0BEM proof 4th paragraph),
isolated from the regular-meromorphic-section input.

**Setting.** `X` locally Noetherian; `P` quasi-coherent, `F` coherent, `G` any `O_X`-module;
`f : P ⟶ F`, `g : P ⟶ G` two maps with the *same kernel on every stalk*
(`f_x z = 0 ↔ g_x z = 0`), and a set `T ⊆ X` off which both `f_x` and `g_x` are surjective.
(In the application `P = I ⊗ F`, `f = denomMulMap a F : h ⊗ t ↦ a(h)•t`,
`g = denomSectionMap b F : h ⊗ t ↦ t ⊗ b(h)`, and `T` is the 02P0 bad set.)

**Conclusion** (`exists_coherent_factor_of_stalkMap_eq_zero_iff`): there are a coherent `IF` and monos
`a : IF ⟶ F`, `b : IF ⟶ G` whose cokernels are supported in `T`.

**Proof.** Put `IF := coimage f = coker (ker f → P)` (Mathlib `Abelian.coimage`), `a := factorThruCoimage f`
(mono, `coimage.π f ≫ a = f`). `ker f` and then `IF` are quasi-coherent (Stacks 01IC,
`isQuasicoherent_kernel`), so `IF` is coherent as a quasi-coherent submodule of the coherent `F`
(Stacks 01Y1, `isCoherent_of_mono`). The map `g` kills `ker f`: a morphism is determined by its stalk maps
(`hom_ext_of_stalkMap`), and for `z ∈ (ker f)_x`, `f_x(ι_x z) = (ι ≫ f)_x z = 0`, hence `g_x(ι_x z) = 0` by
the kernel hypothesis. So `g` descends to `b : IF ⟶ G` with `coimage.π f ≫ b = g`. `b` is mono: check on
stalks (`mono_of_stalkMap_injective`); `π_x` is surjective (`π` epi), so `w = π_x z`, and `b_x w = g_x z = 0`
forces `f_x z = 0`, i.e. `a_x w = 0`, i.e. `w = 0` (`a` mono ⇒ `a_x` injective). Finally at `x ∉ T`,
`f_x = a_x ∘ π_x` surjective ⇒ `a_x` surjective ⇒ `(coker a)_x = 0` (`notMem_support_cokernel_iff`),
and likewise for `b`.

Stalk lemmas proved on the way (all for `AlgebraicGeometry.Scheme.Modules.moduleStalkMap`, the stalk functor
`Scheme.Modules.stalkFunctor x`):
`moduleStalkMap_comp_apply`, `moduleStalkMap_zero_apply`, `stalkMap_injective_of_mono`,
`mono_of_stalkMap_injective`, `notMem_support_cokernel_iff` (`x ∉ Supp (coker φ) ↔ φ_x` surjective, since the
stalk functor preserves cokernels and `coker` in `ModuleCat` is the quotient by the range).

Source: Stacks 02P2 (proof), 01IC, 01Y1, 01AJ (stalk functor exact), 01BA (support).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open MiyaokaMori.ExteriorTensorStalk (moduleStalkMap_comp_apply moduleStalkMap_zero_apply)

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The linear map underlying `(stalkFunctor x).map φ` is `moduleStalkMap X x φ`. -/
theorem stalkFunctor_map_hom {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ).hom = AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ :=
  rfl

/-- A monomorphism of module sheaves is injective on every stalk (the stalk functor preserves finite
limits). -/
theorem stalkMap_injective_of_mono {M N : X.Modules} (φ : M ⟶ N) [Mono φ] (x : X) :
    Function.Injective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ) := by
  have hpres : PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
    (stalk_preservesFiniteLimits_colimits x).1
  have hmono : Mono ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ) :=
    preserves_mono_of_preservesLimit _ φ
  have hinj := (ModuleCat.mono_iff_injective _).mp hmono
  rw [← stalkFunctor_map_hom]
  exact hinj

/-- A morphism injective on every stalk is a monomorphism. -/
theorem mono_of_stalkMap_injective {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, Function.Injective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ)) : Mono φ := by
  apply CategoryTheory.Abelian.mono_of_kernel_ι_eq_zero
  apply MiyaokaMori.ModulesStalkCriteria.hom_ext_of_stalkMap
  intro x
  ext z
  rw [moduleStalkMap_zero_apply]
  apply h x
  rw [map_zero, ← moduleStalkMap_comp_apply, kernel.condition, moduleStalkMap_zero_apply]

/-- `x ∉ Supp (coker φ)` iff `φ_x` is surjective (the stalk functor preserves cokernels and the cokernel
in `ModuleCat` is the quotient by the range). -/
theorem notMem_support_cokernel_iff {M N : X.Modules} (φ : M ⟶ N) (x : X) :
    x ∉ (CategoryTheory.Limits.cokernel φ).support ↔
      Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x φ) := by
  have hpres : PreservesColimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
    (stalk_preservesFiniteLimits_colimits x).2
  let e : (AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj (cokernel φ) ≅
      cokernel ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ) :=
    PreservesCokernel.iso (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) φ
  let e' := e ≪≫ ModuleCat.cokernelIsoRangeQuotient
    ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ)
  have hequiv : Nontrivial ((cokernel φ).stalk x) ↔
      Nontrivial ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj N ⧸
        LinearMap.range ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map φ).hom) :=
    (e'.toLinearEquiv.toEquiv).nontrivial_congr
  rw [mem_support_iff, hequiv, Submodule.Quotient.nontrivial_iff, not_not, LinearMap.range_eq_top]
  exact Iff.rfl

/-- **The assembly step of Stacks 02P2 (see the module docstring).** From `f : P ⟶ F`, `g : P ⟶ G` with
the same stalkwise kernels, both stalkwise surjective off `T`, build the coherent `IF := coimage f` with
monos `a : IF ⟶ F`, `b : IF ⟶ G` and cokernels supported in `T`. -/
theorem exists_coherent_factor_of_stalkMap_eq_zero_iff [AlgebraicGeometry.IsLocallyNoetherian X]
    {P F G : X.Modules} [P.IsQuasicoherent] [F.IsCoherent] (f : P ⟶ F) (g : P ⟶ G)
    (hker : ∀ (x : X) (z : P.presheaf.stalk x),
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x f z = 0 ↔ AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x g z = 0)
    (T : Set X) (hf : ∀ x ∉ T, Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x f))
    (hg : ∀ x ∉ T, Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x g)) :
    ∃ (IF : X.Modules) (a : IF ⟶ F) (b : IF ⟶ G),
      IF.IsCoherent ∧ CategoryTheory.Mono a ∧ CategoryTheory.Mono b ∧
      (CategoryTheory.Limits.cokernel a).support ⊆ T ∧ (CategoryTheory.Limits.cokernel b).support ⊆ T := by
  have hFqc : F.IsQuasicoherent := IsCoherent.quasicoherent
  -- `g` kills `ker f`
  have hzero : kernel.ι f ≫ g = 0 := by
    apply MiyaokaMori.ModulesStalkCriteria.hom_ext_of_stalkMap
    intro x
    ext z
    rw [moduleStalkMap_zero_apply, moduleStalkMap_comp_apply, ← hker, ← moduleStalkMap_comp_apply,
      kernel.condition, moduleStalkMap_zero_apply]
  let IF : X.Modules := Abelian.coimage f
  let a : IF ⟶ F := Abelian.factorThruCoimage f
  let b : IF ⟶ G := cokernel.desc (kernel.ι f) g hzero
  have hπa : Abelian.coimage.π f ≫ a = f := Abelian.coimage.fac f
  have hπb : Abelian.coimage.π f ≫ b = g := cokernel.π_desc _ _ _
  have hker_qc : (kernel f).IsQuasicoherent := (isQuasicoherent_kernel f).1
  have hIFqc : IF.IsQuasicoherent := (isQuasicoherent_kernel (kernel.ι f)).2
  have hmono_a : Mono a := inferInstance
  have hIF : IF.IsCoherent := isCoherent_of_mono a
  have hπsurj : ∀ x : X, Function.Surjective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (Abelian.coimage.π f)) :=
    fun x => MiyaokaMori.FreeStalk.stalkMap_surjective_of_epi _ x
  have hmono_b : Mono b := by
    apply mono_of_stalkMap_injective
    intro x
    rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨z, rfl⟩ := hπsurj x w
    rw [← moduleStalkMap_comp_apply, hπb] at hw
    have hfz : AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x f z = 0 := (hker x z).mpr hw
    rw [← hπa, moduleStalkMap_comp_apply] at hfz
    exact (stalkMap_injective_of_mono a x) (by rw [hfz, map_zero])
  refine ⟨IF, a, b, hIF, hmono_a, hmono_b, ?_, ?_⟩
  · intro x hx
    by_contra hxT
    apply (notMem_support_cokernel_iff a x).mpr _ hx
    intro t
    obtain ⟨z, hz⟩ := hf x hxT t
    exact ⟨AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (Abelian.coimage.π f) z, by
      rw [← moduleStalkMap_comp_apply, hπa, hz]⟩
  · intro x hx
    by_contra hxT
    apply (notMem_support_cokernel_iff b x).mpr _ hx
    intro t
    obtain ⟨z, hz⟩ := hg x hxT t
    exact ⟨AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (Abelian.coimage.π f) z, by
      rw [← moduleStalkMap_comp_apply, hπb, hz]⟩

end AlgebraicGeometry.Scheme.Modules

end
