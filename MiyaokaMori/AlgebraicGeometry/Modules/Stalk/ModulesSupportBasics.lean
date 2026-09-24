import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesTensorStalk
import Mathlib.Topology.KrullDimension

/-! # Elementary facts about supports

Elementary facts about the support `Supp F = {x | F_x ≠ 0}` needed in the
dévissage of Snapper's theorem (Stacks 0BEM):

* `support_eq_of_iso`: `Supp` only depends on the isomorphism class (stalks of isomorphic sheaves are
  isomorphic, `moduleStalkLinearEquiv`).
* `support_subset_of_mono`: `K ↪ F` mono ⇒ `Supp K ⊆ Supp F` (the stalk functor preserves finite limits,
  so `K_x → F_x` is injective; an injective map out of a nontrivial module
  lands in a nontrivial module).
* `mem_support_pushforward_of_isClosedImmersion`: for a closed immersion `i : Z → X` and `z ∈ Supp G`,
  `i z ∈ Supp (i_* G)`: the stalk of the pushforward of an abelian sheaf along an inducing map at `i z`
  is the stalk at `z` (Mathlib `stalkPushforward_iso_of_isInducing`, Stacks 00AE), and the underlying
  abelian presheaf of `i_* G` is the pushforward of that of `G` (`pushforwardAb_obj_toAddCommGrpSheaf`).
* `topologicalKrullDim_le_support_pushforward`: if moreover `Supp G = Z`, then
  `dim Z ≤ dim Supp (i_* G)` (`Z → Supp (i_* G)`, `z ↦ i z`, is inducing).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

theorem mem_support_iff (F : X.Modules) (x : X) : x ∈ F.support ↔ Nontrivial (F.stalk x) :=
  Iff.rfl

/-- The support only depends on the isomorphism class. -/
theorem support_eq_of_iso {M N : X.Modules} (e : M ≅ N) : M.support = N.support := by
  ext x
  rw [mem_support_iff, mem_support_iff]
  exact (moduleStalkLinearEquiv X x e).toEquiv.nontrivial_congr

/-- A subsheaf has smaller support. -/
theorem support_subset_of_mono {K F : X.Modules} (ι : K ⟶ F) [Mono ι] : K.support ⊆ F.support := by
  intro x hx
  rw [mem_support_iff] at hx ⊢
  have hpres : PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
    (stalk_preservesFiniteLimits_colimits x).1
  have hmono : Mono ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map ι) :=
    preserves_mono_of_preservesLimit _ ι
  have hinj : Function.Injective ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map ι) :=
    (ModuleCat.mono_iff_injective _).mp hmono
  have hK : Nontrivial ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).obj K) := hx
  exact hinj.nontrivial

/-- Points of the support of `G` map into the support of `i_* G` for a closed immersion `i`. -/
theorem mem_support_pushforward_of_isClosedImmersion {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules) {z : Z} (hz : z ∈ G.support) :
    i.base z ∈ ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).support := by
  rw [mem_support_iff] at hz ⊢
  -- the underlying abelian presheaf of `i_* G` is `i_* (G.presheaf)`
  have hind : IsInducing i.base := i.isClosedEmbedding.isInducing
  have hiso : IsIso (G.presheaf.stalkPushforward AddCommGrpCat.{u} i.base z) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing AddCommGrpCat.{u} hind G.presheaf z
  have hbij := ConcreteCategory.bijective_of_isIso (G.presheaf.stalkPushforward AddCommGrpCat.{u} i.base z)
  have hG : Nontrivial (G.presheaf.stalk z) := hz
  have h1 : Nontrivial ((i.base _* G.presheaf).stalk (i.base z)) :=
    (Equiv.ofBijective _ hbij).nontrivial
  exact h1

/-- If `Supp G = Z`, then `dim Z ≤ dim Supp (i_* G)` for a closed immersion `i : Z → X`. -/
theorem topologicalKrullDim_le_support_pushforward {Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules) (hG : G.support = Set.univ) :
    topologicalKrullDim Z ≤
      topologicalKrullDim ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).support := by
  let g : Z → ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).support := fun z =>
    ⟨i.base z, mem_support_pushforward_of_isClosedImmersion i G (hG ▸ Set.mem_univ z)⟩
  have hg : Continuous g := i.base.hom.continuous.subtype_mk _
  have hcomp : IsInducing (Subtype.val ∘ g) := by
    have : Subtype.val ∘ g = i.base := funext fun z => rfl
    rw [this]
    exact i.isClosedEmbedding.isInducing
  have hind : IsInducing g := IsInducing.of_comp hg continuous_subtype_val hcomp
  exact hind.topologicalKrullDim_le

end AlgebraicGeometry.Scheme.Modules

end
