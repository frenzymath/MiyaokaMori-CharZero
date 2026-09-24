import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Localization.BaseChangeFiberDescent
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong

/-! # Nonvanishing of pulled-back sections

Let `g : X ⟶ Y` be a morphism of schemes, `M` a line bundle on `Y`, `s ∈ Γ(Y, M)`, `x ∈ X`. If `s`
does not vanish at `g(x)` (the negation of `IsZeroAt`: the germ `s_{g(x)}` is not in
`𝔪_{g(x)}·M_{g(x)}`), then the pulled-back section `g^*s ∈ Γ(X, g^*M)` does not vanish at `x`.

Proof (more general than needed: the line bundle hypothesis is not used, but kept in the
signature). Write `y = g(x)`, `A = O_{Y,y}`, `B = O_{X,x}`, `φ` the stalk map of `g` at `x` (a local
homomorphism of local rings).
1. `(g^*M)_x ≅ B ⊗_A M_y` (`B`-linearly), and the inverse sends the image `u(m)` of the adjunction
   unit to `1 ⊗ m` (`modulePullbackStalkTensorInverse_unit`).
2. The germ of `g^*s` is `u` applied to the germ of `s` (`modulePullbackStalkUnitAddHom_germ` with
   `U = ⊤`; `sectionPullbackAlong` is by definition the component of the adjunction unit at `⊤`).
3. The linear isomorphism carries `𝔪_B·(g^*M)_x` to `𝔪_B·(B ⊗_A M_y)` (`Submodule.map_smul''`), so
   "`g^*s` vanishes at `x`" is equivalent to `1 ⊗ s_y ∈ 𝔪_B·(B ⊗_A M_y)`.
4. Base change along a local homomorphism creates no new elements in the maximal-ideal multiples
   (fibre descent), so `s_y ∈ 𝔪_A·M_y`, i.e. `s` vanishes at `y`, a contradiction.

Reference: the pullback of the zero locus of a section of a line bundle, `Z(g^*s) = g⁻¹Z(s)`
(a standard fact near Stacks 01CR).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

/-- If the pulled-back section vanishes at `x`, the original section vanishes at `g(x)` (for any
sheaf of modules; no line bundle hypothesis is needed). -/
theorem isZeroAt_of_isZeroAt_sectionPullbackAlong {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (M : Y.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (hzero : IsZeroAt (sectionPullbackAlong g s) x) : IsZeroAt s (g.base x) := by
  letI := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra g x
  -- the germ of the pulled-back section at `x` is the adjunction unit applied to the germ of `s` at `g x`
  have hgerm :
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.germ ⊤ x trivial).hom
          (sectionPullbackAlong g s) =
        AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x
          ((M.presheaf.germ ⊤ (g.base x) trivial).hom s) :=
    (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ g M x ⊤ trivial s).symm
  -- transport vanishing along `(g^*M)_x ≅ B ⊗_A M_{g x}` to the tensor product side
  have hzero' :
      (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x
        ((M.presheaf.germ ⊤ (g.base x) trivial).hom s)) ∈
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x)) := by
    rw [← hgerm]; exact hzero
  have hmem :=
    Submodule.mem_map_of_mem (f :=
      ((MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv g M x).symm :
        AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x →ₗ[X.presheaf.stalk x]
          AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensor g M x)) hzero'
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range] at hmem
  -- the inverse computes the image of the unit as `1 ⊗ s_{g x}`
  have hinv :
      ((MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorEquiv g M x).symm :
          AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x →ₗ[X.presheaf.stalk x]
            AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensor g M x)
        (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x
          ((M.presheaf.germ ⊤ (g.base x) trivial).hom s)) =
      (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (g.base x)]
        ((M.presheaf.germ ⊤ (g.base x) trivial).hom s) :=
    MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorInverse_unit g M x _
  rw [hinv] at hmem
  exact MiyaokaMori.BaseChangeFiberDescent.mem_maximalIdeal_smul_of_one_tmul
    (g.stalkMap x).hom _ hmem

/-- If the pulled-back section is zero, the original section vanishes at every image point. -/
theorem isZeroAt_of_sectionPullbackAlong_eq_zero {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (M : Y.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (h : sectionPullbackAlong g s = 0) : IsZeroAt s (g.base x) := by
  apply isZeroAt_of_isZeroAt_sectionPullbackAlong
  show _ ∈ _
  rw [h]
  have h0 : ((TopCat.Presheaf.germ
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.presheaf ⊤ x trivial).hom
      (0 : ((((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj
        (Opposite.op ⊤)) : Type u))) = 0 := map_zero _
  exact Eq.subst (motive := fun z ↦ z ∈ _) h0.symm (Submodule.zero_mem _)

/-- If `s` does not vanish at `g x`, then `g^*s` does not vanish at `x`. -/
theorem not_isZeroAt_sectionPullbackAlong {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) [M.IsLineBundle] (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (h : ¬ IsZeroAt s (g.base x)) :
    ¬ IsZeroAt (sectionPullbackAlong g s) x := fun hzero ↦
  h (isZeroAt_of_isZeroAt_sectionPullbackAlong g M s x hzero)

end
