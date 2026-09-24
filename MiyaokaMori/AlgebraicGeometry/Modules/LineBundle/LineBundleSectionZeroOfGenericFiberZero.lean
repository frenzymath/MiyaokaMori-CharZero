import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionGenericGermZero
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt

/-! # A section vanishing on the generic fibre vanishes

Statement: `π : W ⟶ B` a morphism of integral schemes sending the generic point `ξ` of `W` to the generic
point `η` of `B`; `N` a line bundle on `W`, `m ∈ Γ(W, N)`, `U ⊂ W` a nonempty open. If `m`, restricted to `U`
and pulled back to the fibre `U_η` of `U → B` over `η`, is zero, then `m = 0`.

Proof:
1. `W` is irreducible and `U` a nonempty open, so `ξ ∈ U` (`IsGenericPoint.mem_open_set_iff`); write `ξ_U ∈ U`
   for the corresponding point, `(U.ι ≫ π)(ξ_U) = π(ξ) = η` (`hdom`). By `Scheme.Hom.range_fiberι`, the image
   of the fibre `U_η → U` is exactly the set of points over `η`, so there is `ξ' ∈ U_η` mapping to `ξ_U`.
2. The section in the hypothesis is zero, hence "zero at `ξ'`" (`IsZeroAt`: the germ lies in `𝔪·M`). Apply
   the forward form of the pullback criterion (a pulled-back section zero at `x` ⇒ the original section is
   zero at the image point, for any module) to the fibre immersion `U_η → U`, giving `m|_U` zero at `ξ_U`;
   apply it once more to the open immersion `U → W`, giving `m` zero at `ξ`.
3. The stalk at the generic point of an integral scheme is the function field (the `Field` instance of
   `AlgebraicGeometry.Scheme.functionField`), whose maximal ideal is `⊥`, so "`m` is zero at `ξ`" means that
   the germ of `m` at `ξ` is `0`.
4. Line bundles on integral schemes are torsion-free
   (`lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero`): a global section with vanishing generic germ
   is zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem lineBundle_section_eq_zero_of_generic_fiber_eq_zero {W B : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsIntegral B] (π : W ⟶ B)
    (hdom : π.base (genericPoint W) = genericPoint B)
    (N : W.Modules) [N.IsLineBundle] (U : W.Opens) (hU : (U : Set W).Nonempty)
    (m : (N.val.obj (Opposite.op ⊤) : Type u))
    (h : sectionPullbackAlong ((U.ι ≫ π).fiberι (genericPoint B)) (sectionPullbackAlong U.ι m) = 0) :
    m = 0 := by
  -- 1. the generic point lies in the nonempty open U
  have hξ : genericPoint W ∈ (U : Set W) := by
    rw [(genericPoint_spec W).mem_open_set_iff U.isOpen]
    simpa using hU
  set ξU : (U : W.Opens).toScheme := ⟨genericPoint W, hξ⟩ with hξUdef
  have hbase : U.ι.base ξU = genericPoint W := rfl
  have hpt : (U.ι ≫ π).base ξU = genericPoint B := hdom
  -- there is a point of the fibre mapping to ξU
  obtain ⟨ξ', hξ'⟩ : ξU ∈ Set.range ((U.ι ≫ π).fiberι (genericPoint B)).base := by
    rw [AlgebraicGeometry.Scheme.Hom.range_fiberι]
    exact hpt
  -- 2. the zero section is zero at ξ'; push down step by step
  have hz2 := isZeroAt_of_sectionPullbackAlong_eq_zero
    ((U.ι ≫ π).fiberι (genericPoint B)) _ (sectionPullbackAlong U.ι m) ξ' h
  rw [hξ'] at hz2
  have hz3 := isZeroAt_of_isZeroAt_sectionPullbackAlong U.ι N m ξU hz2
  rw [hbase] at hz3
  -- 3. the stalk at the generic point is a field; its maximal ideal is ⊥
  have hgerm : (N.presheaf.germ ⊤ (genericPoint W) trivial).hom m = 0 := by
    have hbot : IsLocalRing.maximalIdeal (W.presheaf.stalk (genericPoint W)) = ⊥ :=
      IsLocalRing.maximalIdeal_eq_bot
    have := hz3
    rw [IsZeroAt, hbot, Submodule.bot_smul, Submodule.mem_bot] at this
    exact this
  -- 4. line bundles are torsion-free
  exact lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero N m hgerm

end
