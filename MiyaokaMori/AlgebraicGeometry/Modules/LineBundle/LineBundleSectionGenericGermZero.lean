import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates

/-! # A section of a line bundle on an integral scheme vanishes if its generic germ does

Statement: `W` an integral scheme, `N` a line bundle on `W`, `m ∈ Γ(W, N)`. If the germ of `m` at the
generic point `ξ` is zero, then `m = 0`. (Line bundles on integral schemes are torsion-free: a global section
is determined by its germ at the generic point.)

Proof:
1. For every `x ∈ W` take a trivializing open `V ∋ x` and an isomorphism `φ : N|_V ≅ O_V`
   (`SheafOfModules.IsLineBundle.locally_trivial`). `W` is irreducible and `V` nonempty (it contains `x`), so
   the generic point `ξ ∈ V` (`IsGenericPoint.mem_open_set_iff`); write `ξ_V ∈ V` for the corresponding point.
2. Pullback of modules along an open immersion does not change stalks:
   `(V.ι^*N)_{ξ_V} ≅ O_{V,ξ_V} ⊗_{O_{W,ξ}} N_ξ`, and the stalk map `O_{W,ξ} → O_{V,ξ_V}` of an open immersion
   is an isomorphism (`AlgebraicGeometry.IsOpenImmersion`); extension of scalars along a ring isomorphism is
   an isomorphism, so `N_ξ ≅ (N|_V)_{ξ_V}`, and this isomorphism sends germs of sections to germs of the
   restricted sections (`modulePullbackStalkUnitAddHom_germ`).
3. `φ` on the stalk at `ξ_V` gives `(N|_V)_{ξ_V} ≅ (O_V)_{ξ_V} = O_{V,ξ_V} ≅ O_{W,ξ}`; on sections,
   `m|_V ∈ Γ(N, V)` corresponds to some `a ∈ Γ(W, V)`. By step 2 and the hypothesis, the germ of `a` at `ξ`
   is zero.
4. `W` is integral, so `AlgebraicGeometry.germ_injective_of_isIntegral` gives that `Γ(W, V) → O_{W,ξ}` is
   injective, hence `a = 0` and `m|_V = 0` (`φ` is an additive isomorphism on `V`).
5. Such `V`, as `x` varies, cover `W`; the separation axiom of sheaves (`TopCat.Presheaf.section_ext`, with
   `N.isSheaf`) gives `m = 0`.

Reference: locally free sheaves on integral schemes are torsion-free (standard fact near Stacks 01PD).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A global section of a line bundle on an integral scheme whose germ at the generic point is zero is zero. -/
theorem lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero
    {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
    (N : W.Modules) [N.IsLineBundle] (m : (N.val.obj (Opposite.op ⊤) : Type u))
    (h : (N.presheaf.germ ⊤ (genericPoint W) trivial).hom m = 0) : m = 0 := by
  have hglobal_injective :
      Function.Injective (N.presheaf.germ ⊤ (genericPoint W) (by simp)) := by
    intro a b hab
    refine TopCat.Presheaf.section_ext
      (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab W) ⊤ a b ?_
    intro x hx
    obtain ⟨U, hxU, ⟨e⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := N) x
    let e' := e ≪≫ (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).symm
    have hη : genericPoint W ∈ U :=
      AlgebraicGeometry.Divisors.LineGenericCoordinates.genericPoint_mem_of_nonempty W U ⟨⟨x, hxU⟩⟩
    apply (AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization W N U ⟨x, hxU⟩ e').injective
    apply IsFractionRing.injective (W.presheaf.stalk x) W.functionField
    rw [← AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization_toGenericFiber
      W N U e' ⟨x, hxU⟩ hη (N.presheaf.germ ⊤ x hx a),
      ← AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization_toGenericFiber
        W N U e' ⟨x, hxU⟩ hη (N.presheaf.germ ⊤ x hx b)]
    have hab' :
        AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber W N x (N.presheaf.germ ⊤ x hx a) =
          AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber W N x (N.presheaf.germ ⊤ x hx b) := by
      simpa only [AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ] using hab
    exact congrArg
      (AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization W N U
        ⟨genericPoint W, hη⟩ e') hab'
  apply hglobal_injective
  change (N.presheaf.germ ⊤ (genericPoint W) trivial).hom m =
    (N.presheaf.germ ⊤ (genericPoint W) trivial).hom 0
  simpa using h

end
