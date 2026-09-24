import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleRestrictionStalk

/-! # The order of a rational section along an open immersion

Let `f : W → X` be an open immersion of integral locally Noetherian schemes (in particular an
isomorphism), `L` a line bundle on `X`, `t′` a nonzero element of the generic stalk of `L|_W := L.restrict f`
and `z′ ∈ W`. Then `ord_{z′, L|_W}(t′) = ord_{f z′, L}(Φ t′)`, where
`Φ = genericStalkMap f L : (L|_W)_{η_W} → L_{η_X}` is the stalk isomorphism
`AlgebraicGeometry.Scheme.Modules.ModuleRestrictionStalk.stalkEquiv` followed by the specialization `f η_W ⇝ η_X`; `Φ` is injective
and semilinear with respect to `functionFieldMap f`.

Proof:
1. `stalkEquiv f L y : (L|_W)_y ≃ L_{f y}` is semilinear with respect to the local ring isomorphism
   `stalkRingEquiv f y` (the inverse of `f.stalkMap y`), with germ formula `stalkEquiv_germ`; the germ
   formula gives compatibility with specialization maps (`stalkEquiv_specializes`).
2. Three properties of `Φ`: injectivity (`stalkEquiv` is bijective; specialization maps between equal points
   are mutually inverse); `Φ(j_W m) = j_X(stalkEquiv m)` (step 1 and composition of specializations);
   `Φ(f^♯γ • m) = γ • Φ m` (semilinearity of `stalkEquiv` and `moduleStalkSpecializes`, and
   `stalkRingEquiv (f.stalkMap r) = r`).
3. Take a generator `τ` of `L_{f z′}` (`exists_stalk_generator`); `τ′ := stalkEquiv⁻¹ τ` generates
   `(L|_W)_{z′}`; take `γ ∈ K(X)` with `γ • j_X τ = Φ t′` (`exists_smul_toGenericFiber_eq`); step 2 and the
   injectivity of `Φ` give `f^♯γ • j_W τ′ = t′`.
4. Apply the arbitrary-generator characterization (`rationalSectionOrd_eq_ord_of_generator`) on both sides:
   the left side is `ord_{z′}(f^♯γ)`, the right side `ord_{f z′}(γ)`; `ord_functionFieldMap` finishes.
(Stacks 02SE: `div_L(s)` depends only on local rings and stalks, which open immersions do not change.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace MiyaokaMori.RationalSectionOrdRestrict
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.ModuleRestrictionStalk MiyaokaMori.OrdOpenImmersion

variable {W X : Scheme.{u}} (f : W ⟶ X) [IsOpenImmersion f]

/-- The stalk isomorphism is compatible with specialization maps. -/
theorem stalkEquiv_specializes (L : X.Modules) {x y : W} (h : x ⤳ y)
    (m : (L.restrict f).presheaf.stalk y) :
    stalkEquiv f L x (moduleStalkSpecializes W (L.restrict f) h m) =
      moduleStalkSpecializes X L (f.base.hom.map_specializes h) (stalkEquiv f L y m) := by
  obtain ⟨V, hyV, b, rfl⟩ := (L.restrict f).presheaf.exists_germ_eq m
  rw [moduleStalkSpecializes_germ, stalkEquiv_germ, stalkEquiv_germ]
  exact (moduleStalkSpecializes_germ X L (f.base.hom.map_specializes h) (f ''ᵁ V)
    ⟨y, hyV, rfl⟩ _).symm

theorem stalkRingEquiv_stalkMap (y : W) (r : X.presheaf.stalk (f y)) :
    stalkRingEquiv f y (f.stalkMap y r) = r :=
  congrArg (fun φ => φ.hom r) (asIso (f.stalkMap y)).hom_inv_id

omit [IsOpenImmersion f] in
theorem moduleStalkSpecializes_comp (L : X.Modules) {x y z : X} (h : x ⤳ y) (h' : y ⤳ z)
    (m : L.presheaf.stalk z) :
    moduleStalkSpecializes X L h (moduleStalkSpecializes X L h' m) =
      moduleStalkSpecializes X L (h.trans h') m := by
  obtain ⟨V, hV, b, rfl⟩ := L.presheaf.exists_germ_eq m
  simp only [moduleStalkSpecializes_germ]

omit [IsOpenImmersion f] in
theorem moduleStalkSpecializes_self (L : X.Modules) {x : X} (h : x ⤳ x)
    (m : L.presheaf.stalk x) : moduleStalkSpecializes X L h m = m := by
  obtain ⟨V, hV, b, rfl⟩ := L.presheaf.exists_germ_eq m
  simp only [moduleStalkSpecializes_germ]

variable [IsIntegral W] [IsIntegral X]

/-- The transport of generic stalks `Φ : (L|_W)_{η_W} → L_{η_X}` (the stalk isomorphism followed by the
specialization `f η_W ⇝ η_X`). -/
def genericStalkMap (L : X.Modules) (m : (L.restrict f).presheaf.stalk (genericPoint W)) :
    L.presheaf.stalk (genericPoint X) :=
  moduleStalkSpecializes X L ((genericPoint_spec X).specializes (Set.mem_univ _))
    (stalkEquiv f L (genericPoint W) m)

theorem genericStalkMap_injective (L : X.Modules) :
    Function.Injective (genericStalkMap f L) := by
  intro a b hab
  have h' : f (genericPoint W) ⤳ genericPoint X :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion f)
  have := congrArg (moduleStalkSpecializes X L h') hab
  unfold genericStalkMap at this
  rw [moduleStalkSpecializes_comp, moduleStalkSpecializes_comp, moduleStalkSpecializes_self,
    moduleStalkSpecializes_self] at this
  exact (stalkEquiv f L (genericPoint W)).injective this

/-- `Φ` transports "specialize to the generic point" on `W` to "specialize to the generic point" on `X`. -/
theorem genericStalkMap_toGenericFiber (L : X.Modules) (z' : W)
    (m : (L.restrict f).presheaf.stalk z') :
    genericStalkMap f L (moduleStalkToGenericFiber W (L.restrict f) z' m) =
      moduleStalkToGenericFiber X L (f z') (stalkEquiv f L z' m) := by
  unfold genericStalkMap moduleStalkToGenericFiber
  rw [stalkEquiv_specializes, moduleStalkSpecializes_comp]

/-- `Φ` is semilinear with respect to `functionFieldMap f`: `Φ(f^♯γ • m) = γ • Φ m`. -/
theorem genericStalkMap_smul (L : X.Modules) (γ : X.functionField)
    (m : (L.restrict f).presheaf.stalk (genericPoint W)) :
    genericStalkMap f L (functionFieldMap f γ • m) = γ • genericStalkMap f L m := by
  have h' : f (genericPoint W) ⤳ genericPoint X :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion f)
  have hη : genericPoint X ⤳ f (genericPoint W) :=
    (genericPoint_spec X).specializes (Set.mem_univ _)
  have h1 := (stalkEquiv f L (genericPoint W)).map_smulₛₗ (functionFieldMap f γ) m
  have h2 : stalkRingEquiv f (genericPoint W) (functionFieldMap f γ) =
      (X.presheaf.stalkSpecializes h').hom γ := stalkRingEquiv_stalkMap f _ _
  have h12 : stalkEquiv f L (genericPoint W) (functionFieldMap f γ • m) =
      ((X.presheaf.stalkSpecializes h').hom γ) • stalkEquiv f L (genericPoint W) m :=
    h1.trans (congrArg (· • stalkEquiv f L (genericPoint W) m) h2)
  have h3 : (X.presheaf.stalkSpecializes hη).hom ((X.presheaf.stalkSpecializes h').hom γ) = γ :=
    (congrArg (fun φ => φ.hom γ) (X.presheaf.stalkSpecializes_comp hη h')).trans
      (congrArg (fun φ => φ.hom γ) (X.presheaf.stalkSpecializes_refl _))
  unfold genericStalkMap
  rw [h12, (moduleStalkSpecializes X L hη).map_smulₛₗ, h3]

theorem genericStalkMap_zero (L : X.Modules) : genericStalkMap f L 0 = 0 := by
  unfold genericStalkMap
  rw [map_zero, map_zero]

open AlgebraicGeometry.Scheme.Modules in
/-- Restriction along an open immersion does not change the order of a rational section:
`ord_{z′, L|_W}(t′) = ord_{f z′, L}(Φ t′)`. -/
theorem rationalSectionOrd_restrict [IsLocallyNoetherian W] [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle]
    (t' : (L.restrict f).stalk (genericPoint W)) (ht' : t' ≠ 0) (z' : W) :
    (L.restrict f).rationalSectionOrd t' z' =
      L.rationalSectionOrd (genericStalkMap f L t') (f z') := by
  let E := stalkEquiv f L z'
  -- take a generator τ on the X side and transport it back to τ' on the W side
  obtain ⟨τ, hτ⟩ := exists_stalk_generator L (f z')
  let τ' := E.symm τ
  have hEτ' : E τ' = τ := E.apply_symm_apply τ
  have hτ' : Submodule.span (W.presheaf.stalk z') {τ'} = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have hm : E m ∈ Submodule.span (X.presheaf.stalk (f z')) {τ} := by rw [hτ]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
    refine Submodule.mem_span_singleton.mpr ⟨(stalkRingEquiv f z').symm a, ?_⟩
    apply E.injective
    have h1 := E.map_smulₛₗ ((stalkRingEquiv f z').symm a) τ'
    refine h1.trans ?_
    rw [hEτ', ← ha]
    exact congrArg (· • τ) ((stalkRingEquiv f z').apply_symm_apply a)
  have hΦ0 : genericStalkMap f L t' ≠ 0 := by
    intro h0
    exact ht' (genericStalkMap_injective f L (h0.trans (genericStalkMap_zero f L).symm))
  obtain ⟨γ, hγ⟩ := exists_smul_toGenericFiber_eq L (f z') τ hτ (genericStalkMap f L t')
  have hW : functionFieldMap f γ • moduleStalkToGenericFiber W (L.restrict f) z' τ' = t' := by
    apply genericStalkMap_injective f L
    rw [genericStalkMap_smul, genericStalkMap_toGenericFiber]
    exact (congrArg (fun y => γ • moduleStalkToGenericFiber X L (f z') y) hEτ').trans hγ
  rw [rationalSectionOrd_eq_ord_of_generator (L.restrict f) z' τ' hτ' (functionFieldMap f γ) t' ht' hW,
    rationalSectionOrd_eq_ord_of_generator L (f z') τ hτ γ _ hΦ0 hγ]
  exact ord_functionFieldMap f γ z'

end MiyaokaMori.RationalSectionOrdRestrict
end
