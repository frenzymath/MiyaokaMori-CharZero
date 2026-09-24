import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLimit
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistPiApp_Gluing
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistPiApp_TransitionBijective
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjChartCover

/-! # The chart projections of the relative twisting sheaf are isomorphisms on sections

Statement (Stacks 01LI, "the glued sheaf restricted to a piece is that piece", on sections): let
`S : X.GradedAffineAlgebra`, `Y := Proj_X S`, `T := S.twist m = lim_{V ∈ Jᵒᵖ} D(V)` with `J := X.AffineZariskiSite`,
`D(V) := (ι_V)_* O_V(m)` (`ι_V := S.projChart V`, `O_V(m) := Proj.twist (S.grading V) m`) and transition maps
`θ_h := S.twistTransition m h : D(V) ⟶ D(W)` for `h : W ≤ V`. The restriction of the limit projection
`twistπ m U : T ⟶ D(U)` to the chart `Proj S(U)` (along the open immersion `ι_U`, `Scheme.Modules.restrictFunctor`)
is an isomorphism. Equivalently (`Hom.isIso_iff_isIso_app`; the sections of the restriction over `W` are the
sections over `ι_U ''ᵁ W`, `restrictFunctor_map_app`, `rfl`): for every open `Ω ⊆ Y` contained in the image of
`ι_U`, the section map `(twistπ m U).app Ω : Γ(Ω, T) ⟶ Γ(Ω, D(U)) = Γ(ι_U⁻¹Ω, O_U(m))` is an isomorphism.

Proof (the pieces are in the four modules imported above).
0. Sections of the limit (`RelativeProjTwistPiApp_LimitSections`): `twistπ m V` are the legs of the
   limit cone `limit.cone (twistDiagram m)` with apex `T` (`twist = limit (twistDiagram m)`, `twistπ = limit.π`,
   both by definition, `twist_eq_limit`);
   evaluation at `Ω` preserves limits, so `Γ(Ω, T)` is the module of compatible families `(s_V)_V`,
   `s_V ∈ Γ(Ω, D(V))`, `θ_h.app Ω s_V = s_W`, and `(twistπ m U).app Ω` is `s ↦ s_U`.
1. Local bijectivity of the transition maps (`RelativeProjTwistPiApp_TransitionBijective`,
   `bijective_twistTransition_app`): for `h : W ≤ V` and every open `Ω ≤ im ι_W`, `θ_h.app Ω` is bijective. This
   is `RelativeProjTwistLocalIso` (`isIso_twistPullbackHom_restrictGraded`: the adjoint transpose
   `ρ_h^* O_V(m) ⟶ O_W(m)` is an isomorphism) transported to sections along the adjunction unit.
2. Support (`bijective_pushforward_presheaf_map_inf_opensRange`): `Γ(Ω, D(V)) → Γ(Ω ⊓ im ι_V, D(V))` is bijective,
   since both are `Γ(ι_V⁻¹Ω, O_V(m))` (`ι_V⁻¹(Ω ⊓ im ι_V) = ι_V⁻¹Ω`).
3. Covering (`RelativeProjChartCover`, `exists_le_le_of_projChart_mem_opensRange`): a point of
   `im ι_U ⊓ im ι_V` lies in `im ι_W` for some `W ≤ U`, `W ≤ V`; and `im ι_W ≤ im ι_V` for `W ≤ V`
   (`ρ_h ≫ ι_V = ι_W`, `map_projChart`).
4. The gluing argument (`RelativeProjTwistPiApp_Gluing`, `LocallyGluedDiagram.bijective_π_app`):
   from 1–3, for every open `Ω ≤ im ι_U` the projection `(twistπ m U).app Ω` is bijective: injectivity by the
   locality axiom of the sheaves `D(V)` on the covers `Ω ⊓ im ι_W` (`W ≤ U`, `W ≤ V`), surjectivity by
   constructing each `s_V` from `t ∈ Γ(Ω, D(U))` locally (`θ_{W≤V}⁻¹ θ_{W≤U} t` on `Ω ⊓ im ι_W`) and gluing
   (`TopCat.Sheaf.existsUnique_gluing'`). Details in that module's docstring.
5. Applying 4 to `Ω := ι_U ''ᵁ W` for all opens `W` of `Proj S(U)` gives the statement
   (`Hom.isIso_iff_isIso_app`, `ConcreteCategory.isIso_iff_bijective`).

Source: Stacks 01LI (the glued module restricts to the given modules on the pieces), 01NP/01NR;
Lemma 2.2 of the paper. Edge cases: `Ω = ∅` (both sides are the zero module); `U = ∅`
(`Proj S(∅) = ∅`, `im ι_U = ∅`, so `Ω = ∅`). Used for the chart isomorphism `twistChartIso` (Stacks 01LI/01NR).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

-- Guard (as in `RelativeProjTwistLimit`): `O_U(m)` is treated as an opaque module sheaf here.
attribute [local irreducible] AlgebraicGeometry.Proj.twist

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- Sections of the restriction of a morphism along an open immersion: `((restrictFunctor f).map φ).app W` is
`φ.app (f ''ᵁ W)` (definitional; stated separately so that the kernel checks it on generic terms). -/
theorem restrictFunctor_map_app (f : X ⟶ Y) [IsOpenImmersion f] {M N : Y.Modules} (φ : M ⟶ N)
    (W : X.Opens) : ((restrictFunctor f).map φ).app W = φ.app (f ''ᵁ W) := rfl

/-- `f⁻¹(Ω ⊓ im f) = f⁻¹Ω`. -/
theorem preimage_inf_opensRange (f : X ⟶ Y) [IsOpenImmersion f] (Ω : Y.Opens) :
    f ⁻¹ᵁ (Ω ⊓ f.opensRange) = f ⁻¹ᵁ Ω := by
  ext x
  exact ⟨fun h => h.1, fun h => ⟨h, ⟨x, rfl⟩⟩⟩

/-- A restriction map between equal opens is bijective. -/
theorem bijective_presheaf_map_of_eq (N : X.Modules) {A B : X.Opens} (i : A ⟶ B) (e : A = B) :
    Function.Bijective (N.presheaf.map i.op).hom := by
  have : IsIso i := isIso_opens_hom_of_eq i e
  exact ConcreteCategory.bijective_of_isIso _

/-- A pushforward along an open immersion is supported on the image: the restriction
`Γ(Ω, f_* N) → Γ(Ω ⊓ im f, f_* N)` is bijective (both are `Γ(f⁻¹Ω, N)`). -/
theorem bijective_pushforward_presheaf_map_inf_opensRange (f : X ⟶ Y) [IsOpenImmersion f] (N : X.Modules)
    (Ω : Y.Opens) :
    Function.Bijective (((pushforward f).obj N).presheaf.map
      (homOfLE (inf_le_left : Ω ⊓ f.opensRange ≤ Ω)).op).hom := by
  rw [pushforward_obj_presheaf_map]
  exact bijective_presheaf_map_of_eq N _ (preimage_inf_opensRange f Ω)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.GradedAffineAlgebra

variable {X : Scheme.{u}} (S : X.GradedAffineAlgebra)

/-- `W ≤ V` implies `im ι_W ≤ im ι_V` (`ρ_h ≫ ι_V = ι_W`). -/
theorem opensRange_projChart_mono {W V : X.AffineZariskiSite} (h : W ≤ V) :
    (S.projChart W).opensRange ≤ (S.projChart V).opensRange := by
  have hρι : Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) ≫ S.projChart V =
      S.projChart W := S.map_projChart h
  rintro x ⟨w, rfl⟩
  refine ⟨Proj.map (S.restrictGraded h) (S.restrict_irrelevant_le h) w, ?_⟩
  rw [← Scheme.Hom.comp_apply, hρι]

/-- Two chart images meet in a chart image (`RelativeProjChartCover`). -/
theorem exists_le_le_mem_opensRange (U V : X.AffineZariskiSite) (x : S.relativeProj.left)
    (hU : x ∈ (S.projChart U).opensRange) (hV : x ∈ (S.projChart V).opensRange) :
    ∃ W, W ≤ U ∧ W ≤ V ∧ x ∈ (S.projChart W).opensRange := by
  obtain ⟨z, rfl⟩ := hV
  obtain ⟨W, hWU, hWV, w, hw⟩ := S.exists_le_le_of_projChart_mem_opensRange z hU
  have hρι : Proj.map (S.restrictGraded hWV) (S.restrict_irrelevant_le hWV) ≫ S.projChart V =
      S.projChart W := S.map_projChart hWV
  have hw' : Proj.map (S.restrictGraded hWV) (S.restrict_irrelevant_le hWV) w = z := hw
  refine ⟨W, hWU, hWV, w, ?_⟩
  rw [← hw', ← Scheme.Hom.comp_apply, hρι]

/-- The diagram `V ↦ (ι_V)_* O_V(m)` with the chart images `im ι_V` satisfies the hypotheses of the gluing
argument of Stacks 01LI (`LocallyGluedDiagram`). -/
theorem twistDiagram_locallyGlued (m : ℤ) :
    Scheme.Modules.LocallyGluedDiagram (S.twistDiagram m) (fun V => (S.projChart V).opensRange) where
  mono := fun _ _ h => S.opensRange_projChart_mono h
  supp := fun V Ω =>
    Scheme.Modules.bijective_pushforward_presheaf_map_inf_opensRange (S.projChart V)
      (Proj.twist (S.grading V) m) Ω
  loc := fun h Ω hΩ => S.bijective_twistTransition_app m h Ω hΩ
  cover := fun U V x hU hV => S.exists_le_le_mem_opensRange U V x hU hV

/-- **Stacks 01LI on sections**: for every open `Ω ⊆ Proj_X S` inside the chart image `im ι_U`, the section map
`(twistπ m U).app Ω : Γ(Ω, O(m)) → Γ(ι_U⁻¹Ω, O_U(m))` is bijective. -/
theorem bijective_twistπ_app (m : ℤ) (U : X.AffineZariskiSite) (Ω : S.relativeProj.left.Opens)
    (hΩ : Ω ≤ (S.projChart U).opensRange) : Function.Bijective ((S.twistπ m U).app Ω).hom := by
  have : HasLimitsOfShape X.AffineZariskiSiteᵒᵖ S.relativeProj.left.Modules :=
    SheafOfModules.hasLimitsOfShape _ _
  -- the limit cone of `twistDiagram m` has apex `twist m` and legs `twistπ m V` by definition
  -- (`twist_eq_limit`); `twist` is irreducible, so the identification is made with `with_unfolding_all`
  have key := (S.twistDiagram_locallyGlued m).bijective_π_app (limit.isLimit (S.twistDiagram m)) U Ω hΩ
  with_unfolding_all exact key

/-- Stacks 01LI: the restriction of the limit projection `twistπ m U : O(m) ⟶ (ι_U)_* O_U(m)` to the chart
`Proj S(U)` is an isomorphism. On sections over an open `W ⊆ Proj S(U)` this is (by definition of
`restrictFunctor`, `rfl`) the section map `(twistπ m U).app (ι_U ''ᵁ W) : Γ(ι_U ''ᵁ W, O(m)) ⟶ Γ(W, O_U(m))`,
so by `Scheme.Modules.Hom.isIso_iff_isIso_app` the statement is: `(twistπ m U).app Ω` is an isomorphism for
every open `Ω ≤ im ι_U` (every such `Ω` is `ι_U ''ᵁ (ι_U ⁻¹ Ω)`). Natural-language proof in the module
docstring (steps 0–5). -/
theorem isIso_restrictFunctor_map_twistπ (m : ℤ) (U : X.AffineZariskiSite) :
    IsIso ((Scheme.Modules.restrictFunctor (S.projChart U)).map (S.twistπ m U)) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [Scheme.Modules.restrictFunctor_map_app]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (S.bijective_twistπ_app m U _ (Scheme.Hom.image_le_opensRange _ _))

end AlgebraicGeometry.Scheme.GradedAffineAlgebra

end
