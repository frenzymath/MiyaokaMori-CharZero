import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnit

/-!
# Chart-wise pullback of module sections: the scheme-agnostic layer

For a morphism `f : X ⟶ Y`, opens `U ⊆ X`, `W ⊆ Y` and a chart map `g : U ⟶ W` with
`g ≫ W.ι = U.ι ≫ f`, the canonical comparison `(f^* M)|_U ≅ g^* (M|_W)`, its action on pulled-back
global sections, the induced frame of `(f^* M)|_U` from a frame of `M|_W`, and the extensionality
principle for morphisms out of a framed module.

Everything here is stated for **variable** schemes and modules. `HomogeneousTupleTwistPullback`
instantiates it at the projective line; doing the same reasoning directly on the concrete objects
cost the kernel 150 s. The declarations keep the namespace
`AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback`, where `restrictedGlobalSection` has always lived.

Sources: Mathlib's module pullback adjunction and its restriction and composition comparisons;
Stacks Project, `sheaves.tex`, `lemma-push-pull-composition-modules`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback

universe u

local instance moduleChartPullbackUnitSectionOfNat (X : Scheme.{u}) (U : X.Opens) :
    OfNat (Γ(SheafOfModules.unit (R := X.ringCatSheaf), U)) 1 where
  ofNat := show Γ(X, U) from 1

/-- Restrict a genuine global module section, retaining the restriction identification. -/
def restrictedGlobalSection {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (s : Γ(M, ⊤)) : Γ(M.restrict U.ι, ⊤) :=
  (M.restrictAppIso U.ι ⊤).inv
    (M.presheaf.map (CategoryTheory.homOfLE (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top)).op s)

/-- The inverse open-immersion comparison restricts the original global section. -/
theorem restrictIso_inv_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app ⊤
        (ModuleSections.pullback f s) =
      (M.restrictAppIso f ⊤).inv
        (M.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s) := by
  simpa only [Iso.hom_inv_id_apply] using
    congrArg (fun t ↦ (M.restrictAppIso f ⊤).inv t)
      (ModuleSections.restrictIso_inv_pullback f s)

section Generic
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (W : Y.Opens)
  (g : U.toScheme ⟶ W.toScheme) (hg : g ≫ W.ι = U.ι ≫ f) (M : Y.Modules)

/-- Canonical restriction/pullback comparison for a commutative square of a morphism with two
open immersions: `(f^* M)|_U ≅ g^* (M|_W)`. All data are variables; concrete uses instantiate. -/
def chartPullbackIso :
    ((Scheme.Modules.pullback f).obj M).restrict U.ι ≅
      (Scheme.Modules.pullback g).obj (M.restrict W.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
    (Scheme.Modules.pullbackComp U.ι f).app _ ≪≫
    (Scheme.Modules.pullbackCongr hg.symm).app _ ≪≫
    ((Scheme.Modules.pullbackComp g W.ι).app _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app _).symm

/-- The canonical comparison preserves the pullback of every global section. -/
theorem chartPullbackIso_section (s : Γ(M, ⊤)) :
    (chartPullbackIso f U W g hg M).hom.app ⊤
        (restrictedGlobalSection ((Scheme.Modules.pullback f).obj M) U
          (ModuleSections.pullback f s)) =
      ModuleSections.pullback g (restrictedGlobalSection M W s) := by
  unfold chartPullbackIso restrictedGlobalSection
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [ModuleSections.restrictIso_hom_restrict]
  erw [ModuleSections.pullback_comp U.ι f s]
  rw [ModuleSections.pullbackCongr_apply, ModuleSections.pullback_comp_inv]
  erw [ModuleSections.pullback_naturality (g := g)
    ((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).inv
    (ModuleSections.pullback W.ι s)]
  rw [restrictIso_inv_pullback]


/-- Bridge form of `chartPullbackIso_section`, for instantiating at **concrete** schemes.

Kernel-cost note: a concrete statement
written with its own named constants (`P := pullbackTwist …`, `e := chartPullbackIsoOn …`) is
only *definitionally* equal to the instance of `chartPullbackIso_section`, and the difference sits
underneath projection-headed applications (`DFunLike.coe`, `Iso.hom`, `Functor.obj`), where the
kernel does not compare arguments first but unfolds both sides: that cost 108 s. Here the named
constants enter as *variables* tied by equations, so the instance is syntactically the concrete
statement and the three equations are discharged by `rfl` at top level (cheap). -/
theorem chartPullbackIso_section_of_eq {P : X.Modules}
    (hP : (Scheme.Modules.pullback f).obj M = P)
    (e : P.restrict U.ι ≅ (Scheme.Modules.pullback g).obj (M.restrict W.ι))
    (he : e = hP ▸ chartPullbackIso f U W g hg M)
    (s : Γ(M, ⊤)) (t : Γ(P, ⊤)) (ht : t = hP ▸ ModuleSections.pullback f s) :
    e.hom.app ⊤ (restrictedGlobalSection P U t) =
      ModuleSections.pullback g (restrictedGlobalSection M W s) := by
  subst hP
  have he' : e = chartPullbackIso f U W g hg M := he
  have ht' : t = ModuleSections.pullback f s := ht
  subst he'; subst ht'
  exact chartPullbackIso_section f U W g hg M s

/-- A frame of `M` on the target chart induces a frame of the pullback on the source chart. -/
def pullbackFrameIso (φ : M.restrict W.ι ≅ SheafOfModules.unit (R := W.toScheme.ringCatSheaf)) :
    ((Scheme.Modules.pullback f).obj M).restrict U.ι ≅
      SheafOfModules.unit (R := U.toScheme.ringCatSheaf) :=
  chartPullbackIso f U W g hg M ≪≫ (Scheme.Modules.pullback g).mapIso φ ≪≫ Scheme.Modules.pullbackUnitIso g

-- `SheafOfModules.unit` is an object of `SheafOfModules X.ringCatSheaf`, while `X.Modules` is a plain
-- `def` around it: `simp`/`rw` only see through that with this option (elaborator-only; the kernel
-- is unaffected).
set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the pulled-back frame uses the structure-ring map of the chart morphism. -/
theorem pullbackFrameIso_section
    (φ : M.restrict W.ι ≅ SheafOfModules.unit (R := W.toScheme.ringCatSheaf)) (s : Γ(M, ⊤)) :
    (pullbackFrameIso f U W g hg M φ).hom.app ⊤
        (restrictedGlobalSection ((Scheme.Modules.pullback f).obj M) U
          (ModuleSections.pullback f s)) =
      g.appTop (φ.hom.app ⊤ (restrictedGlobalSection M W s)) := by
  unfold pullbackFrameIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Scheme.Modules.pullbackUnitIso_hom,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [chartPullbackIso_section, ModuleSections.pullback_naturality]
  exact ModuleSections.pullback_unit g (φ.hom.app ⊤ (restrictedGlobalSection M W s))

/-- Bridge form of `pullbackFrameIso_section`; see `chartPullbackIso_section_of_eq`. -/
theorem pullbackFrameIso_section_of_eq {P : X.Modules}
    (hP : (Scheme.Modules.pullback f).obj M = P)
    (φ : M.restrict W.ι ≅ SheafOfModules.unit (R := W.toScheme.ringCatSheaf))
    (e : P.restrict U.ι ≅ SheafOfModules.unit (R := U.toScheme.ringCatSheaf))
    (he : e = hP ▸ pullbackFrameIso f U W g hg M φ)
    (s : Γ(M, ⊤)) (t : Γ(P, ⊤)) (ht : t = hP ▸ ModuleSections.pullback f s) :
    e.hom.app ⊤ (restrictedGlobalSection P U t) =
      g.appTop (φ.hom.app ⊤ (restrictedGlobalSection M W s)) := by
  subst hP
  have he' : e = pullbackFrameIso f U W g hg M φ := he
  have ht' : t = ModuleSections.pullback f s := ht
  subst he'; subst ht'
  exact pullbackFrameIso_section f U W g hg M φ s

end Generic

-- `SheafOfModules.unit` is an object of `SheafOfModules X.ringCatSheaf`, while `X.Modules` is a plain
-- `def` around it: `simp`/`rw` only see through that with this option (elaborator-only; the kernel
-- is unaffected).
set_option backward.isDefEq.respectTransparency false in
/-- Two morphisms out of a module with a frame agree once they agree on the framing section. -/
theorem hom_ext_of_frame {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ SheafOfModules.unit (R := X.ringCatSheaf)) (s : Γ(M, ⊤))
    (hs : e.hom.app ⊤ s = 1) (φ ψ : M ⟶ N) (h : φ.app ⊤ s = ψ.app ⊤ s) : φ = ψ := by
  have hinv : e.inv.app ⊤ 1 = s := by
    rw [← hs]
    change (e.hom ≫ e.inv).app ⊤ s = s
    rw [Iso.hom_inv_id]
    rfl
  apply (cancel_epi e.inv).mp
  apply N.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro W
  have ht : (N.unitHomEquiv (e.inv ≫ φ)).val (op ⊤) =
      (N.unitHomEquiv (e.inv ≫ ψ)).val (op ⊤) := by
    change φ.app ⊤ (e.inv.app ⊤ 1) = ψ.app ⊤ (e.inv.app ⊤ 1)
    simpa only [hinv] using h
  calc
    (N.unitHomEquiv (e.inv ≫ φ)).val W =
        N.val.map (CategoryTheory.homOfLE (show W.unop ≤ ⊤ from le_top)).op
          ((N.unitHomEquiv (e.inv ≫ φ)).val (op ⊤)) :=
      (PresheafOfModules.sections_property (N.unitHomEquiv (e.inv ≫ φ)) _).symm
    _ = N.val.map (CategoryTheory.homOfLE (show W.unop ≤ ⊤ from le_top)).op
          ((N.unitHomEquiv (e.inv ≫ ψ)).val (op ⊤)) := congrArg _ ht
    _ = (N.unitHomEquiv (e.inv ≫ ψ)).val W :=
      PresheafOfModules.sections_property (N.unitHomEquiv (e.inv ≫ ψ)) _

end AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback

/-! ## Restriction of module isomorphisms to smaller opens (base-free)

The namespace `AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistRestriction` is opened by name in
`WeightedPowerMapPullbackTwistGlue` / `…TwistLocal`.

Stated for **variable** modules (composing the three factors directly on the concrete sheaves cost
the kernel 21 s / 47 s). -/

namespace AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistRestriction

open HomogeneousTupleTwistPullback

universe u

/-- Restrict a global section along an arbitrary actual open immersion. -/
def restrictGlobalSection {X Y : Scheme.{u}} (M : Y.Modules) (f : X ⟶ Y)
    [IsOpenImmersion f] (s : Γ(M, ⊤)) : Γ(M.restrict f, ⊤) :=
  (M.restrictAppIso f ⊤).inv
    (M.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s)

/-- Restricting a module morphism commutes with restriction of its global sections. -/
theorem restrict_map_globalSection {X Y : Scheme.{u}} {M N : Y.Modules}
    (f : X ⟶ Y) [IsOpenImmersion f] (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.restrictFunctor f).map φ).app ⊤ (restrictGlobalSection M f s) =
      restrictGlobalSection N f (φ.app ⊤ s) := by
  change φ.app (f ''ᵁ ⊤)
    (M.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s) =
      N.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op (φ.app ⊤ s)
  exact φ.mapPresheaf.naturality_apply _ s

/-- Canonical identification of direct restriction with the two successive restrictions. -/
def nestedRestrictionIso {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (hUV : U ≤ V) : M.restrict U.ι ≅ (M.restrict V.ι).restrict (X.homOfLE hUV) :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι hUV)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE hUV) V.ι).app M

/-- The canonical nested restriction identification preserves the original global section. -/
theorem nestedRestrictionIso_section {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (hUV : U ≤ V) (s : Γ(M, ⊤)) :
    (nestedRestrictionIso M hUV).hom.app ⊤ (restrictedGlobalSection M U s) =
      restrictGlobalSection (M.restrict V.ι) (X.homOfLE hUV)
        (restrictedGlobalSection M V s) := by
  unfold nestedRestrictionIso
  simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Iso.app_hom, CategoryTheory.Iso.app_inv,
    Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ s)) =
    M.presheaf.map _ (M.presheaf.map _ s)
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]; congr 2

/-- Restrict an isomorphism between restrictions to a smaller open, transporting both ends by the
canonical nested-restriction comparisons. Stated for **variable** modules: the concrete comparison
below only instantiates it (composing the three factors directly on the concrete sheaves cost the
kernel 21 s here and 47 s in the section formula). -/
def restrictIsoOfLE {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens} (hUV : U ≤ V)
    (e : M.restrict V.ι ≅ N.restrict V.ι) : M.restrict U.ι ≅ N.restrict U.ι :=
  nestedRestrictionIso M hUV ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE hUV)).mapIso e ≪≫
    (nestedRestrictionIso N hUV).symm

/-- If `e` matches two restricted global sections on the larger open, its restriction matches
them on the smaller open. -/
theorem restrictIsoOfLE_section {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (hUV : U ≤ V) (e : M.restrict V.ι ≅ N.restrict V.ι) (s : Γ(M, ⊤)) (t : Γ(N, ⊤))
    (h : e.hom.app ⊤ (restrictedGlobalSection M V s) = restrictedGlobalSection N V t) :
    (restrictIsoOfLE hUV e).hom.app ⊤ (restrictedGlobalSection M U s) =
      restrictedGlobalSection N U t := by
  unfold restrictIsoOfLE
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [nestedRestrictionIso_section, restrict_map_globalSection, h,
    ← nestedRestrictionIso_section N hUV t]
  change ((nestedRestrictionIso N hUV).hom ≫ (nestedRestrictionIso N hUV).inv).app ⊤ _ = _
  rw [Iso.hom_inv_id]
  rfl

end AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistRestriction
