import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoProjTwistZero
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation

/-! # Auxiliary lemmas for `isIso_pullback_one_evaluation_zero`

Small lemmas for the relative part of the statement that `π^*O → π^*S_0 → O(0)` is an isomorphism: a morphism out
of the unit sheaf is determined by the image of `1`; the value of the pullback unit isomorphism `pullbackUnitIso` on
`1` is the adjunction unit; the adjoint transpose of `evaluation` is the presheaf morphism extended from the basis;
on the absolute Proj, `κ` sends `1` to `twistSection 1`.
Sources: Mathlib's `SheafOfModules.pullbackObjUnitToUnit` (the underlying morphism of `pullbackUnitIso` and its
transpose `unitToPushforwardObjUnit`); the construction of the evaluation map in `RelativeProjEvaluation`
(`evaluationLocal_eq`, `evaluationPresheafHom_app_affine`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {W : AlgebraicGeometry.Scheme.{u}}

theorem app_map_res' {M N : W.Modules} (φ : M ⟶ N) {U V : W.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app U x) :=
  _root_.PresheafOfModules.naturality_apply φ.val (homOfLE h).op x

/-- Two morphisms out of the unit sheaf that send `1` to the same section on some open `U₀` equal to `⊤` are equal
(Mathlib's `SheafOfModules.unitHomEquiv`: `unit ⟶ M` is determined by the family of images of `1`; `1|_U = 1`). -/
theorem hom_ext_unit_of_eq_top {M : W.Modules}
    (f g : (𝟙_ W.Modules) ⟶ M) (U₀ : W.Opens) (hU₀ : U₀ = ⊤)
    (h : f.val.app (op U₀) (1 : W.ringCatSheaf.obj.obj (op U₀)) =
      g.val.app (op U₀) (1 : W.ringCatSheaf.obj.obj (op U₀))) : f = g := by
  apply (SheafOfModules.unitHomEquiv M).injective
  apply Subtype.ext
  funext X
  induction X using Opposite.rec with
  | op U =>
  have hle : U ≤ U₀ := hU₀ ▸ le_top
  have e1 : (SheafOfModules.unit W.ringCatSheaf).val.map (homOfLE hle).op
      (1 : W.ringCatSheaf.obj.obj (op U₀)) = (1 : W.ringCatSheaf.obj.obj (op U)) :=
    _root_.PresheafOfModules.unit_map_one _ _
  have key : f.val.app (op U) (1 : W.ringCatSheaf.obj.obj (op U)) =
      g.val.app (op U) (1 : W.ringCatSheaf.obj.obj (op U)) :=
    (congrArg (fun x => f.val.app (op U) x) e1.symm).trans
      ((_root_.PresheafOfModules.naturality_apply f.val (homOfLE hle).op
          (1 : W.ringCatSheaf.obj.obj (op U₀))).trans
        ((congrArg (fun x => M.val.map (homOfLE hle).op x) h).trans
          ((_root_.PresheafOfModules.naturality_apply g.val (homOfLE hle).op
            (1 : W.ringCatSheaf.obj.obj (op U₀))).symm.trans
            (congrArg (fun x => g.val.app (op U) x) e1))))
  exact (SheafOfModules.unitHomEquiv_apply_coe M f (op U)).trans
    (key.trans (SheafOfModules.unitHomEquiv_apply_coe M g (op U)).symm)

/-- The inverse of the comparison isomorphism `restrictUnitIso` of unit sheaves sends `1` to `1` (its components are the
inverses of the ring isomorphisms `appIso`). -/
theorem restrictUnitIso_inv_app_one {W' : AlgebraicGeometry.Scheme.{u}} (ι : W ⟶ W')
    [AlgebraicGeometry.IsOpenImmersion ι] (U : W.Opens) :
    (AlgebraicGeometry.Scheme.Modules.restrictUnitIso ι).inv.app U (1 : Γ(W, U)) =
      (1 : Γ(W', ι ''ᵁ U)) :=
  map_one (ι.appIso U).inv.hom

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {Y Z : AlgebraicGeometry.Scheme.{u}}

/-- The value of the inverse of `pullbackUnitIso f` on `f.app T n` is the value of the adjunction unit
`𝟙_Z → f_* f^* 𝟙_Z` on `n`. (Mathlib: the adjoint transpose of `pullbackObjUnitToUnit` is the morphism of sheaves of
rings `unitToPushforwardObjUnit`.) -/
theorem pullbackUnitIso_inv_app_app (f : Y ⟶ Z) (T : Z.Opens) (n : Γ(Z, T)) :
    AlgebraicGeometry.Scheme.Modules.Hom.app (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).inv
        (f ⁻¹ᵁ T) (f.app T n) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Z.ringCatSheaf)).app T n := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  have h2 := congrArg (fun k => k.val.app (op T) n) h
  have h3 : AlgebraicGeometry.Scheme.Modules.Hom.app
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom (f ⁻¹ᵁ T)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Z.ringCatSheaf)).app T n) = f.app T n := h2
  rw [← h3]
  have e := congrArg (fun k => AlgebraicGeometry.Scheme.Modules.Hom.app k (f ⁻¹ᵁ T)
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Z.ringCatSheaf)).app T n))
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom_inv_id
  exact e

/-- Naturality of the adjunction unit, sectionwise: `f^*φ` applied to a pulled-back section is the pullback of the
section obtained by applying `φ`. -/
theorem pullback_map_app_unit_app (f : Y ⟶ Z) {M N : Z.Modules} (φ : M ⟶ N) (T : Z.Opens) (x : Γ(M, T)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map φ).app (f ⁻¹ᵁ T)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app T x) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).app T (φ.app T x) := by
  have h := congrArg (fun k => AlgebraicGeometry.Scheme.Modules.Hom.app k T x)
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality φ)
  simp only [Functor.id_map, Functor.comp_map, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply] at h
  exact h.symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- `κ` sends the global section `1` to `twistSection 𝒜 1` (pointwise `(1 : A_(x)).val = 1 = mk 1 1`). -/
theorem unitToTwistZero_app_top_one :
    (AlgebraicGeometry.Proj.unitToTwistZero 𝒜).app ⊤ (1 : Γ(AlgebraicGeometry.Proj 𝒜, ⊤)) =
      AlgebraicGeometry.Proj.twistSection 𝒜 (1 : A) (SetLike.one_mem_graded 𝒜) := by
  apply Subtype.ext
  funext x
  exact HomogeneousLocalization.val_one.trans (Localization.mk_one).symm

/-- Equality of `twistSection` for homogeneous elements is well defined (proof irrelevance). -/
theorem twistSection_congr {d : ℕ} {f g : A} (h : f = g) (hf : f ∈ 𝒜 d) :
    AlgebraicGeometry.Proj.twistSection 𝒜 f hf = AlgebraicGeometry.Proj.twistSection 𝒜 g (h ▸ hf) := by
  subst h
  rfl

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- The adjoint transpose of `evaluation S m` is the morphism of sheaves of modules packaged from the presheaf morphism
extended from the basis (`Equiv.apply_symm_apply`). -/
theorem homEquiv_evaluation (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Scheme.relativeProj S).hom).homEquiv _ _
      (AlgebraicGeometry.Scheme.relativeProj.evaluation S m) =
    SheafOfModules.Hom.mk (PresheafOfModules.homMk
      (AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom S m)
      (fun V r s => AlgebraicGeometry.Scheme.relativeProj.evaluationPresheafHom_smul S m V.unop r s)) :=
  Equiv.apply_symm_apply _ _

/-- `sectionsOf V 0 (S.one.app V 1)` is the `1` of the section ring. -/
theorem sectionsOf_one_app_one (V : X.Opens) :
    ((S.sectionsOf V 0 (S.one.app V (1 : Γ(X, V))) : S.sectionsGrading V 0) : S.sectionsRing V) = 1 :=
  congrArg Subtype.val (map_one (S.sectionsUnit V))

end AlgebraicGeometry.Scheme.relativeProj

end
