import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdRestrict
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02rtScheme
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameIsFrame
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueIsoOfFrames
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineCartierPresentationOfFrames

/-! # Pullback of rational sections along a dominant morphism

**Pullback of rational sections along a dominant morphism**: `X`, `Y` integral schemes, `f : X ⟶ Y` sending
the generic point to the generic point (dominant), `L` a module sheaf on `Y`. This module provides

* the embedding of function fields `R(Y) → R(X)`: `AlgebraicGeometry.functionFieldAlgebra f hf` (the stalk
  map at the generic point);
* the pullback of rational sections `f^* : L_{η_Y} → (f^*L)_{η_X}` (`rationalSectionPullback`): first
  transport `L_{η_Y}` to `L_{f η_X}` along `f η_X = η_Y` (`AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes`), then apply the
  stalk unit of the pullback module `AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit` (the unit of the pullback–pushforward
  adjunction on stalks, semilinear with respect to `f.stalkMap η_X`);
* its compatibility with the function field embedding, with `ord` and divisors, and with frames
  (`rationalSectionPullback_smul`, `rationalSectionPullback_ne_zero`, `rationalSectionOrd_rationalSectionPullback`,
  `properPushforward_rationalSectionDivisor_pullback`, `exists_frame_genericCoordinate_rationalSectionPullback`;
  the last one through the pullback of frame sections, `isFrame_unitSec` and `frameIso`).

This is needed for Stacks 02ST (`f_*(div_{f^*L}(f^*s)) = [R(X):R(Y)]·div_L(s)`) and the general proper case
of Stacks 02SU / 02S2 built on it, which require pulling back rational sections from `Y` to `X`; the open
immersion case is `genericStalkMap` in `RationalSectionOrdRestrict` (in the opposite direction).

Sources: the proof of Stacks 02ST ("we may assume `L = O_Y`, in this case `s` corresponds to a rational
function `g ∈ R(Y)`"); Stacks 01CD (`f^*O_Y = O_X`); Stacks `sheaves.tex`, `lemma-stalk-pullback-modules`
(`(f^*M)_x = O_{X,x} ⊗_{O_{Y,f x}} M_{f x}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Divisors

section PullbackFrame

variable {X' Y' : AlgebraicGeometry.Scheme.{u}}

/-- A single section `e` is a frame iff the one-element family `fun _ => e` indexed by `PUnit` is a
`DualPullback.IsFrameOn` frame (both say that `r ↦ r • e|_W` is bijective on every `W ≤ V`, up to
`Γ(X, W) ≃ (PUnit → Γ(X, W))`). -/
theorem isFrameOn_punit_iff (F : Y'.Modules) {V : Y'.Opens} (e : Γ(F, V)) :
    MiyaokaMori.DualPullback.IsFrameOn F (fun _ : PUnit.{u + 1} => e) ↔ IsFrame F V e := by
  unfold MiyaokaMori.DualPullback.IsFrameOn IsFrame
  refine forall₂_congr fun W hW => ?_
  have hfun : (⇑(MiyaokaMori.DualPullback.frameMap F (fun _ : PUnit.{u + 1} => e) hW)) =
      (fun r : Γ(Y', W) => r • F.res hW e) ∘ (Equiv.punitArrowEquiv Γ(Y', W)) := by
    funext r
    rw [MiyaokaMori.DualPullback.frameMap_apply, Fintype.sum_unique]
    rfl
  rw [hfun]
  exact Equiv.bijective_comp _ _

/-- **The pullback of a frame is a frame** (single-section version): if `e` is a frame of `F` on `V`, the
adjunction unit section `unit(e) ∈ Γ(p^*F, p⁻¹V)` is a frame of `p^*F` on `p⁻¹V`. This is
`MiyaokaMori.DualPullback.isFrameOn_pullback` with `I = PUnit`. -/
theorem isFrame_unitSec (p : X' ⟶ Y') (F : Y'.Modules) {V : Y'.Opens} {e : Γ(F, V)}
    (he : IsFrame F V e) :
    IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback p).obj F) (p ⁻¹ᵁ V)
      (MiyaokaMori.DualPullback.unitSec p F e) := by
  have h1 : MiyaokaMori.DualPullback.IsFrameOn F (fun _ : PUnit.{u + 1} => e) :=
    (isFrameOn_punit_iff F e).mpr he
  have h2 := MiyaokaMori.DualPullback.isFrameOn_pullback p F V h1
  exact (isFrameOn_punit_iff _ _).mp h2

/-- For any rank-one trivialization `e : M|_U ≅ free(Fin 1)`, the germ at the generic point of the section
`(e ≪≫ moduleFreeOneIsoUnit)⁻¹(1)` has coordinate `1` (`lineStalkEquivOfTrivialization_germ`, `inv_hom_id`). -/
theorem genericCoordinate_germ_trivialization_inv_one {Z : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral Z] (M : Z.Modules) (U : Z.Opens) (hU : Nonempty U)
    (e : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1))) :
    AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Z M U hU e
      (M.presheaf.germ (U.ι ''ᵁ ⊤) (genericPoint Z)
        ⟨⟨genericPoint Z, AlgebraicGeometry.Divisors.LineGenericCoordinates.genericPoint_mem_of_nonempty Z U hU⟩,
          trivial, rfl⟩
        ((e ≪≫ AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).inv.val.app (op ⊤)
          (1 : Γ(U.toScheme, ⊤)))) = 1 := by
  unfold AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate
  refine (AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization_germ Z M U
    ⟨genericPoint Z, AlgebraicGeometry.Divisors.LineGenericCoordinates.genericPoint_mem_of_nonempty Z U hU⟩ e ⊤ trivial
    _).trans ?_
  have h : (e ≪≫ AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).hom.val.app (op ⊤)
      ((e ≪≫ AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).inv.val.app (op ⊤)
        (1 : Γ(U.toScheme, ⊤))) = (1 : Γ(U.toScheme, ⊤)) :=
    ConcreteCategory.congr_hom
      (congrArg (fun k : SheafOfModules.unit U.toScheme.ringCatSheaf ⟶ _ => k.val.app (op ⊤))
        (e ≪≫ AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).inv_hom_id)
      (1 : Γ(U.toScheme, ⊤))
  rw [h]
  exact map_one _

end PullbackFrame

variable {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
  [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y)
  (hf : f.base (genericPoint X) = genericPoint Y)

/-- Dominance gives `f η_X = η_Y`, so the stalk of `L` at the generic point of `Y` can be transported to
`f η_X` (a specialization map along an equality). -/
def genericStalkTransport (L : Y.Modules) :
    L.presheaf.stalk (genericPoint Y) → L.presheaf.stalk (f.base (genericPoint X)) :=
  AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes Y L (specializes_of_eq hf)

/-- **The pullback of rational sections along a dominant morphism** `f^* : L_{η_Y} → (f^*L)_{η_X}`: the
composite of `AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes` (transporting `L_{η_Y}` to `L_{f η_X}`, semilinear with
respect to `Y.presheaf.stalkSpecializes`) and `AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit` (the stalk unit
`M_{f x} → (f^*M)_x` of the pullback module, semilinear with respect to `f.stalkMap x`). -/
def rationalSectionPullback (L : Y.Modules) (s : L.presheaf.stalk (genericPoint Y)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).presheaf.stalk (genericPoint X) :=
  AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X) (genericStalkTransport f hf L s)

@[simp]
theorem rationalSectionPullback_zero (L : Y.Modules) :
    rationalSectionPullback f hf L 0 = 0 := by
  show AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X)
      (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes Y L (specializes_of_eq hf) 0) = 0
  rw [map_zero, map_zero]

theorem rationalSectionPullback_add (L : Y.Modules)
    (s t : L.presheaf.stalk (genericPoint Y)) :
    rationalSectionPullback f hf L (s + t)
      = rationalSectionPullback f hf L s + rationalSectionPullback f hf L t := by
  show AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X)
      (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes Y L (specializes_of_eq hf) (s + t)) = _
  rw [map_add, map_add]
  rfl

/-- **Compatibility with the function field embedding (semilinearity)**: `f^*(γ · s) = (image of γ in R(X)) · f^*s`.
Here `R(Y) → R(X)` is the `algebraMap` of `AlgebraicGeometry.functionFieldAlgebra f hf`, i.e.
`(Y.presheaf.stalkCongr _).hom ≫ f.stalkMap (genericPoint X)`; the proof chains the `map_smulₛₗ` of the two
semilinear maps. -/
theorem rationalSectionPullback_smul (L : Y.Modules) (γ : Y.functionField)
    (s : L.presheaf.stalk (genericPoint Y)) :
    letI := AlgebraicGeometry.functionFieldAlgebra f hf
    rationalSectionPullback f hf L (γ • s)
      = (algebraMap Y.functionField X.functionField γ) • rationalSectionPullback f hf L s := by
  letI := AlgebraicGeometry.functionFieldAlgebra f hf
  show AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X)
      (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes Y L (specializes_of_eq hf) (γ • s)) = _
  rw [(AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes Y L (specializes_of_eq hf)).map_smulₛₗ,
    (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X)).map_smulₛₗ]
  rfl

omit [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] in
/-- The stalk unit of the pullback preserves generators: if `τ` generates `L_{f x}` then `unit(τ)` generates
`(f^*L)_x` (Stacks `sheaves.tex`, `lemma-stalk-pullback-modules`: `(f^*L)_x = O_{X,x} ⊗ L_{f x}`, generated by
`a ⊗ rτ = a f(r) • (1 ⊗ τ)`). -/
theorem span_modulePullbackStalkUnit_eq_top (L : Y.Modules) (x : X)
    (τ : L.presheaf.stalk (f.base x))
    (hτ : Submodule.span (Y.presheaf.stalk (f.base x)) {τ} = ⊤) :
    Submodule.span (X.presheaf.stalk x) {AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L x τ} = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  obtain ⟨t, rfl⟩ :=
    (MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective f L x).2 v
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul a m =>
    rw [AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap_tmul]
    have hm : m ∈ Submodule.span (Y.presheaf.stalk (f.base x)) {τ} := by rw [hτ]; trivial
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hm
    rw [(AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L x).map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

omit [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y] in
/-- The stalk unit of the pullback is compatible with specialization maps (equality on germs). -/
theorem modulePullbackStalkUnit_specializes (L : Y.Modules) {x x' : X} (h : x ⤳ x')
    (m : L.presheaf.stalk (f.base x')) :
    AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) h
        (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L x' m) =
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L x
        (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes Y L (f.base.hom.map_specializes h) m) := by
  obtain ⟨U, hU, m0, rfl⟩ := L.presheaf.exists_germ_eq m
  have e1 := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ f L x' U hU m0
  have e2 := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ f L x U
    ((f.base.hom.map_specializes h).mem_open U.isOpen hU) m0
  change AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X _ h
      (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom f L x' _) =
    AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom f L x
      (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes Y L (f.base.hom.map_specializes h) _)
  erw [e1, AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes_germ, AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes_germ, e2]

/-- The pullback of rational sections is compatible with "specialize to the generic point":
`f^*(j_Y m) = j_X(unit_x m)` for `m ∈ L_{f x}`. -/
theorem rationalSectionPullback_toGenericFiber (L : Y.Modules) (x : X)
    (m : L.presheaf.stalk (f.base x)) :
    rationalSectionPullback f hf L (AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber Y L (f.base x) m) =
      AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) x
        (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L x m) := by
  unfold AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber
  rw [modulePullbackStalkUnit_specializes]
  unfold rationalSectionPullback genericStalkTransport
  rw [MiyaokaMori.RationalSectionOrdRestrict.moduleStalkSpecializes_comp]

/-- The commutative square of the function field embedding and the stalk maps:
`O_{Y,f x} → R(Y) → R(X)` equals `O_{Y,f x} → O_{X,x} → R(X)`. -/
theorem functionFieldAlgebra_algebraMap_stalk (x : X) (u : Y.presheaf.stalk (f.base x)) :
    letI := AlgebraicGeometry.functionFieldAlgebra f hf
    algebraMap Y.functionField X.functionField
        (algebraMap (Y.presheaf.stalk (f.base x)) Y.functionField u)
      = algebraMap (X.presheaf.stalk x) X.functionField ((f.stalkMap x).hom u) := by
  letI := AlgebraicGeometry.functionFieldAlgebra f hf
  have hηx : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have hηy : genericPoint Y ⤳ f.base x := (genericPoint_spec Y).specializes trivial
  have key : Y.presheaf.stalkSpecializes hηy ≫
      (Y.presheaf.stalkCongr (Inseparable.of_eq hf.symm)).hom ≫ f.stalkMap (genericPoint X) =
        f.stalkMap x ≫ X.presheaf.stalkSpecializes hηx := by
    show Y.presheaf.stalkSpecializes hηy ≫ Y.presheaf.stalkSpecializes (specializes_of_eq hf) ≫
      f.stalkMap (genericPoint X) = _
    rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
    exact AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap f (genericPoint X) x hηx
  exact congrArg (fun φ => φ.hom u) key

include hf in
/-- For dominant `f`, the stalk map `O_{Y,f η_X} → R(X)` at the generic point is injective (a field
homomorphism through `stalkCongr`). -/
theorem stalkMap_genericPoint_injective :
    Function.Injective (f.stalkMap (genericPoint X)).hom := by
  letI := AlgebraicGeometry.functionFieldAlgebra f hf
  let e := Y.presheaf.stalkCongr (Inseparable.of_eq hf.symm)
  intro a b hab
  have ha : e.hom.hom (e.inv.hom a) = a := e.inv_hom_id_apply a
  have hb : e.hom.hom (e.inv.hom b) = b := e.inv_hom_id_apply b
  have h2 : algebraMap Y.functionField X.functionField (e.inv.hom a) =
      algebraMap Y.functionField X.functionField (e.inv.hom b) := by
    change (f.stalkMap _).hom (e.hom.hom (e.inv.hom a)) = (f.stalkMap _).hom (e.hom.hom (e.inv.hom b))
    rw [ha, hb]; exact hab
  have h3 := (algebraMap Y.functionField X.functionField).injective h2
  rw [← ha, ← hb, h3]

/-- **The pullback of a nonzero rational section is nonzero.**

Proof: let `m :=` the transport of `s` to `L_{f η_X}`, nonzero (specializations between equal points are
mutually inverse). Take a generator `τ` of `L_{f η_X}`, `m = r • τ` with `r ≠ 0`. `unit(τ)` generates
`(f^*L)_{η_X}` (`span_modulePullbackStalkUnit_eq_top`), the nonzero generic stalk of a line bundle, so
`unit(τ) ≠ 0`; `f^*s = unit(m) = f^♯(r) • unit(τ)` with `f^♯(r) ≠ 0` (`stalkMap_genericPoint_injective`), a
nonzero product in a vector space over the field `R(X)`.
Sources: Stacks `sheaves.tex`, `lemma-stalk-pullback-modules`; the implicit step "`f^*s` is still a nonzero
meromorphic section" in the proof of Stacks 02ST. -/
theorem rationalSectionPullback_ne_zero (L : Y.Modules) [L.IsLineBundle]
    (s : L.presheaf.stalk (genericPoint Y)) (hs : s ≠ 0) :
    rationalSectionPullback f hf L s ≠ 0 := by
  have hm : genericStalkTransport f hf L s ≠ 0 := by
    intro h0
    apply hs
    have h1 := congrArg (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes Y L (specializes_of_eq hf.symm)) h0
    unfold genericStalkTransport at h1
    rwa [MiyaokaMori.RationalSectionOrdRestrict.moduleStalkSpecializes_comp,
      MiyaokaMori.RationalSectionOrdRestrict.moduleStalkSpecializes_self, map_zero] at h1
  obtain ⟨τ, hτ⟩ := exists_stalk_generator L (f.base (genericPoint X))
  have hmem : genericStalkTransport f hf L s ∈
      Submodule.span (Y.presheaf.stalk (f.base (genericPoint X))) {τ} := by rw [hτ]; trivial
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hm (by rw [← hr, zero_smul])
  have hgen := span_modulePullbackStalkUnit_eq_top f L (genericPoint X) τ hτ
  obtain ⟨v, hv⟩ := exists_ne_zero_of_trivialization ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)
  have hτ0 : AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X) τ ≠ 0 := by
    intro h0
    apply hv
    have hv' : v ∈ Submodule.span (X.presheaf.stalk (genericPoint X))
        {AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X) τ} := by rw [hgen]; trivial
    rw [h0, Submodule.span_singleton_eq_bot.mpr rfl] at hv'
    exact (Submodule.mem_bot _).mp hv'
  have hfr : (f.stalkMap (genericPoint X)).hom r ≠ 0 := by
    intro h0
    apply hr0
    exact stalkMap_genericPoint_injective f hf (h0.trans (map_zero _).symm)
  show AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X) (genericStalkTransport f hf L s) ≠ 0
  rw [← hr, (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L (genericPoint X)).map_smulₛₗ]
  exact smul_ne_zero hfr hτ0

variable [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]

/-- **Compatibility with frames**: a frame of `L` on `U ∋ η_Y` pulls back to a frame of `f^*L` on `f⁻¹U`, and
in this pair of frames "pull back the rational section" is "transport the coordinate along the function
field embedding". This is the precise form of the first step of the proof of Stacks 02ST ("we may assume
`L = O_Y`, in which case `s` corresponds to a rational function `g ∈ R(Y)`"), with local frames instead of a
global trivialization of `L`.

Proof (through frame sections):
1. Let `E := e ≪≫ moduleFreeOneIsoUnit`, `σ₀ := E⁻¹(1) ∈ Γ(L, U.ι ''ᵁ ⊤)`; `σ₀` is a frame
   (`isFrame_restrictIso_inv_one`), and restricting to `U` gives a frame `σ` (`U.ι ''ᵁ ⊤ = U`). In `e` the
   germ of `σ` at the generic point has coordinate `1` (`genericCoordinate_germ_trivialization_inv_one`).
2. `σ' := unit(σ) ∈ Γ(f^*L, f⁻¹U)` is a frame (`isFrame_unitSec`, i.e. `DualPullback.isFrameOn_pullback` with a
   one-element index); `e' :=` the trivialization `frameIso` given by `σ'`, in which the germ of `σ'` at the
   generic point has coordinate `1` (`genericCoordinate_frameIso_germ`).
3. `s = c_e(s) • (σ)_η` (the coordinate is an `R(Y)`-linear isomorphism and both sides have coordinate
   `c_e(s)`); `f^*((σ)_η) = (σ')_η` (`moduleStalkSpecializes_germ`, `modulePullbackStalkUnitAddHom_germ`: the
   stalk unit sends germs to germs of unit sections); hence `f^*s = algebraMap(c_e s) • (σ')_η`
   (`rationalSectionPullback_smul`), whose `e'`-coordinate is `algebraMap(c_e s)`.
Sources: the first paragraph of the proof of Stacks 02ST; Stacks 01CD. -/
theorem exists_frame_genericCoordinate_rationalSectionPullback (L : Y.Modules)
    (U : Y.Opens) (hU : Nonempty U)
    (e : L.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1))) :
    letI := AlgebraicGeometry.functionFieldAlgebra f hf
    ∃ (hU' : Nonempty (f ⁻¹ᵁ U : X.Opens))
      (e' : ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
        SheafOfModules.free (R := (f ⁻¹ᵁ U : X.Opens).toScheme.ringCatSheaf) (ULift.{u} (Fin 1))),
      ∀ s : L.presheaf.stalk (genericPoint Y),
        AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate X ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)
            (f ⁻¹ᵁ U) hU' e' (rationalSectionPullback f hf L s)
          = algebraMap Y.functionField X.functionField
              (AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Y L U hU e s) := by
  letI := AlgebraicGeometry.functionFieldAlgebra f hf
  have hη : genericPoint Y ∈ U := AlgebraicGeometry.Divisors.LineGenericCoordinates.genericPoint_mem_of_nonempty Y U hU
  have hηX : genericPoint X ∈ (f ⁻¹ᵁ U : X.Opens) := by
    show f.base (genericPoint X) ∈ U
    rw [hf]; exact hη
  have hU' : Nonempty (f ⁻¹ᵁ U : X.Opens) := ⟨⟨_, hηX⟩⟩
  -- 1. the frame section of `e` on `U`
  let E := e ≪≫ AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme
  let σ₀ : Γ(L, U.ι ''ᵁ ⊤) := E.inv.val.app (op ⊤) (1 : Γ(U.toScheme, ⊤))
  have hσ₀ : IsFrame L (U.ι ''ᵁ ⊤) σ₀ := isFrame_restrictIso_inv_one E
  have hle : U ≤ U.ι ''ᵁ ⊤ := U.ι_image_top.ge
  let σ : Γ(L, U) := L.res hle σ₀
  have hσ : IsFrame L U σ := hσ₀.restrict hle
  -- 2. its pullback is a frame of `f^*L` on `f⁻¹U`
  have hσ' : IsFrame ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) (f ⁻¹ᵁ U)
      (MiyaokaMori.DualPullback.unitSec f L σ) := isFrame_unitSec f L hσ
  refine ⟨hU', MiyaokaMori.LineCartierPresentationOfFrames.frameIso hσ', fun s => ?_⟩
  have h1 := MiyaokaMori.LineCartierPresentationOfFrames.genericCoordinate_frameIso_germ hσ' hU'
  have h2 : AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Y L U hU e
      (L.presheaf.germ U (genericPoint Y) hη σ) = 1 := by
    have h0 := genericCoordinate_germ_trivialization_inv_one L U hU e
    rwa [show L.presheaf.germ U (genericPoint Y) hη σ =
        L.presheaf.germ (U.ι ''ᵁ ⊤) (genericPoint Y) ⟨⟨genericPoint Y, hη⟩, trivial, rfl⟩ σ₀ from
      L.presheaf.germ_res_apply (homOfLE hle) (genericPoint Y) hη σ₀]
  -- 3. `s = c_e(s) • σ_η`, and the pullback of `σ_η` is `σ'_η`
  have h3 : s = AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Y L U hU e s •
      L.presheaf.germ U (genericPoint Y) hη σ := by
    apply (AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Y L U hU e).injective
    rw [(AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Y L U hU e).map_smul, h2, smul_eq_mul,
      mul_one]
  have h4 : rationalSectionPullback f hf L (L.presheaf.germ U (genericPoint Y) hη σ) =
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).presheaf.germ (f ⁻¹ᵁ U) (genericPoint X)
        hηX (MiyaokaMori.DualPullback.unitSec f L σ) := by
    unfold rationalSectionPullback genericStalkTransport
    rw [AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes_germ]
    exact AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ f L (genericPoint X) U _ σ
  have h5 : rationalSectionPullback f hf L s =
      algebraMap Y.functionField X.functionField
        (AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Y L U hU e s) •
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).presheaf.germ (f ⁻¹ᵁ U) (genericPoint X)
        hηX (MiyaokaMori.DualPullback.unitSec f L σ) := by
    conv_lhs => rw [h3]
    rw [rationalSectionPullback_smul, h4]
  rw [h5, (AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate X _ (f ⁻¹ᵁ U) hU' _).map_smul, h1,
    smul_eq_mul, mul_one]

/-- **Pointwise order formula (generator version)**: for `x ∈ X`, `τ` a generator of `L_{f x}` and
`γ • j_Y(τ) = s ≠ 0`, `ord_{x, f^*L}(f^*s) = ord_x(image of γ in R(X))`.

Proof: `unit_x(τ)` generates `(f^*L)_x` (`span_modulePullbackStalkUnit_eq_top`);
`f^*s = f^*(γ • j_Y τ) = algebraMap γ • f^*(j_Y τ) = algebraMap γ • j_X(unit_x τ)`
(`rationalSectionPullback_smul`, `rationalSectionPullback_toGenericFiber`); `f^*s ≠ 0`
(`rationalSectionPullback_ne_zero`); then the arbitrary-generator characterization
`rationalSectionOrd_eq_ord_of_generator`. Sources: Stacks 02SE, 02SH; the first paragraph of the proof of 02ST. -/
theorem rationalSectionOrd_rationalSectionPullback_of_generator (L : Y.Modules) [L.IsLineBundle]
    (x : X) (τ : L.presheaf.stalk (f.base x))
    (hτ : Submodule.span (Y.presheaf.stalk (f.base x)) {τ} = ⊤)
    (γ : Y.functionField) (s : L.presheaf.stalk (genericPoint Y)) (hs : s ≠ 0)
    (hγ : γ • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber Y L (f.base x) τ = s) :
    letI := AlgebraicGeometry.functionFieldAlgebra f hf
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).rationalSectionOrd
        (rationalSectionPullback f hf L s) x
      = X.ord (algebraMap Y.functionField X.functionField γ) x := by
  letI := AlgebraicGeometry.functionFieldAlgebra f hf
  have hX : algebraMap Y.functionField X.functionField γ •
      AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) x
        (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit f L x τ) = rationalSectionPullback f hf L s := by
    rw [← rationalSectionPullback_toGenericFiber f hf, ← rationalSectionPullback_smul f hf, hγ]
  exact rationalSectionOrd_eq_ord_of_generator _ x _ (span_modulePullbackStalkUnit_eq_top f L x τ hτ)
    _ _ (rationalSectionPullback_ne_zero f hf L s hs) hX

/-- **Compatibility at the level of `ord`**: on the preimage of a frame open `U` of `L`, the order of `f^*s` is
the order of the coordinate of `s` transported along the function field embedding. (The hypothesis
`[L.IsLineBundle]` is needed since the generator characterization requires `f^*L` to be a line bundle.)

Proof: for `s = 0` both sides are `ord(0)`. For `s ≠ 0` take a generator `τ` of `L_{f z′}` and `γ` with
`γ • j τ = s`; the left side is `ord_{z′}(algebraMap γ)` (`rationalSectionOrd_rationalSectionPullback_of_generator`);
on the right, `c(s) = γ · c(j τ)` where `c(j τ)` is the image in `R(Y)` of the unit `e_{f z′}(τ)` of
`O_{Y,f z′}`, whose image in `R(X)` is the image of `f^♯(e_{f z′}(τ)) ∈ O_{X,z′}^×`
(`functionFieldAlgebra_algebraMap_stalk`), of order `0`; `Scheme.ord_mul` finishes. -/
theorem rationalSectionOrd_rationalSectionPullback (L : Y.Modules) [L.IsLineBundle]
    (U : Y.Opens) (hU : Nonempty U)
    (e : L.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (s : L.presheaf.stalk (genericPoint Y)) (z' : X) (hz' : f.base z' ∈ U) :
    letI := AlgebraicGeometry.functionFieldAlgebra f hf
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).rationalSectionOrd
        (rationalSectionPullback f hf L s) z'
      = X.ord (algebraMap Y.functionField X.functionField
          (AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Y L U hU e s)) z' := by
  letI := AlgebraicGeometry.functionFieldAlgebra f hf
  by_cases hs : s = 0
  · subst hs
    obtain ⟨V, hzV, ⟨eV⟩⟩ :=
      exists_trivialization ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) z'
    refine (rationalSectionOrd_eq_ord_genericCoordinate' _ V z' hzV eV
      (rationalSectionPullback f hf L 0)).trans ?_
    rw [rationalSectionPullback_zero, map_zero, map_zero, map_zero]
  obtain ⟨τ, hτ⟩ := exists_stalk_generator L (f.base z')
  obtain ⟨γ, hγ⟩ := exists_smul_toGenericFiber_eq L (f.base z') τ hτ s
  rw [rationalSectionOrd_rationalSectionPullback_of_generator f hf L z' τ hτ γ s hs hγ]
  let ez := AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization Y L U ⟨f.base z', hz'⟩ e
  let c := AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate Y L U hU e
  have hj : c (AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber Y L (f.base z') τ) =
      algebraMap (Y.presheaf.stalk (f.base z')) Y.functionField (ez τ) :=
    AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization_toGenericFiber Y L U e
      ⟨f.base z', hz'⟩ _ τ
  have hu : IsUnit (ez τ) := by
    have hmem : ez.symm 1 ∈ Submodule.span (Y.presheaf.stalk (f.base z')) {τ} := by
      rw [hτ]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : a * ez τ = 1 := by
      have h2 := (ez.map_smul a τ).symm.trans (congrArg ez ha)
      rwa [LinearEquiv.apply_symm_apply, smul_eq_mul] at h2
    exact IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact h1)
  have hcs : c s = γ * c (AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber Y L (f.base z') τ) :=
    (congrArg c hγ.symm).trans (c.map_smul γ _)
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    exact hs (hγ.symm.trans (zero_smul _ _))
  have hunit : IsUnit ((f.stalkMap z').hom (ez τ)) := hu.map _
  have hne1 : algebraMap Y.functionField X.functionField γ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap Y.functionField X.functionField).injective).mpr hγ0
  have hne2 : algebraMap (X.presheaf.stalk z') X.functionField ((f.stalkMap z').hom (ez τ)) ≠ 0 :=
    (hunit.map _).ne_zero
  show X.ord (algebraMap Y.functionField X.functionField γ) z' =
    X.ord (algebraMap Y.functionField X.functionField (c s)) z'
  rw [hcs, map_mul, hj, functionFieldAlgebra_algebraMap_stalk f hf z',
    AlgebraicGeometry.Scheme.ord_mul hne1 hne2, ord_algebraMap_of_isUnit z' hunit, add_zero]

omit [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y] in
/-- `functionFieldDegree f` (the residue field version `[κ(η_X) : κ(f η_X)]`) equals `[R(X) : R(Y)]` for the
function field embedding `functionFieldAlgebra f hf` (the two algebra structures agree pointwise; the same
argument as for `dominantFunctionFieldMap` in `PullbackDegreeFiniteCover`). -/
theorem functionFieldDegree_eq_finrank_functionFieldAlgebra :
    functionFieldDegree f = @Module.finrank Y.functionField X.functionField _ _
      (@Algebra.toModule _ _ _ _ (AlgebraicGeometry.functionFieldAlgebra f hf)) := by
  rw [functionFieldDegree_eq_finrank f hf]
  have hmap : (Y.presheaf.stalkCongr (Inseparable.of_eq hf.symm)).hom ≫ f.stalkMap (genericPoint X) =
      Y.functionFieldIsoResidueField.hom ≫ (Y.residueFieldCongr hf.symm).hom ≫
        f.residueFieldMap (genericPoint X) ≫ X.functionFieldIsoResidueField.inv := by
    apply (cancel_mono (X.residue (genericPoint X))).1
    simp only [Category.assoc]
    rw [← AlgebraicGeometry.Scheme.residue_residueFieldMap]
    rw [← Category.assoc]
    rw [← AlgebraicGeometry.Scheme.residue_residueFieldCongr]
    simp [AlgebraicGeometry.Scheme.functionFieldIsoResidueField]
    exact hf.symm
  have hA : (Y.functionFieldIsoResidueField.hom ≫ (Y.residueFieldCongr hf.symm).hom ≫
        f.residueFieldMap (genericPoint X) ≫ X.functionFieldIsoResidueField.inv).hom.toAlgebra =
      AlgebraicGeometry.functionFieldAlgebra f hf := by
    apply Algebra.algebra_ext
    intro r
    exact congrArg (fun q => q.hom r) hmap.symm
  rw [hA]

omit [AlgebraicGeometry.IsIntegral X] in
/-- `ord_z(γ^n) = n · ord_z(γ)` for `γ ≠ 0`. -/
theorem ord_pow_of_ne_zero {γ : Y.functionField} (hγ : γ ≠ 0) (y : Y) (n : ℕ) :
    Y.ord (γ ^ n) y = n * Y.ord γ y := by
  induction n with
  | zero =>
    have h := ord_algebraMap_of_isUnit (W := Y) y (isUnit_one (M := Y.presheaf.stalk y))
    rw [map_one] at h
    simpa using h
  | succ n ih =>
    rw [pow_succ, AlgebraicGeometry.Scheme.ord_mul (pow_ne_zero n hγ) hγ, ih]
    push_cast; ring

/-- **Compatibility with divisors (the divisor level of Stacks 02ST)**:

`f_*(div_{f^*L}(f^*s)) = [R(X) : R(Y)] · div_L(s)`.

The hypotheses "`X`, `Y` locally of finite type over a field `k`, `f` a `k`-morphism, `X` and `Y` both of
dimension `d`" are necessary: for general integral locally Noetherian schemes and proper `f` the statement
is **false**, since the pushforward compares weights by `Order.height` (dimension of the closure) and on a
scheme that is not universally catenary a codimension-one point can map to a codimension-two point with the
same closure dimension. Counterexample (Nagata, *Local Rings*, Appendix, Example 2): `Y = Spec A` with `A` a
two-dimensional Noetherian local domain whose normalization `B` is finite and has a height-one maximal ideal
`n`; take `f : Spec B → Y` (finite, hence proper, of degree `1`), `L = O`, `s = g` a uniformizer of `n`. Then
the left side has coefficient `ord_n(g)·[κ(n):κ(m)] ≠ 0` at the closed point `m`, while `div_Y(g)` has
coefficient `0` at the codimension-two point `m`. The hypotheses of Stacks 02ST (the conventions of
`chow.tex`: universally catenary with a dimension function, `X`, `Y` locally of finite type) exclude this.

Proof: compare coefficients at each `y ∈ Y`. Take a generator `τ` of `L_y` and `γ ∈ R(Y)^*` with `γ • j τ = s`.
1. For every `x ∈ f⁻¹(y)`: `ord_{x,f^*L}(f^*s) = ord_x(image of γ in R(X))`
   (`rationalSectionOrd_rationalSectionPullback_of_generator`), so the coefficient of the left side at `y` is
   `(f_* div_X(γ))(y)` (the pushforward at `y` depends only on the coefficients over `f⁻¹(y)`).
2. The scheme version of Stacks 02RT (`properPushforward_principalCycle_of_locallyOfFiniteType`):
   `f_* div_X(γ) = div_Y(Nm(γ))`, `Nm_{R(X)/R(Y)}(γ) = γ^{[R(X):R(Y)]}` (`Algebra.norm_algebraMap`), and
   `ord_y(γ^n) = n·ord_y(γ)`.
3. The right side at `y` is `deg · ord_{y,L}(s) = deg · ord_y(γ)` (`rationalSectionOrd_eq_ord_of_generator`),
   with `deg = [R(X):R(Y)]` (`functionFieldDegree_eq_finrank_functionFieldAlgebra`).
Sources: Stacks 02ST (`lemma-equal-c1-as-cycles`) and 02RT (`lemma-proper-pushforward-alteration`). -/
theorem properPushforward_rationalSectionDivisor_pullback {k : Type u} [Field k]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper f]
    (d : ℕ) (hX : topologicalKrullDim X = d) (hY : topologicalKrullDim Y = d)
    (L : Y.Modules) [L.IsLineBundle]
    (s : L.presheaf.stalk (genericPoint Y)) (hs : s ≠ 0) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f
        (AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L)
          (rationalSectionPullback f hf L s))
      = (functionFieldDegree f : ℤ) •
          AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor L s := by
  classical
  letI := AlgebraicGeometry.functionFieldAlgebra f hf
  ext y
  change ∑ᶠ x ∈ f.base ⁻¹' {y},
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).rationalSectionOrd
        (rationalSectionPullback f hf L s) x *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f (Order.height (α := X))
        (Order.height (α := Y)) x : ℕ) : ℤ) = (functionFieldDegree f : ℤ) * L.rationalSectionOrd s y
  obtain ⟨τ, hτ⟩ := exists_stalk_generator L y
  obtain ⟨γ, hγ⟩ := exists_smul_toGenericFiber_eq L y τ hτ s
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    exact hs (hγ.symm.trans (zero_smul _ _))
  have hγ0' : algebraMap Y.functionField X.functionField γ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap Y.functionField X.functionField).injective).mpr hγ0
  have h02rt := congrArg (fun c => c y)
    (AlgebraicGeometry.properPushforward_principalCycle_of_locallyOfFiniteType (k := k) f hf d hX hY
      (Units.mk0 _ hγ0'))
  change ∑ᶠ x ∈ f.base ⁻¹' {y}, X.principalCycle (Units.mk0 _ hγ0') x *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f (Order.height (α := X))
        (Order.height (α := Y)) x : ℕ) : ℤ) = Y.principalCycle _ y at h02rt
  simp only [AlgebraicGeometry.Scheme.principalCycle_apply, Units.coe_map, Units.val_mk0,
    MonoidHom.coe_coe, Algebra.norm_algebraMap] at h02rt
  have hsum : ∀ x ∈ f.base ⁻¹' {y},
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L).rationalSectionOrd
        (rationalSectionPullback f hf L s) x *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f (Order.height (α := X))
        (Order.height (α := Y)) x : ℕ) : ℤ) =
      X.ord (algebraMap Y.functionField X.functionField γ) x *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f (Order.height (α := X))
        (Order.height (α := Y)) x : ℕ) : ℤ) := by
    intro x hx
    have hxy : f.base x = y := hx
    subst hxy
    rw [rationalSectionOrd_rationalSectionPullback_of_generator f hf L x τ hτ γ s hs hγ]
  rw [finsum_mem_congr rfl hsum, h02rt, ord_pow_of_ne_zero hγ0,
    rationalSectionOrd_eq_ord_of_generator L y τ hτ γ s hs hγ,
    functionFieldDegree_eq_finrank_functionFieldAlgebra f hf]

end AlgebraicGeometry.Scheme.Modules

end
