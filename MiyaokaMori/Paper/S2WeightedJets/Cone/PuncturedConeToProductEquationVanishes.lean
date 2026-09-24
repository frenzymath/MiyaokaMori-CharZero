import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensor

/-! # Pullback of a section along the zero scheme, and the homogeneous evaluation under isomorphisms

Two general lemmas used for `puncturedConeToProduct.eval_coord_eq_zero`: the defining equations `F_j`
vanish on the coordinates of the punctured cone `Z^× ⊆ Z ⊆ Tot(A^{⊕(N+1)})`
(eq. (2.1) of the paper).

1. `sectionPullbackAlong_subschemeι_eq_zero` — Stacks 02OR, direction "a morphism factoring through
   the zero scheme `Z(s)` pulls `s` back to `0`", for the closed immersion `ι = I.subschemeι` of an
   ideal sheaf `I ⊇ I(s)` (`idealSheafOfSection`). Proof, germ by germ
   (`TopCat.Presheaf.section_ext`): at `y = ι x` take an affine open `W` and a frame `e` of `L|_W`
   (`exists_affine_frame_le`), write `s|_W = c • e` with `c = coord_e(s|_W)`; `c ∈ I(s)(W) ⊆ I(W) =
   ker (ι.app W)` (`IdealSheafData.le_def`, `ker_subschemeι_app`), so `ι.app W c = 0`; the germ of
   `ι^*s` is the stalk unit applied to the germ of `s` (`AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ`),
   the unit is semilinear over `ι.stalkMap x` (`LinearMap.map_smulₛₗ`), and `ι.stalkMap x (germ c) =
   germ (ι.app W c) = 0` (`Scheme.Hom.germ_stalkMap_apply`).
2. `evalHomogeneousAtSections_iso` — naturality of the homogeneous evaluation
   under an isomorphism of line bundles `θ : M ≅ M'`:
   `θ^{⊗e}(F(f_0, …, f_N)) = F(θ f_0, …, θ f_N)`, where `θ^{⊗e} = tensorPowIsoOfIso θ e` is built
   recursively from `tensorIsoTensorObj` and the monoidal `tensorIso`. Proof: induction on `e` for the
   monomials (`tensorIsoTensorObj.hom` turns `sectionTensor` into `tensorSections` by `rfl`,
   `tensorHom_tensorSections` acts factorwise, `tensorIsoTensorObj.inv` goes back by injectivity), then
   `map_sum`/`map_smul`. Corollary `evalHomogeneousAtSections_iso_eq_zero`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- Stacks 02OR, the direction "a morphism factoring through the zero scheme of `s` pulls `s` back
to zero", for the closed immersion `I.subschemeι` of an ideal sheaf `I ⊇ I(s)`. -/
theorem AlgebraicGeometry.Scheme.sectionPullbackAlong_subschemeι_eq_zero {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (L : X.Modules) [L.IsLineBundle] (s : (L.val.obj (Opposite.op ⊤) : Type u))
    (h : AlgebraicGeometry.Scheme.idealSheafOfSection L s ≤ I) :
    sectionPullbackAlong I.subschemeι s = 0 := by
  let ι := I.subschemeι
  let M := (AlgebraicGeometry.Scheme.Modules.pullback ι).obj L
  let F : TopCat.Sheaf AddCommGrpCat.{u} I.subscheme := ⟨M.presheaf, M.isSheaf⟩
  apply TopCat.Presheaf.section_ext F ⊤
  intro x _
  show M.presheaf.germ ⊤ x trivial (sectionPullbackAlong ι s) = M.presheaf.germ ⊤ x trivial 0
  rw [map_zero]
  obtain ⟨W, hW, -, hxW, e, hf⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le L (U := ⊤) (p := ι.base x) trivial
  set sW : Γ(L, W) := L.res (le_top : W ≤ ⊤) (show Γ(L, ⊤) from s) with hsW
  set c := hf.coord le_rfl sW with hcdef
  have hc : c • L.res le_rfl e = sW := hf.coord_smul_frame le_rfl sW
  have hcI : c ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).ideal ⟨W, hW⟩ := by
    show c ∈ Ideal.span (Set.range fun φ : Γ(L, W) →ₗ[Γ(X, W)] Γ(X, W) =>
      φ (L.presheaf.map (CategoryTheory.homOfLE le_top).op (show Γ(L, ⊤) from s)))
    exact Ideal.subset_span ⟨(hf.coordEquiv le_rfl).toLinearMap, rfl⟩
  have hcK : ι.app W c = 0 := by
    have hmem : c ∈ I.ideal ⟨W, hW⟩ := AlgebraicGeometry.Scheme.IdealSheafData.le_def.mp h ⟨W, hW⟩ hcI
    rw [← I.ker_subschemeι_app ⟨W, hW⟩] at hmem
    exact RingHom.mem_ker.mp hmem
  have hs : L.presheaf.germ ⊤ (ι.base x) trivial (show Γ(L, ⊤) from s) =
      X.presheaf.germ W (ι.base x) hxW c • L.presheaf.germ W (ι.base x) hxW e := by
    have h1 : L.presheaf.germ ⊤ (ι.base x) trivial (show Γ(L, ⊤) from s) =
        L.presheaf.germ W (ι.base x) hxW sW :=
      (TopCat.Presheaf.germ_res_apply L.presheaf (CategoryTheory.homOfLE (le_top : W ≤ ⊤))
        (ι.base x) hxW _).symm
    rw [h1, ← hc, AlgebraicGeometry.Scheme.Modules.germ_smul', AlgebraicGeometry.Scheme.Modules.res_self]
  have hgerm : M.presheaf.germ ⊤ x trivial (sectionPullbackAlong ι s) =
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit ι L x
        (L.presheaf.germ ⊤ (ι.base x) trivial (show Γ(L, ⊤) from s)) :=
    (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ ι L x ⊤ trivial s).symm
  have hz : (ι.stalkMap x).hom (X.presheaf.germ W (ι.base x) hxW c) = 0 := by
    have := AlgebraicGeometry.Scheme.Hom.germ_stalkMap_apply ι W x hxW c
    rw [hcK, map_zero] at this
    exact this
  rw [hgerm, hs, LinearMap.map_smulₛₗ, hz, zero_smul]


/-! ## Naturality of `evalHomogeneousAtSections` under an isomorphism of line bundles -/

/-- `θ^{⊗e} : M^{⊗e} ≅ M'^{⊗e}` for an isomorphism `θ : M ≅ M'` (recursive on `e`, via
`tensorIsoTensorObj` and the monoidal `tensorIso`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso {X : AlgebraicGeometry.Scheme.{u}}
    {M M' : X.Modules} (θ : M ≅ M') : (e : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.tensorPow M e ≅ AlgebraicGeometry.Scheme.Modules.tensorPow M' e)
  | 0 => CategoryTheory.Iso.refl _
  | e + 1 =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso
        (AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e) θ ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm

private theorem tensorIsoTensorObj_sectionTensor' {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).hom.app ⊤ (sectionTensor s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t := by
  rfl

private theorem tensorIsoTensorObj_inv_tensorSections' {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).inv.val.app (Opposite.op ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t) =
      sectionTensor s t := by
  let e := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N
  have hinj : Function.Injective (fun z => (e.hom.val.app (Opposite.op ⊤)).hom z) := by
    intro a b hab
    have h' := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom a) e.hom_inv_id
    have h'' := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom b) e.hom_inv_id
    change (e.inv.val.app (Opposite.op ⊤)).hom ((e.hom.val.app (Opposite.op ⊤)).hom a) = a at h'
    change (e.inv.val.app (Opposite.op ⊤)).hom ((e.hom.val.app (Opposite.op ⊤)).hom b) = b at h''
    calc
      a = (e.inv.val.app (Opposite.op ⊤)).hom ((e.hom.val.app (Opposite.op ⊤)).hom a) := h'.symm
      _ = (e.inv.val.app (Opposite.op ⊤)).hom ((e.hom.val.app (Opposite.op ⊤)).hom b) := congrArg _ hab
      _ = b := h''
  apply hinj
  have h := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t)) e.inv_hom_id
  change (e.hom.val.app (Opposite.op ⊤)).hom ((e.inv.val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t)) =
    AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t at h
  calc
    _ = AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t := h
    _ = (e.hom.val.app (Opposite.op ⊤)).hom (sectionTensor s t) :=
      (tensorIsoTensorObj_sectionTensor' s t).symm

/-- `θ^{⊗e}` sends the monomial `f_{q 0} ⊗ ⋯ ⊗ f_{q (e-1)}` to the monomial of `θ ∘ f`. -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso_monomial {X : AlgebraicGeometry.Scheme.{u}}
    {M M' : X.Modules} (θ : M ≅ M') {N : ℕ} (f : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) :
    ∀ e (q : Fin e → Fin (N + 1)),
      ((AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e).hom.val.app (Opposite.op ⊤)).hom
          (evalHomogeneousAtSections.monomial M f e q) =
        evalHomogeneousAtSections.monomial M' (fun i => (θ.hom.val.app (Opposite.op ⊤)).hom (f i)) e q := by
  intro e
  induction e with
  | zero =>
      intro q
      rfl
  | succ e ih =>
      intro q
      change ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow M' e) M').inv.val.app (Opposite.op ⊤)).hom
        (((CategoryTheory.MonoidalCategory.tensorIso
          (AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e) θ).hom.val.app (Opposite.op ⊤)).hom
          (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            (AlgebraicGeometry.Scheme.Modules.tensorPow M e) M).hom.val.app (Opposite.op ⊤)).hom
            (sectionTensor (evalHomogeneousAtSections.monomial M f e (fun i => q i.castSucc))
              (f (q (Fin.last e)))))) = _
      have h1 : ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            (AlgebraicGeometry.Scheme.Modules.tensorPow M e) M).hom.val.app (Opposite.op ⊤)).hom
            (sectionTensor (evalHomogeneousAtSections.monomial M f e (fun i => q i.castSucc))
              (f (q (Fin.last e)))) =
          AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤
            (evalHomogeneousAtSections.monomial M f e (fun i => q i.castSucc)) (f (q (Fin.last e))) :=
        tensorIsoTensorObj_sectionTensor' _ _
      rw [h1]
      have h2 : (CategoryTheory.MonoidalCategory.tensorIso
            (AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e) θ).hom =
          CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
            (AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e).hom θ.hom := rfl
      rw [h2]
      change ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow M' e) M').inv.val.app (Opposite.op ⊤)).hom
        ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
            (AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e).hom θ.hom).val.app (Opposite.op ⊤)
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤
            (evalHomogeneousAtSections.monomial M f e (fun i => q i.castSucc)) (f (q (Fin.last e))))) = _
      rw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
      have hi := ih (fun i => q i.castSucc)
      change (ConcreteCategory.hom
          ((AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e).hom.val.app (Opposite.op ⊤)))
          (evalHomogeneousAtSections.monomial M f e (fun i => q i.castSucc)) = _ at hi
      rw [hi, tensorIsoTensorObj_inv_tensorSections']
      rfl

/-- **Naturality of `evalHomogeneousAtSections` under an isomorphism of line bundles**:
`θ^{⊗e}(F(f_0, …, f_N)) = F(θ f_0, …, θ f_N)`. -/
theorem evalHomogeneousAtSections_iso {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M M' : X.Modules} [M.IsLineBundle]
    [M'.IsLineBundle] (θ : M ≅ M') {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    (f : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e).hom.val.app (Opposite.op ⊤)).hom
        (evalHomogeneousAtSections M F hF f) =
      evalHomogeneousAtSections M' F hF (fun i => (θ.hom.val.app (Opposite.op ⊤)).hom (f i)) := by
  simp only [evalHomogeneousAtSections]
  change (((AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e).hom.val.app
    (Opposite.op ⊤)).hom) (∑ i ∈ F.support.attach, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  change (((AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso θ e).hom.val.app
      (Opposite.op ⊤)).hom)
      ((show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
          (MvPolynomial.coeff (↑x) F)) •
        evalHomogeneousAtSections.monomial M f e
          (evalHomogeneousAtSections.indices (↑x) (hF (MvPolynomial.mem_support_iff.mp x.property)))) = _
  rw [map_smul]
  congr 1
  exact AlgebraicGeometry.Scheme.Modules.tensorPowIsoOfIso_monomial θ f e _

/-- If `F(f) = 0` then `F(θ ∘ f) = 0` for an isomorphism `θ` of line bundles. -/
theorem evalHomogeneousAtSections_iso_eq_zero {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {M M' : X.Modules} [M.IsLineBundle]
    [M'.IsLineBundle] (θ : M ≅ M') {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    (f : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (h : evalHomogeneousAtSections M F hF f = 0) :
    evalHomogeneousAtSections M' F hF (fun i => (θ.hom.val.app (Opposite.op ⊤)).hom (f i)) = 0 := by
  rw [← evalHomogeneousAtSections_iso θ F hF f, h, map_zero]

end
