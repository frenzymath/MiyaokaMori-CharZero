import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueConstruction
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.Stacks00an

/-! # Comparison morphisms into and out of the glued sheaf of modules

Constructions attached to `GlueData.glued` (the kernel construction of Stacks 00AL): the
projections `glued ⟶ ι_{i*}F_i` to the pieces, the comparison morphisms `glued|_{U_i} ⟶ F_i`
obtained from them by the adjunction `restrict ⊣ pushforward`, and the morphism `M ⟶ glued`
induced by compatible morphisms `M|_{U_i} ⟶ F_i` through the universal property of the kernel.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The projection of the glued sheaf to the `i`-th piece (adjoint form):
`glued = ker(∏_j ι_{j*}F_j ⇉ …) ⟶ ∏_j ι_{j*}F_j ⟶ ι_{i*}F_i`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.GlueData.toPushforward {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} {U : ι → X.Opens} (D : AlgebraicGeometry.Scheme.Modules.GlueData U) (i : ι) :
    D.glued ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward (U i).ι).obj (D.F i) :=
  (CategoryTheory.Limits.kernel.ι _ : D.glued ⟶ CategoryTheory.Limits.piObj
      (fun j => (AlgebraicGeometry.Scheme.Modules.pushforward (U j).ι).obj (D.F j))) ≫
    CategoryTheory.Limits.Pi.π (fun j => (AlgebraicGeometry.Scheme.Modules.pushforward (U j).ι).obj (D.F j)) i

/-- The comparison morphism `glued|_{U_i} ⟶ F_i`: `toPushforward` transposed along
`restrict ⊣ pushforward` (`restrictAdjunction`). That it is an isomorphism (Stacks 00AL) is a
separate theorem; here only the morphism is constructed. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.GlueData.restrictTo {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} {U : ι → X.Opens} (D : AlgebraicGeometry.Scheme.Modules.GlueData U) (i : ι) :
    D.glued.restrict (U i).ι ⟶ D.F i :=
  ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _).symm (D.toPushforward i)

private theorem AlgebraicGeometry.Scheme.Modules.glueLiftAux_cat1 {C : Type*} [Category C]
    {A A1 A2 A3 B1 B : C} (a : A ⟶ A1) (p : A1 ⟶ B1) (c : B1 ⟶ B) (b1 : A ⟶ A2) (b2 : A2 ⟶ A3)
    (a' : A1 ⟶ A3) (p' : A3 ⟶ B) (nat : a' ≫ p' = p ≫ c) (e : a ≫ a' = b1 ≫ b2) :
    (a ≫ p) ≫ c = b1 ≫ b2 ≫ p' := by
  rw [Category.assoc, ← nat, ← Category.assoc, e, Category.assoc]

/-- The section map on `V` of the adjoint `M ⟶ W.ι_* F` of `f : M|_W ⟶ F`, followed by restriction
to `V' ≤ W`, equals restricting the sections of `M` to `V'.ι ''ᵁ V'.ι ⁻¹ᵁ V` and then applying the
section map of `f|_{V'}` (`f.app (homOfLE h ''ᵁ V'.ι ⁻¹ᵁ V)`). -/
private theorem AlgebraicGeometry.Scheme.Modules.homEquiv_app_comp_map {X : AlgebraicGeometry.Scheme.{u}}
    {V' W : X.Opens} (h : V' ≤ W) {M : X.Modules} {F : W.toScheme.Modules}
    (f : M.restrict W.ι ⟶ F) (V : X.Opens) :
    ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction W.ι).homEquiv M F f).app V ≫
        F.presheaf.map (homOfLE (AlgebraicGeometry.Scheme.Modules.homOfLE_image_preimage_le h V)).op =
      M.presheaf.map (homOfLE (V'.ι.image_preimage_le V)).op ≫
        M.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image h (V'.ι ⁻¹ᵁ V))).op ≫
        f.app (X.homOfLE h ''ᵁ (V'.ι ⁻¹ᵁ V)) := by
  have hle := AlgebraicGeometry.Scheme.Modules.homOfLE_image_preimage_le h V
  have nat := f.mapPresheaf.naturality (homOfLE hle).op
  simp only [AlgebraicGeometry.Scheme.Modules.mapPresheaf_app] at nat
  rw [AlgebraicGeometry.Scheme.Modules.restrict_map] at nat
  rw [Adjunction.homEquiv_unit, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app,
    AlgebraicGeometry.Scheme.Modules.pushforward_map_app]
  exact AlgebraicGeometry.Scheme.Modules.glueLiftAux_cat1 _ _ _ _ _ _ _ nat
    (AlgebraicGeometry.Scheme.Modules.glueAux_map22 M.presheaf _ _ _ _)

private theorem AlgebraicGeometry.Scheme.Modules.glueLiftAux_cat2 {C : Type*} [Category C]
    {M0 M1 Mi Mj Pi Pj Fi Fj : C} (pj : M0 ⟶ Pj) (rj : Pj ⟶ Fj) (pi : M0 ⟶ Pi) (ri : Pi ⟶ Fi)
    (φ : Fi ⟶ Fj) (m : M0 ⟶ M1) (mi : M1 ⟶ Mi) (fi : Mi ⟶ Fi) (mj : M1 ⟶ Mj) (fj : Mj ⟶ Fj)
    (e1 : pj ≫ rj = m ≫ mj ≫ fj) (e2 : pi ≫ ri = m ≫ mi ≫ fi) (hA : mi ≫ fi ≫ φ = mj ≫ fj) :
    pj ≫ rj = pi ≫ ri ≫ φ := by
  rw [e1, ← Category.assoc pi, e2, ← hA]
  simp only [Category.assoc]

/-- The section map on `A` of the inverse of `restrictιIso` is the restriction map of `M`
(the two opens are equal). -/
private theorem AlgebraicGeometry.Scheme.Modules.restrictιIso_inv_app' {X : AlgebraicGeometry.Scheme.{u}}
    {V' W : X.Opens} (h : V' ≤ W) (M : X.Modules) (A : V'.toScheme.Opens) :
    (AlgebraicGeometry.Scheme.Modules.restrictιIso h M).inv.app A =
      M.presheaf.map (eqToHom (AlgebraicGeometry.Scheme.Modules.image_homOfLE_image h A)).op := by
  simp only [AlgebraicGeometry.Scheme.Modules.restrictιIso, Iso.trans_inv, Iso.symm_inv, Iso.app_hom,
    Iso.app_inv, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_hom_app_app,
    AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr_inv_app_app]
  exact AlgebraicGeometry.Scheme.Modules.glueAux_map2 M.presheaf _ _ _

/-- The section map on `V` of `pushforwardRestrictMap` is the restriction map of `F`
(its body is the same as that of `pushforwardRestrictHom`). -/
private theorem AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap_app {X : AlgebraicGeometry.Scheme.{u}}
    {V' W : X.Opens} (h : V' ≤ W) (F : W.toScheme.Modules) (V : X.Opens) :
    (AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap h F).app V =
      F.presheaf.map (homOfLE (AlgebraicGeometry.Scheme.Modules.homOfLE_image_preimage_le h V)).op :=
  AlgebraicGeometry.Scheme.Modules.pushforwardRestrictHom_app h F V

/-- The morphisms `f_i : M|_{U_i} ⟶ F_i` on the pieces are compatible with the gluing data:
`φ_ij ∘ f_i = f_j` on `U_ij` (aligned via `restrictιIso`; same shape as `IsGlueCompatible`, but
the `f_i` need not be isomorphisms). -/
def AlgebraicGeometry.Scheme.Modules.GlueData.IsLiftCompatible {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} {U : ι → X.Opens} (D : AlgebraicGeometry.Scheme.Modules.GlueData U) {M : X.Modules}
    (f : ∀ i, M.restrict (U i).ι ⟶ D.F i) (i j : ι) : Prop :=
  (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_left : U i ⊓ U j ≤ U i) M).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_left : U i ⊓ U j ≤ U i))).map (f i) ≫
      (D.φ i j).hom
    = (AlgebraicGeometry.Scheme.Modules.restrictιIso (inf_le_right : U i ⊓ U j ≤ U j) M).inv ≫
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE (inf_le_right : U i ⊓ U j ≤ U j))).map (f j)

/-- The `(i, j)` component of the condition of `kernel.lift`: when `f` is compatible with the gluing
data, the two branches of the adjoint morphisms `M ⟶ ι_{i*}F_i` agree. -/
theorem AlgebraicGeometry.Scheme.Modules.GlueData.lift_condition {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} {U : ι → X.Opens} (D : AlgebraicGeometry.Scheme.Modules.GlueData U) {M : X.Modules}
    (f : ∀ i, M.restrict (U i).ι ⟶ D.F i) (i j : ι) (hf : D.IsLiftCompatible f i j) :
    (AlgebraicGeometry.Scheme.Modules.restrictAdjunction (U j).ι).homEquiv _ _ (f j) ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap (inf_le_right : U i ⊓ U j ≤ U j) (D.F j) =
      (AlgebraicGeometry.Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (f i) ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap (inf_le_left : U i ⊓ U j ≤ U i) (D.F i) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward (U i ⊓ U j).ι).map (D.φ i j).hom := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro V
  have e1 := AlgebraicGeometry.Scheme.Modules.homEquiv_app_comp_map (inf_le_right : U i ⊓ U j ≤ U j) (f j) V
  have e2 := AlgebraicGeometry.Scheme.Modules.homEquiv_app_comp_map (inf_le_left : U i ⊓ U j ≤ U i) (f i) V
  have hA := congrArg (fun g => AlgebraicGeometry.Scheme.Modules.Hom.app g ((U i ⊓ U j).ι ⁻¹ᵁ V)) hf
  simp only [AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.restrictιIso_inv_app'] at hA
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap_app,
    AlgebraicGeometry.Scheme.Modules.pushforwardRestrictMap_app,
    AlgebraicGeometry.Scheme.Modules.pushforward_map_app]
  exact AlgebraicGeometry.Scheme.Modules.glueLiftAux_cat2 _ _ _ _ _ _ _ _ _ _ e1 e2 hA

/-- The morphism into the glued sheaf (universal property of the kernel): each
`f_i : M|_{U_i} ⟶ F_i` gives by adjunction `M ⟶ ι_{i*}F_i`, these assemble to
`M ⟶ ∏_i ι_{i*}F_i`, and `kernel.lift` applies. The hypothesis `hf` (the `f_i`, `f_j` are
compatible on `U_ij` via `φ_ij`, `IsLiftCompatible`) is necessary: it supplies, through
`lift_condition`, the equality of the two branches required by `kernel.lift`. -/

noncomputable def AlgebraicGeometry.Scheme.Modules.GlueData.lift {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} {U : ι → X.Opens} (D : AlgebraicGeometry.Scheme.Modules.GlueData U) {M : X.Modules}
    (f : ∀ i, M.restrict (U i).ι ⟶ D.F i) (hf : ∀ i j, D.IsLiftCompatible f i j) : M ⟶ D.glued :=
  (CategoryTheory.Limits.kernel.lift _
    (CategoryTheory.Limits.Pi.lift fun i =>
      (AlgebraicGeometry.Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (f i)) (by
        rw [Preadditive.comp_sub, sub_eq_zero]
        refine CategoryTheory.Limits.Pi.hom_ext _ _ fun p => ?_
        simp only [Category.assoc, CategoryTheory.Limits.Pi.lift_π,
          CategoryTheory.Limits.Pi.lift_π_assoc]
        exact D.lift_condition f p.1 p.2 (hf p.1 p.2)) : M ⟶ D.glued)

/-- `lift` composed with the projection to the `i`-th piece is the adjoint of `f_i`. -/
theorem AlgebraicGeometry.Scheme.Modules.GlueData.lift_toPushforward {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} {U : ι → X.Opens} (D : AlgebraicGeometry.Scheme.Modules.GlueData U) {M : X.Modules}
    (f : ∀ i, M.restrict (U i).ι ⟶ D.F i) (hf : ∀ i j, D.IsLiftCompatible f i j) (i : ι) :
    D.lift f hf ≫ D.toPushforward i =
      (AlgebraicGeometry.Scheme.Modules.restrictAdjunction (U i).ι).homEquiv _ _ (f i) := by
  exact (CategoryTheory.Limits.kernel.lift_ι_assoc _ _ _ _).trans (CategoryTheory.Limits.Pi.lift_π _ _)

end
