import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.Stacks01ne
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualPowerContraction
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheafMul

/-! # Naturality of the projectivization and the minor criterion

(a) The projectivization morphism induced by a nowhere-all-zero tuple of sections `P` commutes with pullback;
(b) if two tuples `P` (line bundle `M`) and `Q` (line bundle `M'`) induce the same morphism to `P^N`, then all
`2×2` minors `P_i⊗Q_j − P_j⊗Q_i`, as sections of `M⊗M'`, vanish; (c) multiplying the tuple by an everywhere
invertible function does not change the projectivization.

Used implicitly in the proof of Theorem 4.2 of the paper: projectivization commutes with restriction,
and a constant projective map forces the tuple to be proportional to the seed tuple.

All three are assembled from two lemmas: the uniqueness of Stacks 01NE (`projectiveSpace_hom_ext_of_sections`) and
`projectivizationMorphism_pullback_twist` (`θ : φ_P^*O(1) ≅ M` sends `x_ℓ` to `P_ℓ`). The remaining section-level
algebra (pullback of composites, scaling by units, `s⊗t = t⊗s` on a line bundle) is proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Scalar multiplication by a global function `a ∈ Γ(X, O)`: the endomorphism of the module sheaf `M` given on each open `U` by `x ↦ a|_U • x`. -/
noncomputable def smulHomOfGlobal {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (a : Γ(X, ⊤)) :
    M ⟶ M :=
  SheafOfModules.Hom.mk (PresheafOfModules.homMk
    { app := fun U => M.smul (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a)
      naturality := fun {U V} i => by
        have hr : X.presheaf.map i.unop.op (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a) =
            X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op a := by
          rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
          rfl
        have h := M.map_comp_smul i.unop (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a)
        rw [hr] at h
        exact h.symm }
    (fun U r m => by
      change (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a) •
          ((show Γ(X, U.unop) from r) • (show Γ(M, U.unop) from m)) =
        (show Γ(X, U.unop) from r) •
          ((X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op a) • (show Γ(M, U.unop) from m))
      rw [smul_smul, smul_smul, mul_comm]))

theorem smulHomOfGlobal_app {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (a : Γ(X, ⊤))
    (U : X.Opens) (x : Γ(M, U)) :
    (smulHomOfGlobal M a).app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op a • x :=
  rfl

theorem smulHomOfGlobal_app_top {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (a : Γ(X, ⊤))
    (x : Γ(M, ⊤)) :
    (smulHomOfGlobal M a).app ⊤ x = a • x := by
  rw [smulHomOfGlobal_app]
  have h : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  rw [h, X.presheaf.map_id]
  rfl

theorem smulHomOfGlobal_mul {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (a b : Γ(X, ⊤)) :
    smulHomOfGlobal M a ≫ smulHomOfGlobal M b = smulHomOfGlobal M (b * a) := by
  ext U x
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    smulHomOfGlobal_app, smulHomOfGlobal_app, smulHomOfGlobal_app, smul_smul, map_mul]

theorem smulHomOfGlobal_one {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    smulHomOfGlobal M (1 : Γ(X, ⊤)) = 𝟙 M := by
  ext U x
  rw [smulHomOfGlobal_app, map_one, one_smul]
  rfl

/-- Scalar multiplication by a unit `u ∈ Γ(X, O)^×`: an automorphism of the module sheaf `M`. -/
noncomputable def unitSmulIso {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (u : Γ(X, ⊤)ˣ) :
    M ≅ M where
  hom := smulHomOfGlobal M (u : Γ(X, ⊤))
  inv := smulHomOfGlobal M ((u⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤))
  hom_inv_id := by rw [smulHomOfGlobal_mul, Units.inv_mul, smulHomOfGlobal_one]
  inv_hom_id := by rw [smulHomOfGlobal_mul, Units.mul_inv, smulHomOfGlobal_one]

theorem unitSmulIso_hom_app_top {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (u : Γ(X, ⊤)ˣ)
    (x : Γ(M, ⊤)) :
    (unitSmulIso M u).hom.app ⊤ x = (u : Γ(X, ⊤)) • x :=
  smulHomOfGlobal_app_top M _ x

/-- The inverse of an isomorphism undoes it on sections: `e⁻¹(e x) = x`. -/
theorem iso_inv_app_hom_app {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules} (e : A ≅ B)
    (U : X.Opens) (x : Γ(A, U)) :
    e.inv.app U (e.hom.app U x) = x := by
  have h := congrArg (fun f : A ⟶ A => f.app U x) e.hom_inv_id
  exact h

/-- **Symmetry of the tensor product of sections of a line bundle**: for a line bundle `M` and `s, t ∈ Γ(M, ⊤)`,
`s ⊗ t = t ⊗ s ∈ Γ(M ⊗ M, ⊤)`. Locally, on an open `W` with frame `e`, `s| = a•e` and `t| = b•e`, so
`(s⊗t)| = (ab)•(e⊗e) = (t⊗s)|`; separatedness of the sheaf gives the global equality. -/
theorem sectionTensor_comm_of_isLineBundle {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    [M.IsLineBundle] (s t : Γ(M, ⊤)) :
    sectionTensor s t = sectionTensor t s := by
  choose W hW e he using AlgebraicGeometry.Scheme.Modules.exists_frame M
  refine TopCat.Sheaf.eq_of_locally_eq'
    ⟨(AlgebraicGeometry.Scheme.Modules.tensor M M).presheaf,
      (AlgebraicGeometry.Scheme.Modules.tensor M M).isSheaf⟩ W ⊤
    (fun p => homOfLE le_top) ?_ _ _ ?_
  · intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hW x⟩
  · intro p
    change (AlgebraicGeometry.Scheme.Modules.moduleTensor M M).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (U := ⊤) s t) =
      (AlgebraicGeometry.Scheme.Modules.moduleTensor M M).presheaf.map (homOfLE (le_top : W p ≤ ⊤)).op
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (U := ⊤) t s)
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (M := M) (N := M) (homOfLE (le_top : W p ≤ ⊤)) s t,
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (M := M) (N := M) (homOfLE (le_top : W p ≤ ⊤)) t s]
    have hs := (he p).coord_smul_frame le_rfl (M.res (le_top : W p ≤ ⊤) s)
    have ht := (he p).coord_smul_frame le_rfl (M.res (le_top : W p ≤ ⊤) t)
    rw [AlgebraicGeometry.Scheme.Modules.res_self] at hs ht
    change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M.res (le_top : W p ≤ ⊤) s) (M.res (le_top : W p ≤ ⊤) t) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M.res (le_top : W p ≤ ⊤) t) (M.res (le_top : W p ≤ ⊤) s)
    rw [← hs, ← ht, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul, mul_comm]

/-- Naturality of the tensor of sections in the second factor: `s ⊗ e(t) = (id ⊗ e)(s ⊗ t)`. -/
theorem sectionTensor_hom_app_right {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules} (e : M ⟶ M')
    (s t : Γ(M, ⊤)) :
    sectionTensor s (e.app ⊤ t) =
      (AlgebraicGeometry.Scheme.Modules.tensorMap (𝟙 M) e).app ⊤ (sectionTensor s t) := by
  have h := AlgebraicGeometry.Scheme.Modules.ModuleDualPowerContraction.tensorMap_section (𝟙 M) e (U := ⊤) s t
  exact h.symm

/-- Section-level core of (b): if a line bundle isomorphism `e : M ≅ M'` sends `P_ℓ` to `Q_ℓ`, then `P_i ⊗ Q_j = P_j ⊗ Q_i`. -/
theorem minors_eq_of_iso_map {X : AlgebraicGeometry.Scheme.{u}} {ι : Type v} (M M' : X.Modules)
    [M.IsLineBundle] (e : M ≅ M')
    (P : ι → Γ(M, ⊤)) (Q : ι → Γ(M', ⊤))
    (he : ∀ ℓ, e.hom.app ⊤ (P ℓ) = Q ℓ) (i j : ι) :
    sectionTensor (P i) (Q j) = sectionTensor (P j) (Q i) := by
  rw [← he i, ← he j, sectionTensor_hom_app_right, sectionTensor_hom_app_right,
    sectionTensor_comm_of_isLineBundle M (P i) (P j)]

/-- `e_P⁻¹ ≫ e_Q` sends `P` to `Q` (both are images of the same `x`). -/
theorem symm_trans_hom_app_top_of_eq {X : AlgebraicGeometry.Scheme.{u}} {A M M' : X.Modules}
    (θP : A ≅ M) (θQ : A ≅ M') (x : Γ(A, ⊤)) {p : Γ(M, ⊤)} {q : Γ(M', ⊤)}
    (hp : θP.hom.app ⊤ x = p) (hq : θQ.hom.app ⊤ x = q) :
    (θP.symm ≪≫ θQ).hom.app ⊤ p = q := by
  subst hp hq
  rw [Iso.trans_hom, Iso.symm_hom, AlgebraicGeometry.Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, iso_inv_app_hom_app]

/-- `θ ≪≫ (multiplication by u)` on global sections: `x ↦ u • θ(x)`. -/
theorem trans_unitSmulIso_hom_app_top {X : AlgebraicGeometry.Scheme.{u}} {A M : X.Modules}
    (θ : A ≅ M) (u : Γ(X, ⊤)ˣ) (x : Γ(A, ⊤)) :
    (θ ≪≫ unitSmulIso M u).hom.app ⊤ x = (u : Γ(X, ⊤)) • θ.hom.app ⊤ x := by
  rw [Iso.trans_hom, AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    unitSmulIso_hom_app_top]

/-- Section-level core of (a): `θ′ := (pullbackComp)⁻¹ ≪≫ g^*θ` sends `(g ≫ φ)^*s` to `g^*(θ(φ^*s))`. -/
theorem pullbackComp_symm_trans_mapIso_app_top {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (φ : Y ⟶ Z) {L : Z.Modules} {M : Y.Modules}
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback φ).obj L ≅ M) (s : (L.val.obj (Opposite.op ⊤) : Type u)) :
    ((((AlgebraicGeometry.Scheme.Modules.pullbackComp g φ).app L).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback g).mapIso θ).hom.app ⊤).hom
        (sectionPullbackAlong (g ≫ φ) s) =
      sectionPullbackAlong g ((θ.hom.app ⊤).hom (sectionPullbackAlong φ s)) := by
  rw [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  have h1 := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp_inv g φ (M := L) s
  have h2 := sectionPullbackAlong_naturality g θ.hom (sectionPullbackAlong φ s)
  change ((AlgebraicGeometry.Scheme.Modules.pullback g).map θ.hom).app ⊤
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp g φ).app L).inv.app ⊤)
        (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback (g ≫ φ) s)) = _
  rw [h1]
  exact h2.symm

end AlgebraicGeometry.Scheme.Modules

/-- **(a) Projectivization commutes with pullback**: `g ≫ φ_P = φ_{g^*P}`. By the uniqueness of 01NE:
`θ′ := (pullbackComp)⁻¹ ≪≫ g^*θ` sends `(g ≫ φ_P)^*x_ℓ` to `g^*(θ(φ_P^*x_ℓ)) = g^*P_ℓ`
(`pullbackComp_symm_trans_mapIso_app_top`). -/
theorem projectivizationMorphism_pullback {k : Type u} [Field k]
    {V V' : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [V'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : V' ⟶ V) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (hP) (hP') :
    g ≫ projectivizationMorphism (k := k) M P hP
      = projectivizationMorphism (k := k) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
          (fun ℓ => sectionPullbackAlong g (P ℓ)) hP' := by
  obtain ⟨θ, hθ⟩ := projectivizationMorphism_pullback_twist (k := k) M P hP
  refine projectiveSpace_hom_ext_of_sections (g ≫ projectivizationMorphism (k := k) M P hP)
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) _ hP'
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp g (projectivizationMorphism (k := k) M P hP)).app
        (projectiveSpaceTwist k N 1)).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback g).mapIso θ) ?_
  intro i
  have h1 := AlgebraicGeometry.Scheme.Modules.pullbackComp_symm_trans_mapIso_app_top g
    (projectivizationMorphism (k := k) M P hP) θ (projectiveSpaceCoordinate k N i)
  have h2 := congrArg (sectionPullbackAlong g) (hθ i)
  exact h1.trans h2

/-- **(b) Same morphism ⇒ minors vanish**: `φ_P = φ_Q =: φ`, and `θ_P`, `θ_Q` send `φ^*x_ℓ` to `P_ℓ`, `Q_ℓ`
respectively, so `e := θ_P⁻¹ ≫ θ_Q : M ≅ M′` satisfies `e(P_ℓ) = Q_ℓ`; `P_i ⊗ Q_j = (id ⊗ e)(P_i ⊗ P_j)`, and
`P_i ⊗ P_j` is symmetric on a line bundle (`sectionTensor_comm_of_isLineBundle`). -/
theorem minors_eq_zero_of_projectivizationMorphism_eq {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M M' : V.Modules) [M.IsLineBundle] [M'.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (Q : Fin (N + 1) → (M'.val.obj (Opposite.op ⊤) : Type u)) (hP) (hQ)
    (h : projectivizationMorphism (k := k) M P hP = projectivizationMorphism (k := k) M' Q hQ) (i j : Fin (N + 1)) :
    sectionTensor (P i) (Q j) = sectionTensor (P j) (Q i) := by
  obtain ⟨θP, hθP⟩ := projectivizationMorphism_pullback_twist (k := k) M P hP
  have hQ' := projectivizationMorphism_pullback_twist (k := k) M' Q hQ
  rw [← h] at hQ'
  obtain ⟨θQ, hθQ⟩ := hQ'
  exact AlgebraicGeometry.Scheme.Modules.minors_eq_of_iso_map M M' (θP.symm ≪≫ θQ) P Q
    (fun ℓ => AlgebraicGeometry.Scheme.Modules.symm_trans_hom_app_top_of_eq θP θQ _ (hθP ℓ) (hθQ ℓ)) i j

/-- **(c) Invariance under multiplication by a unit**: `θ ≪≫ (multiplication by u) : φ_P^*O(1) ≅ M` sends `x_ℓ` to `u • P_ℓ`, so `φ_P = φ_{u•P}` by the uniqueness of 01NE. -/
theorem projectivizationMorphism_smul_unit {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (hP)
    (u : Γ(V, ⊤)ˣ) (hP') :
    projectivizationMorphism (k := k) M
        (fun ℓ => (show V.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(V, ⊤))) • P ℓ) hP'
      = projectivizationMorphism (k := k) M P hP := by
  obtain ⟨θ, hθ⟩ := projectivizationMorphism_pullback_twist (k := k) M P hP
  symm
  refine projectiveSpace_hom_ext_of_sections (projectivizationMorphism (k := k) M P hP) M _ hP'
    (θ ≪≫ AlgebraicGeometry.Scheme.Modules.unitSmulIso M u) ?_
  intro i
  have h1 := AlgebraicGeometry.Scheme.Modules.trans_unitSmulIso_hom_app_top θ u
    (sectionPullbackAlong (projectivizationMorphism (k := k) M P hP) (projectiveSpaceCoordinate k N i))
  have h2 := congrArg (fun y : Γ(M, ⊤) => (u : Γ(V, ⊤)) • y) (hθ i)
  exact h1.trans h2

end
