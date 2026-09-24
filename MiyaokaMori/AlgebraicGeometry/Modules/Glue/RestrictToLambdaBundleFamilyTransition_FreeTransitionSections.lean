import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.FreeTransitionCompatible

/-! # Compatibility with `freeTransition` in terms of frame sections

A sectionwise characterization of block isomorphisms compatible with `freeTransition`
(independent of `C` and `A¹`): a block isomorphism `e_α : M|_{U_α} ≅ O^r` gives frame sections
`σ^α_i := e_α⁻¹(e_i) ∈ Γ(M, U_α)`, and
`IsTransitionCompatible U O^r (freeTransition (U α) (U α') g) M e α α'` holds iff for every `i`
and every open `P` of `U_α ⊓ U_α'`,
  `e_α'(σ^α_i|_{k''P}) = Σ_j (swap g)_{ji}|_P • e_j`        (`k : U_α ⊓ U_α' → U_α'`).

Reference: Hartshorne II Ex. 5.18(a) (locally free sheaves ↔ transition matrices: the matrix of a
transition isomorphism in a frame).

Proof: both sides of `IsTransitionCompatible` are morphisms out of `M|_{U_αα'}`; composing with
the inverse of the block isomorphism turns the condition into
`freeTransition = e_α⁻¹ ≫ (restrictιIso) ≫ (restrictιIso)⁻¹ ≫ e_α'` (morphisms out of
`O^r|_{U_α}`); by `restrictFree_hom_ext` and `hom_ext_of_gen` it suffices to compare values on the
generators `e_i|_P`: the left side is `Σ_j (swap g)_{ji}|_P • e_j` by
`restrictFreeIso_hom_app_freeSec` and `matrixHom_app_freeSec`, the right side is
`e_α'(σ^α_i|_{k''P})` because `restrictιIso` acts on sections as a restriction map
(`restrictιIso_inv_app`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry bundleFamilyOfCocycle

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- Two successive restrictions combine into one. -/
theorem resTrans (M : Y.Modules) {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restriction along `le_rfl` is the identity. -/
theorem resRfl (M : Y.Modules) {U : Y.Opens} (h : U ≤ U) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h).op x = x := by
  have : (homOfLE h : U ⟶ U) = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restriction along `eqToHom` is restriction along `homOfLE`. -/
theorem map_eqToHom_op_apply (M : Y.Modules) {V W : Y.Opens} (e : W = V) (x : Γ(M, V)) :
    M.presheaf.map (eqToHom e).op x = M.presheaf.map (homOfLE (le_of_eq e)).op x := by
  have : (eqToHom e : W ⟶ V) = homOfLE (le_of_eq e) := Subsingleton.elim _ _
  rw [this]

/-- The inverse of `restrictιIso` acts on sections as a restriction map (the two opens are equal). -/
theorem restrictιIso_inv_app_apply {V' W : Y.Opens} (h : V' ≤ W) (M : Y.Modules)
    (A : V'.toScheme.Opens) (x : Γ(M, V'.ι ''ᵁ A)) :
    (restrictιIso h M).inv.app A x =
      M.presheaf.map (homOfLE (le_of_eq (image_homOfLE_image h A))).op x := by
  have e : (restrictιIso h M).inv.app A =
      M.presheaf.map (eqToHom (image_homOfLE_image h A)).op := by
    simp only [restrictιIso, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Hom.comp_app,
      restrictFunctorComp_hom_app_app, restrictFunctorCongr_inv_app_app]
    exact glueAux_map2 M.presheaf _ _ _
  rw [e]
  exact map_eqToHom_op_apply M _ x

/-- `restrictιIso` acts on sections as a restriction map (the two opens are equal). -/
theorem restrictιIso_hom_app_apply {V' W : Y.Opens} (h : V' ≤ W) (M : Y.Modules)
    (A : V'.toScheme.Opens) (x : Γ(M, W.ι ''ᵁ (Y.homOfLE h ''ᵁ A))) :
    (restrictιIso h M).hom.app A x =
      M.presheaf.map (homOfLE (le_of_eq (image_homOfLE_image h A).symm)).op x := by
  have h1 := modIso_inv_app_hom_app (restrictιIso h M) A x
  have h3 := restrictιIso_inv_app_apply h M A ((restrictιIso h M).hom.app A x)
  have h4 : M.presheaf.map (homOfLE (le_of_eq (image_homOfLE_image h A))).op
      ((restrictιIso h M).hom.app A x) = x := h3.symm.trans h1
  have h2 := congrArg (M.presheaf.map (homOfLE (le_of_eq (image_homOfLE_image h A).symm)).op) h4
  have h5 : M.presheaf.map (homOfLE (le_of_eq (image_homOfLE_image h A).symm)).op
      (M.presheaf.map (homOfLE (le_of_eq (image_homOfLE_image h A))).op
        ((restrictιIso h M).hom.app A x)) = (restrictιIso h M).hom.app A x :=
    (resTrans M _ _ _).trans (resRfl M _ _)
  exact h5.symm.trans h2

/-- Morphisms commute with restriction (elementwise). -/
theorem appRes {M N : Y.Modules} (φ : M ⟶ N) {U U' : Y.Opens} (h : U' ≤ U) (x : Γ(M, U)) :
    φ.app U' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app U x) :=
  congr($(φ.val.naturality (homOfLE h).op) x)

section Frame

variable {ι : Type u} {r : ℕ} (U : ι → Y.Opens) (M : Y.Modules)
  (e : ∀ α, M.restrict (U α).ι ≅ Modules.free (X := (U α).toScheme) (ULift.{u} (Fin r)))

/-- The `i`-th frame section `σ^α_i := e_α⁻¹(e_i) ∈ Γ(M, U_α)` given by the block isomorphism `e_α`. -/
def frameSec (α : ι) (i : ULift.{u} (Fin r)) : Γ(M, (U α).ι ''ᵁ ⊤) :=
  (e α).inv.app ⊤ (freeSec (ULift.{u} (Fin r)) i ⊤)

theorem image_homOfLE_image_le (α α' : ι) (P : (U α ⊓ U α').toScheme.Opens) :
    (U α').ι ''ᵁ (Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ P) ≤ (U α).ι ''ᵁ ⊤ := by
  rw [image_homOfLE_image, Scheme.Opens.ι_image_top]
  exact ((U α ⊓ U α').ι_image_le P).trans inf_le_left

/-- The transition coefficient `c_{ji} = (swap g)_{ji}|_P`, transported to `Γ(U_α', k''P)`. -/
def transitionCoeff (α α' : ι) (g : Matrix (Fin r) (Fin r) Γ(Y, U α' ⊓ U α))
    (P : (U α ⊓ U α').toScheme.Opens) (j i : ULift.{u} (Fin r)) :
    Γ(U α', Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ P) :=
  ((Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')).appIso P).inv
    ((U α ⊓ U α').toScheme.presheaf.map (homOfLE (le_top : P ≤ ⊤)).op
      ((U α ⊓ U α').topIso.inv (swapMatrix (U α) (U α') g j.down i.down)))

/-- The value of `freeTransition` on the generator `e_i|_P`. -/
theorem freeTransition_app_freeSec (α α' : ι) (g : Matrix (Fin r) (Fin r) Γ(Y, U α' ⊓ U α))
    (i : ULift.{u} (Fin r)) (P : (U α ⊓ U α').toScheme.Opens) :
    (freeTransition (U α) (U α') g).app P
        (freeSec (ULift.{u} (Fin r)) i (Y.homOfLE (inf_le_left : U α ⊓ U α' ≤ U α) ''ᵁ P)) =
      (∑ j, transitionCoeff U α α' g P j i •
        freeSec (ULift.{u} (Fin r)) j (Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ P) :
        Γ(Modules.free (X := (U α').toScheme) (ULift.{u} (Fin r)),
          Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ P)) := by
  have h0 : (U α ⊓ U α' : Y.Opens) ≤ U α := inf_le_left
  have h1 : (U α ⊓ U α' : Y.Opens) ≤ U α' := inf_le_right
  change (restrictFreeIso' (r := r) h1).inv.app P
    ((matrixHom' (U α ⊓ U α') (swapMatrix (U α) (U α') g)).app P
      ((restrictFreeIso' (r := r) h0).hom.app P
        (freeSec (ULift.{u} (Fin r)) i (Y.homOfLE h0 ''ᵁ P)))) = _
  have hA : (restrictFreeIso' (r := r) h0).hom.app P
      (freeSec (ULift.{u} (Fin r)) i (Y.homOfLE h0 ''ᵁ P)) = freeSec (ULift.{u} (Fin r)) i P :=
    restrictFreeIso_hom_app_freeSec h0 i P
  have hB : ∀ j, (restrictFreeIso' (r := r) h1).inv.app P (freeSec (ULift.{u} (Fin r)) j P) =
      ((Modules.free (ULift.{u} (Fin r))).restrictAppIso (Y.homOfLE h1) P).inv
        (freeSec (ULift.{u} (Fin r)) j (Y.homOfLE h1 ''ᵁ P)) := fun j => by
    rw [← restrictFreeIso_hom_app_freeSec h1 j P]
    exact modIso_inv_app_hom_app _ _ _
  rw [hA, matrixHom_app_freeSec, map_sum]
  simp only [Hom.app_smul, hB]
  change _ = ((Modules.free (ULift.{u} (Fin r))).restrictAppIso (Y.homOfLE h1) P).inv
    (∑ j, transitionCoeff U α α' g P j i • freeSec (ULift.{u} (Fin r)) j (Y.homOfLE h1 ''ᵁ P))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_restrictAppIso_inv_apply]
  congr 1
  unfold transitionCoeff
  exact (congr($(((Y.homOfLE h1).appIso P).inv_hom_id) _)).symm

/-- The value of the transport morphism `e_α⁻¹ ≫ restrictιIso ≫ restrictιIso⁻¹ ≫ e_α'` on the
generator `e_i|_P`: `e_α'(σ^α_i|_{k''P})`. -/
theorem transport_app_freeSec (α α' : ι) (i : ULift.{u} (Fin r))
    (P : (U α ⊓ U α').toScheme.Opens) :
    ((restrictFunctor (Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α'))).map (e α').hom).app P
      ((restrictιIso (inf_le_right : U α ⊓ U α' ≤ U α') M).inv.app P
        ((restrictιIso (inf_le_left : U α ⊓ U α' ≤ U α) M).hom.app P
          (((restrictFunctor (Y.homOfLE (inf_le_left : U α ⊓ U α' ≤ U α))).map (e α).inv).app P
            (freeSec (ULift.{u} (Fin r)) i
              (Y.homOfLE (inf_le_left : U α ⊓ U α' ≤ U α) ''ᵁ P))))) =
    (e α').hom.app (Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ P)
      (M.presheaf.map (homOfLE (image_homOfLE_image_le U α α' P)).op (frameSec U M e α i)) := by
  have h0 : (U α ⊓ U α' : Y.Opens) ≤ U α := inf_le_left
  have h1 : (U α ⊓ U α' : Y.Opens) ≤ U α' := inf_le_right
  have hs : freeSec (ULift.{u} (Fin r)) i (Y.homOfLE h0 ''ᵁ P) =
      (Modules.free (X := (U α).toScheme) (ULift.{u} (Fin r))).presheaf.map
        (homOfLE (le_top : Y.homOfLE h0 ''ᵁ P ≤ ⊤)).op (freeSec (ULift.{u} (Fin r)) i ⊤) :=
    ((SheafOfModules.freeSection (R := (U α).toScheme.ringCatSheaf) i).property
      (homOfLE (le_top : Y.homOfLE h0 ''ᵁ P ≤ ⊤)).op).symm
  change (e α').hom.app (Y.homOfLE h1 ''ᵁ P)
    ((restrictιIso h1 M).inv.app P ((restrictιIso h0 M).hom.app P
      ((e α).inv.app (Y.homOfLE h0 ''ᵁ P)
        (freeSec (ULift.{u} (Fin r)) i (Y.homOfLE h0 ''ᵁ P))))) = _
  rw [hs, appRes]
  have hσ : (M.restrict (U α).ι).presheaf.map (homOfLE (le_top : Y.homOfLE h0 ''ᵁ P ≤ ⊤)).op
      ((e α).inv.app ⊤ (freeSec (ULift.{u} (Fin r)) i ⊤)) =
      M.presheaf.map (homOfLE ((U α).ι.image_mono (le_top : Y.homOfLE h0 ''ᵁ P ≤ ⊤))).op
        (frameSec U M e α i) := rfl
  rw [hσ]
  have h2 := restrictιIso_hom_app_apply h0 M P
    (M.presheaf.map (homOfLE ((U α).ι.image_mono (le_top : Y.homOfLE h0 ''ᵁ P ≤ ⊤))).op
      (frameSec U M e α i))
  rw [resTrans] at h2
  have h3 := restrictιIso_inv_app_apply h1 M P
    (M.presheaf.map (homOfLE (((le_of_eq (image_homOfLE_image h0 P).symm)).trans
      ((U α).ι.image_mono (le_top : Y.homOfLE h0 ''ᵁ P ≤ ⊤)))).op (frameSec U M e α i))
  rw [resTrans] at h3
  rw [h2, h3]

/-- `IsTransitionCompatible` iff the transition morphism equals
`e_α⁻¹ ≫ restrictιIso ≫ restrictιIso⁻¹ ≫ e_α'`. -/
theorem isTransitionCompatible_iff_eq (F : ∀ α, (U α).toScheme.Modules)
    (θ : ∀ α α', (F α).restrict (Y.homOfLE (inf_le_left : U α ⊓ U α' ≤ U α)) ⟶
      (F α').restrict (Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α')))
    (e : ∀ α, M.restrict (U α).ι ≅ F α) (α α' : ι) :
    IsTransitionCompatible U F θ M e α α' ↔
      θ α α' = (restrictFunctor (Y.homOfLE (inf_le_left : U α ⊓ U α' ≤ U α))).map (e α).inv ≫
        (restrictιIso (inf_le_left : U α ⊓ U α' ≤ U α) M).hom ≫
        (restrictιIso (inf_le_right : U α ⊓ U α' ≤ U α') M).inv ≫
        (restrictFunctor (Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α'))).map (e α').hom := by
  unfold IsTransitionCompatible
  rw [Iso.inv_comp_eq, ← Functor.mapIso_hom, ← Iso.eq_inv_comp, Functor.mapIso_inv]

/-- **Compatibility with `freeTransition` iff the transition relation of frame sections**:
`IsTransitionCompatible U O^r (freeTransition (U α) (U α') (g α α')) M e α α'` holds iff for every
`i` and `P`, `e_α'(σ^α_i|_{k''P}) = Σ_j (swap (g α α'))_{ji}|_P • e_j`. -/
theorem isTransitionCompatible_freeTransition_iff
    (g : ∀ α α', Matrix (Fin r) (Fin r) Γ(Y, U α' ⊓ U α)) (α α' : ι) :
    IsTransitionCompatible U (fun α => Modules.free (X := (U α).toScheme) (ULift.{u} (Fin r)))
      (fun α α' => freeTransition (U α) (U α') (g α α')) M e α α' ↔
    ∀ (i : ULift.{u} (Fin r)) (P : (U α ⊓ U α').toScheme.Opens),
      (e α').hom.app (Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ P)
        (M.presheaf.map (homOfLE (image_homOfLE_image_le U α α' P)).op (frameSec U M e α i)) =
      (∑ j, transitionCoeff U α α' (g α α') P j i •
        freeSec (ULift.{u} (Fin r)) j (Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ P) :
        Γ(Modules.free (X := (U α').toScheme) (ULift.{u} (Fin r)),
          Y.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ P)) := by
  have h0 : (U α ⊓ U α' : Y.Opens) ≤ U α := inf_le_left
  have h1 : (U α ⊓ U α' : Y.Opens) ≤ U α' := inf_le_right
  rw [isTransitionCompatible_iff_eq]
  constructor
  · intro h i P
    have h2 := congrArg (fun φ => Hom.app φ P
      (freeSec (ULift.{u} (Fin r)) i (Y.homOfLE h0 ''ᵁ P))) h
    have h3 : (freeTransition (U α) (U α') (g α α')).app P
        (freeSec (ULift.{u} (Fin r)) i (Y.homOfLE h0 ''ᵁ P)) =
        ((restrictFunctor (Y.homOfLE h1)).map (e α').hom).app P
          ((restrictιIso h1 M).inv.app P ((restrictιIso h0 M).hom.app P
            (((restrictFunctor (Y.homOfLE h0)).map (e α).inv).app P
              (freeSec (ULift.{u} (Fin r)) i (Y.homOfLE h0 ''ᵁ P))))) := h2
    rw [freeTransition_app_freeSec, transport_app_freeSec] at h3
    exact h3.symm
  · intro h
    apply restrictFree_hom_ext
    intro i
    apply hom_ext_of_gen _ (gen_restrict_unit h0)
    intro O
    change (freeTransition (U α) (U α') (g α α')).app O
        ((ιFree' (ULift.{u} (Fin r)) i).app (Y.homOfLE h0 ''ᵁ O) (unitOne (U α).toScheme _)) =
      ((restrictFunctor (Y.homOfLE h1)).map (e α').hom).app O
        ((restrictιIso h1 M).inv.app O ((restrictιIso h0 M).hom.app O
          (((restrictFunctor (Y.homOfLE h0)).map (e α).inv).app O
            ((ιFree' (ULift.{u} (Fin r)) i).app (Y.homOfLE h0 ''ᵁ O) (unitOne (U α).toScheme _)))))
    rw [ιFree_app_one, freeTransition_app_freeSec, transport_app_freeSec]
    exact (h i O).symm

end Frame

end AlgebraicGeometry.Scheme.Modules

end
