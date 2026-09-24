import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.FreeTransitionCompatible
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.RestrictToLambdaBundleFamilyTransition_PullbackSections
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.RestrictToLambdaBundleFamilyTransition_FreeTransitionSections

/-! # Pullback along a section preserves transition-compatible block isomorphisms

General form (independent of `C` and `A¹`): let `s : X → Y` be a section of `π : Y → X`
(`s ≫ π = 𝟙`), and let `M` carry block isomorphisms `e_α` on the open cover `π⁻¹U_α` compatible
with `freeTransition (π⁻¹U α) (π⁻¹U α') (g α α')`. Then `s^*M` carries block isomorphisms on the
`U_α` compatible with `freeTransition (U α) (U α') (g α α' transported along s^♯)`
(`pullback_transition_exists`). With `X = C`, `Y = A¹_C`, `s = sectionAt t`, `π = toBase` this
gives the transition formula for the restriction of a bundle family to `λ = t`.

Reference: Hartshorne II Ex. 5.18 (pullback preserves local trivializations and transition
functions).

Proof: `ε_α := baseChangeFreeIso`; by `isTransitionCompatible_freeTransition_iff` the
compatibility reduces to a relation between frame sections: `ε_α⁻¹(e_i)` is the pulled-back frame
section `s^*(σ^α_i)` (`baseChangeFreeIso_inv_app_freeSec`); after restricting to `U_αα'` and
applying `ε_α'` it becomes "apply `e_α'` (the section form of `he`), pull back (semilinearly:
coefficients through `s^♯`), then `pullbackObjFreeIso`"
(`baseChangeFreeIso_hom_app_pullbackSectionsOn`,
`pullbackObjFreeIso_hom_app_pullbackSectionsOn_sum`); finally compare coefficients
(`coeff_identity`: both sides reduce to the same `s.appLE`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry bundleFamilyOfCocycle

section RingLemmas

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- Restriction along `le_rfl` is the identity (structure sheaf). -/
theorem resO_rfl {U : Y.Opens} (h : U ≤ U) (a : Γ(Y, U)) :
    Y.presheaf.map (homOfLE h).op a = a := by
  have : (homOfLE h : U ⟶ U) = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- Restriction along `eqToHom` is restriction along `homOfLE` (structure sheaf). -/
theorem mapO_eqToHom_op_apply {V W : Y.Opens} (e : W = V) (a : Γ(Y, V)) :
    Y.presheaf.map (eqToHom e).op a = Y.presheaf.map (homOfLE (le_of_eq e)).op a := by
  have : (eqToHom e : W ⟶ V) = homOfLE (le_of_eq e) := Subsingleton.elim _ _
  rw [this]

/-- The restriction maps of an open subscheme are those of `Y`. -/
theorem toScheme_map_apply (U : Y.Opens) {A B : U.toScheme.Opens} (h : A ≤ B) (v : Γ(U, B)) :
    U.toScheme.presheaf.map (homOfLE h).op v =
      Y.presheaf.map (homOfLE (U.ι.image_mono h)).op v := rfl

/-- `topIso.inv` is restriction along an equality of opens. -/
theorem topIso_inv_apply (U : Y.Opens) (a : Γ(Y, U)) :
    U.topIso.inv a = Y.presheaf.map (homOfLE (le_of_eq U.ι_image_top)).op a := by
  rw [← mapO_eqToHom_op_apply (e := U.ι_image_top)]
  rfl

/-- The inverse of the `appIso` of `homOfLE` acts on sections as restriction along an equality of
opens. -/
theorem homOfLE_appIso_inv_apply {V' W : Y.Opens} (h : V' ≤ W) (A : V'.toScheme.Opens)
    (y : Γ(Y, V'.ι ''ᵁ A)) :
    ((Y.homOfLE h).appIso A).inv y =
      Y.presheaf.map (homOfLE (le_of_eq (image_homOfLE_image h A))).op y := by
  have e := image_homOfLE_image h A
  have h1 : ((Y.homOfLE h).appIso A).hom (Y.presheaf.map (homOfLE (le_of_eq e)).op y) = y := by
    rw [Scheme.Hom.appIso_hom', Scheme.homOfLE_appLE]
    exact (res_res_apply _ _ y).trans (resO_rfl _ y)
  have h2 := ConcreteCategory.congr_hom ((Y.homOfLE h).appIso A).hom_inv_id
    (Y.presheaf.map (homOfLE (le_of_eq e)).op y)
  change ((Y.homOfLE h).appIso A).inv (((Y.homOfLE h).appIso A).hom
    (Y.presheaf.map (homOfLE (le_of_eq e)).op y)) = Y.presheaf.map (homOfLE (le_of_eq e)).op y at h2
  rw [h1] at h2
  exact h2

/-- `f.appLE` followed by restriction (elementwise). -/
theorem appLE_map_apply {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V) (a : Γ(Y, U)) :
    X.presheaf.map (homOfLE h).op (f.appLE U V e a) = f.appLE U V' (h.trans e) a := by
  have := congr($(Scheme.Hom.appLE_map f e (homOfLE h).op) a)
  simpa only [CommRingCat.comp_apply] using this

/-- Restriction followed by `f.appLE` (elementwise). -/
theorem map_appLE_apply {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {U U' : Y.Opens} {V : X.Opens}
    (e : V ≤ f ⁻¹ᵁ U) (h : U ≤ U') (a : Γ(Y, U')) :
    f.appLE U V e (Y.presheaf.map (homOfLE h).op a) =
      f.appLE U' V (e.trans ((Opens.map f.base).map (homOfLE h)).le) a := by
  have := congr($(Scheme.Hom.map_appLE f e (homOfLE h).op) a)
  simpa only [CommRingCat.comp_apply] using this

/-- Pulling back a section and then restricting the target open. -/
theorem pullbackSectionsOn_restrict_target {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) {V : Y.Opens} {V' W' : X.Opens} (h : V' ≤ f ⁻¹ᵁ V) (h' : W' ≤ f ⁻¹ᵁ V)
    (hW' : W' ≤ V') (x : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hW').op
        (pullbackSectionsOn f M V V' h x) =
      pullbackSectionsOn f M V W' h' x := by
  rw [pullbackSectionsOn_restrict f M h h' le_rfl hW', resRfl]

end RingLemmas

section Section

variable {X Y : AlgebraicGeometry.Scheme.{u}} (s : X ⟶ Y) (π : Y ⟶ X) (hsπ : s ≫ π = 𝟙 X)

include hsπ in
/-- Preimages under the section `s`: `s⁻¹(π⁻¹ W) = W`. -/
theorem preimage_section (W : X.Opens) : s ⁻¹ᵁ (π ⁻¹ᵁ W) = W := by
  rw [← Scheme.Hom.comp_preimage, hsπ]
  rfl

variable {ι : Type u} (U : ι → X.Opens) {r : ℕ}

include hsπ in
/-- Comparison of coefficients: `s_α'` sends the transition coefficient `(swap g)_{ji}` on `Y` to
the transition coefficient `(swap (g(t)))_{ji}` on `X`; both sides are the same `s.appLE`. -/
theorem coeff_identity (α α' : ι) (g : Matrix (Fin r) (Fin r) Γ(Y, π ⁻¹ᵁ U α' ⊓ π ⁻¹ᵁ U α))
    (O : (U α ⊓ U α').toScheme.Opens) (j i : ULift.{u} (Fin r))
    (hA : X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O ≤
      (s.resLE (π ⁻¹ᵁ U α') (U α') (le_of_eq (preimage_section s π hsπ (U α')).symm)) ⁻¹ᵁ
        (Y.homOfLE (inf_le_right : π ⁻¹ᵁ U α ⊓ π ⁻¹ᵁ U α' ≤ π ⁻¹ᵁ U α') ''ᵁ ⊤)) :
    (s.resLE (π ⁻¹ᵁ U α') (U α') (le_of_eq (preimage_section s π hsπ (U α')).symm)).appLE
        (Y.homOfLE (inf_le_right : π ⁻¹ᵁ U α ⊓ π ⁻¹ᵁ U α' ≤ π ⁻¹ᵁ U α') ''ᵁ ⊤)
        (X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O) hA
        (transitionCoeff (fun α => π ⁻¹ᵁ U α) α α' g ⊤ j i) =
      transitionCoeff U α α' (g.map (s.appLE (π ⁻¹ᵁ (U α' ⊓ U α)) (U α' ⊓ U α)
        (le_of_eq (preimage_section s π hsπ _).symm))) O j i := by
  unfold transitionCoeff
  rw [Scheme.Hom.resLE_appLE, toScheme_map_apply, toScheme_map_apply, topIso_inv_apply,
    topIso_inv_apply, homOfLE_appIso_inv_apply, homOfLE_appIso_inv_apply]
  change s.appLE _ _ _ (Y.presheaf.map _ (Y.presheaf.map _ (Y.presheaf.map _
      (Y.presheaf.map (homOfLE _).op (g j.down i.down))))) =
    X.presheaf.map _ (X.presheaf.map _ (X.presheaf.map _ (X.presheaf.map (homOfLE _).op
      (s.appLE _ _ _ (g j.down i.down)))))
  rw [res_res_apply, res_res_apply, res_res_apply, res_res_apply, res_res_apply, res_res_apply,
    map_appLE_apply]
  exact (appLE_map_apply s _ _ (g j.down i.down)).symm

include hsπ in
/-- **Pullback preserves transition-compatible block isomorphisms** (general form): if `s : X → Y`
is a section of `π : Y → X` and `M` carries block isomorphisms `e_α` on the cover `π⁻¹U_α`
compatible with `freeTransition (π⁻¹U α) (π⁻¹U α') (g α α')`, then `s^*M` carries block
isomorphisms on the `U_α` compatible with
`freeTransition (U α) (U α') (g α α' transported along s^♯)`. -/
theorem pullback_transition_exists (M : Y.Modules)
    (g : ∀ α α', Matrix (Fin r) (Fin r) Γ(Y, π ⁻¹ᵁ U α' ⊓ π ⁻¹ᵁ U α))
    (e : ∀ α, M.restrict (π ⁻¹ᵁ U α).ι ≅
      Modules.free (X := (π ⁻¹ᵁ U α).toScheme) (ULift.{u} (Fin r)))
    (he : ∀ α α', IsTransitionCompatible (fun α => π ⁻¹ᵁ U α)
      (fun α => Modules.free (X := (π ⁻¹ᵁ U α).toScheme) (ULift.{u} (Fin r)))
      (fun α α' => freeTransition (π ⁻¹ᵁ U α) (π ⁻¹ᵁ U α') (g α α')) M e α α') :
    ∃ ε : ∀ α, ((AlgebraicGeometry.Scheme.Modules.pullback s).obj M).restrict (U α).ι ≅
        Modules.free (X := (U α).toScheme) (ULift.{u} (Fin r)),
      ∀ α α', IsTransitionCompatible U
        (fun α => Modules.free (X := (U α).toScheme) (ULift.{u} (Fin r)))
        (fun α α' => freeTransition (U α) (U α') ((g α α').map (s.appLE (π ⁻¹ᵁ (U α' ⊓ U α))
          (U α' ⊓ U α) (le_of_eq (preimage_section s π hsπ _).symm))))
        ((AlgebraicGeometry.Scheme.Modules.pullback s).obj M) ε α α' := by
  have hpre : ∀ W : X.Opens, s ⁻¹ᵁ (π ⁻¹ᵁ W) = W := preimage_section s π hsπ
  have sq : ∀ α, s.resLE (π ⁻¹ᵁ U α) (U α) (le_of_eq (hpre (U α)).symm) ≫ (π ⁻¹ᵁ U α).ι =
      (U α).ι ≫ s := fun α => Scheme.Hom.resLE_comp_ι _ _
  refine ⟨fun α => baseChangeFreeIso s (s.resLE (π ⁻¹ᵁ U α) (U α) (le_of_eq (hpre (U α)).symm))
    (U α).ι (π ⁻¹ᵁ U α).ι (sq α) M (e α), fun α α' => ?_⟩
  refine (isTransitionCompatible_freeTransition_iff U _ _ _ α α').mpr ?_
  intro i O
  -- inclusions of opens
  have hO : (U α').ι ''ᵁ (X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O) ≤ U α ⊓ U α' := by
    rw [image_homOfLE_image]
    exact (U α ⊓ U α').ι_image_le O
  have h₂ : (U α').ι ''ᵁ (X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O) ≤
      s ⁻¹ᵁ ((π ⁻¹ᵁ U α).ι ''ᵁ ⊤) := by
    rw [Scheme.Opens.ι_image_top, hpre]
    exact hO.trans inf_le_left
  have hWW := image_homOfLE_image_le (fun α => π ⁻¹ᵁ U α) α α' ⊤
  have h₃ : (U α').ι ''ᵁ (X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O) ≤
      s ⁻¹ᵁ ((π ⁻¹ᵁ U α').ι ''ᵁ
        (Y.homOfLE (inf_le_right : π ⁻¹ᵁ U α ⊓ π ⁻¹ᵁ U α' ≤ π ⁻¹ᵁ U α') ''ᵁ ⊤)) := by
    rw [image_homOfLE_image, image_homOfLE_image, Scheme.Opens.ι_image_top,
      ← Scheme.Hom.preimage_inf, hpre]
    exact (U α ⊓ U α').ι_image_le O
  have hA : X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O ≤
      (s.resLE (π ⁻¹ᵁ U α') (U α') (le_of_eq (hpre (U α')).symm)) ⁻¹ᵁ
        (Y.homOfLE (inf_le_right : π ⁻¹ᵁ U α ⊓ π ⁻¹ᵁ U α' ≤ π ⁻¹ᵁ U α') ''ᵁ ⊤) :=
    (Scheme.Hom.le_resLE_preimage_iff s _ _ _).mpr h₃
  -- left-hand side: pullback of the frame section
  have step1 : ((AlgebraicGeometry.Scheme.Modules.pullback s).obj M).presheaf.map
      (homOfLE (image_homOfLE_image_le U α α' O)).op
      ((baseChangeFreeIso s (s.resLE (π ⁻¹ᵁ U α) (U α) (le_of_eq (hpre (U α)).symm))
        (U α).ι (π ⁻¹ᵁ U α).ι (sq α) M (e α)).inv.app ⊤ (freeSec (ULift.{u} (Fin r)) i ⊤)) =
      pullbackSectionsOn s M
        ((π ⁻¹ᵁ U α').ι ''ᵁ (Y.homOfLE (inf_le_right : π ⁻¹ᵁ U α ⊓ π ⁻¹ᵁ U α' ≤ π ⁻¹ᵁ U α') ''ᵁ ⊤))
        ((U α').ι ''ᵁ (X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O)) h₃
        (M.presheaf.map (homOfLE hWW).op (frameSec (fun α => π ⁻¹ᵁ U α) M e α i)) := by
    rw [baseChangeFreeIso_inv_app_freeSec]
    exact (pullbackSectionsOn_restrict_target s M _ h₂ _ _).trans
      (pullbackSectionsOn_res s M h₂ h₃ hWW _)
  refine (congrArg _ step1).trans ?_
  -- the section form of `he`
  have hhe := (isTransitionCompatible_freeTransition_iff (fun α => π ⁻¹ᵁ U α) M e g α α').mp
    (he α α') i ⊤
  have step2 : (baseChangeFreeIso s (s.resLE (π ⁻¹ᵁ U α') (U α') (le_of_eq (hpre (U α')).symm))
      (U α').ι (π ⁻¹ᵁ U α').ι (sq α') M (e α')).hom.app
        (X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O)
      (pullbackSectionsOn s M
        ((π ⁻¹ᵁ U α').ι ''ᵁ (Y.homOfLE (inf_le_right : π ⁻¹ᵁ U α ⊓ π ⁻¹ᵁ U α' ≤ π ⁻¹ᵁ U α') ''ᵁ ⊤))
        ((U α').ι ''ᵁ (X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O)) h₃
        (M.presheaf.map (homOfLE hWW).op (frameSec (fun α => π ⁻¹ᵁ U α) M e α i))) =
      ∑ j, (s.resLE (π ⁻¹ᵁ U α') (U α') (le_of_eq (hpre (U α')).symm)).appLE _ _ hA
          (transitionCoeff (fun α => π ⁻¹ᵁ U α) α α' (g α α') ⊤ j i) •
        freeSec (ULift.{u} (Fin r)) j (X.homOfLE (inf_le_right : U α ⊓ U α' ≤ U α') ''ᵁ O) := by
    rw [baseChangeFreeIso_hom_app_pullbackSectionsOn s _ (U α').ι (π ⁻¹ᵁ U α').ι (sq α') M (e α')
      _ _ h₃ hA, hhe, pullbackObjFreeIso_hom_app_pullbackSectionsOn_sum]
  refine step2.trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_identity s π hsπ U α α' (g α α') O j i hA]

end Section

end AlgebraicGeometry.Scheme.Modules

end
