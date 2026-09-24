import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousLocalFormula
import MiyaokaMori.AlgebraicGeometry.Modules.HomogeneousEquationAsSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.HomogeneousEquationSectionAtTotalSpaceSectionLemmas
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProductEquationVanishes
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProductZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.GenericallyScalarOfCoefficientsZeroThickeningRestrict

/-! # Vanishing of homogeneous equations on thickenings, general form

Variable-level lemmas for the vanishing of the equations on the thickening
(`restrictToThickening_evalHomogeneous_eq_zero`, `ThickeningEquationsVanish`). All reasoning about the closed
immersion `i : C̃_(κ)(L) → Tot(L)` is done here with schemes, morphisms and sheaves as variables; the concrete
module only instantiates.

1. `thickeningRestrict_eq_zero_of_sectionPullbackAlong_eq_zero`: `thickeningRestrict i p h M P`
   (the variable-level form of `restrictToThickening`, module
   `GenericallyScalarOfCoefficientsZeroThickeningRestrict`) is `0` as soon as `i^* P = 0`, because it
   is a module map applied to `i^* P`.
2. `thickeningRestrict_map_evalHomogeneous_eq_zero`: if the homogeneous evaluation `F` of the
   restricted tuple `(thickeningRestrict i p h A (P ℓ))_ℓ` vanishes, then for every module map
   `Θ : (p^*A)^{⊗e} ⟶ p^*M'` the restriction of `Θ(F(P))` vanishes. Proof: `thickeningRestrict`
   of `Θ(F(P))` is a module map applied to `i^*(Θ(F(P))) = (i^*Θ)(i^* F(P))`
   (`sectionPullbackAlong_naturality`), so it suffices that `i^* F(P) = 0`;
   `evalHomogeneousAtSections_pullback` gives `θ_e(i^* F(P)) = F(i^* P)` with
   `θ_e = pullbackTensorPowIso i (p^*A) e` an isomorphism; and `F(i^*P) = 0` because the restricted
   tuple is `Ψ ∘ i^*P` for the isomorphism `Ψ = (pullbackComp i p).app A : i^*p^*A ≅ g^*A`
   (after `subst h`, the transport `eqToHom` is the identity), `F(Ψ ∘ i^*P) = Ψ^{⊗e}(F(i^*P))`
   (`evalHomogeneousAtSections_iso`), and an isomorphism reflects `0`
   (`iso_hom_app_top_eq_zero_iff_hes`).
3. `evalHomogeneousAtSections_coordinates_eq_zero_of_factors_cone`: the homogeneous equations
   `F_j` vanish on the coordinates of any morphism `W → 𝒵 = V(F_j(τ)) ⊆ Tot(A^{⊕(N+1)})` into the
   cone. This is `puncturedConeToProduct.eval_coord_eq_zero_aux` (`PuncturedConeToProduct`) with the open
   immersion `W.ι` of the punctured cone replaced by an arbitrary morphism `j₀ : W → 𝒵` and the
   `k`-structure of `W` an arbitrary instance whose structure morphism is `q ≫ (C ↘ Spec k)`. Proof
   (Stacks 02OR, direction "factors through the zero scheme ⇒ the pulled-back section vanishes"):
   `F_j(τ) ∈ Γ(Tot, (π^*A)^{⊗d})` pulls back to `0` along `ι = I.subschemeι`
   (`sectionPullbackAlong_subschemeι_eq_zero`, `I(F_j(τ)) ≤ I = ⨆ I(F_j(τ))`), hence along `jW = j₀ ≫ ι`
   (`ModuleSections.pullback_comp`); `evalHomogeneousAtSections_pullback` along `jW` gives
   `F_j(jW^*τ_0, …, jW^*τ_N) = 0`; the coordinates of `jW` are the images of the `jW^*τ_ℓ` under
   `pullbackComp jW π` (`totalSpaceHomEquiv_naturality_map`), and `evalHomogeneousAtSections_iso_eq_zero`
   transports along that isomorphism.

In the paper: "its reduction modulo `t^{k+1}` is zero, because `ȷ` takes values in `𝒵`".
-/
/- `sectionPullbackAlong` is by definition the adjunction unit, and `ModuleSections.pullback` is its `Γ`-typed
reducible abbreviation: the proofs below use `simp only [sectionPullbackAlong_eq_pullback]` (to reach the
latter) or plain `unfold sectionPullbackAlong` (to reach the unit). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `thickeningRestrict i p h M P = 0` as soon as `i^* P = 0` (it is a module map applied to
`i^* P`). -/
theorem thickeningRestrict_eq_zero_of_sectionPullbackAlong_eq_zero {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (i : X ⟶ Y) (p : Y ⟶ Z) {g : X ⟶ Z} (h : i ≫ p = g) (M : Z.Modules)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback p).obj M).val.obj (Opposite.op ⊤) : Type u))
    (hP : sectionPullbackAlong i P = 0) :
    thickeningRestrict i p h M P = 0 := by
  unfold thickeningRestrict
  rw [hP]
  exact map_zero _

/-- **Restriction of a transported homogeneous evaluation vanishes** when the homogeneous
evaluation of the restricted tuple vanishes: for `Θ : (p^*A)^{⊗e} ⟶ p^*M'`,
`thickeningRestrict i p h M' (Θ (F(P))) = 0` if `F((thickeningRestrict i p h A (P ℓ))_ℓ) = 0`.
See the module docstring, item 2. -/
theorem thickeningRestrict_map_evalHomogeneous_eq_zero {k : Type u} [Field k]
    {X Y Z : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (i : X ⟶ Y) [i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] (p : Y ⟶ Z) {g : X ⟶ Z}
    (h : i ≫ p = g) (A : Z.Modules) [A.IsLineBundle] {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k)
    (hF : F.IsHomogeneous e)
    (P : Fin (N + 1) → (((AlgebraicGeometry.Scheme.Modules.pullback p).obj A).val.obj (Opposite.op ⊤) : Type u))
    (hP : evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A) F hF
      (fun ℓ => thickeningRestrict i p h A (P ℓ)) = 0)
    {M' : Z.Modules}
    (Θ : AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) e ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback p).obj M') :
    thickeningRestrict i p h M'
      (Θ.app ⊤ (evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) F hF P)) = 0 := by
  subst h
  apply thickeningRestrict_eq_zero_of_sectionPullbackAlong_eq_zero
  -- i^*(Θ(F(P))) = (i^*Θ)(i^*F(P)); it suffices that i^*F(P) = 0
  change sectionPullbackAlong i ((Θ.val.app (Opposite.op ⊤)).hom
    (evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) F hF P)) = 0
  rw [sectionPullbackAlong_naturality]
  suffices hz : sectionPullbackAlong i
      (evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) F hF P) = 0 by
    rw [hz]
    exact map_zero _
  -- F(i^*P) = 0: the restricted tuple is Ψ ∘ i^*P for the iso Ψ = (pullbackComp i p).app A
  have hΨ : (fun ℓ => thickeningRestrict i p rfl A (P ℓ)) =
      fun ℓ => ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i p).app A).hom.val.app
        (Opposite.op ⊤)).hom (sectionPullbackAlong i (P ℓ))) := by
    funext ℓ
    unfold thickeningRestrict
    simp only [CategoryTheory.eqToHom_refl, CategoryTheory.Category.comp_id]
  rw [hΨ, ← evalHomogeneousAtSections_iso
    (M := (AlgebraicGeometry.Scheme.Modules.pullback i).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A))
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp i p).app A) F hF
    (fun ℓ => sectionPullbackAlong i (P ℓ))] at hP
  have hFi : evalHomogeneousAtSections
      ((AlgebraicGeometry.Scheme.Modules.pullback i).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A))
      F hF (fun ℓ => sectionPullbackAlong i (P ℓ)) = 0 :=
    (AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff_hes _ _).mp hP
  -- θ_e (i^* F(P)) = F(i^* P) = 0 and θ_e is an isomorphism
  have h5 := evalHomogeneousAtSections_pullback (k := k) i
    ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) F hF P
  rw [hFi] at h5
  exact (AlgebraicGeometry.Scheme.Modules.iso_hom_app_top_eq_zero_iff_hes _ _).mp h5

/-- **The homogeneous equations vanish on the coordinates of any morphism into the cone**
`𝒵 = V(F_j(τ)) ⊆ Tot(A^{⊕(N+1)})`: for `j₀ : W → 𝒵`, `q = j₀ ≫ ι ≫ π : W → C`, and any
`k`-structure on `W` with structure morphism `q ≫ (C ↘ Spec k)`, `F_j` evaluated at the coordinates
`(q^*π_ℓ)(σ)` of the section `σ ∈ Γ(W, q^*A^{⊕(N+1)})` corresponding to `j₀ ≫ ι` is `0`.
Generalizes `puncturedConeToProduct.eval_coord_eq_zero_aux` (`W.ι` replaced by `j₀`). See the module
docstring, item 3. -/
theorem evalHomogeneousAtSections_coordinates_eq_zero_of_factors_cone {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}} [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (A : C.Modules) [A.IsLineBundle] (N : ℕ) {ι : Type u} (deg : ι → ℕ)
    (F : ι → MvPolynomial (Fin (N + 1)) k) (hF : ∀ j, (F j).IsHomogeneous (deg j))
    {W : AlgebraicGeometry.Scheme.{u}} [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (j₀ : W ⟶ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection A N (F j) (hF j))).subscheme)
    (q : W ⟶ C)
    (hq : (j₀ ≫ (⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection A N (F j) (hF j))).subschemeι) ≫
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = q)
    (hW : (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      q ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    (j : ι) :
    evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback q).obj A) (F j) (hF j)
      (fun ℓ => (((AlgebraicGeometry.Scheme.Modules.pullback q).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
          (CategoryTheory.Over.mk q) (CategoryTheory.Over.homMk _ hq))) = 0 := by
  subst hq
  let V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  let T := AlgebraicGeometry.Scheme.totalSpace V
  let p := T.hom
  let I : T.left.IdealSheafData := ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
    (homogeneousEquationSection A N (F j) (hF j))
  let jW : W ⟶ T.left := j₀ ≫ I.subschemeι
  let instT : T.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨p ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have hover : jW.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨by
    show jW ≫ (p ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
      W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
    rw [hW]
    simp only [Category.assoc]
    rfl⟩
  -- F_j(τ) vanishes on Z, hence on W
  have hI : AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A N (F j) (hF j)) ≤ I :=
    le_iSup (fun j => AlgebraicGeometry.Scheme.idealSheafOfSection _
      (homogeneousEquationSection A N (F j) (hF j))) j
  have hz1 : sectionPullbackAlong I.subschemeι
      (homogeneousEquationSection A N (F j) (hF j)) = 0 :=
    AlgebraicGeometry.Scheme.sectionPullbackAlong_subschemeι_eq_zero I _ _ hI
  have hz2 : sectionPullbackAlong jW (homogeneousEquationSection A N (F j) (hF j)) = 0 := by
    have h := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp j₀ I.subschemeι
      (homogeneousEquationSection A N (F j) (hF j))
    change ((AlgebraicGeometry.Scheme.Modules.pullbackComp j₀ I.subschemeι).app _).hom.app ⊤
      (sectionPullbackAlong j₀ (sectionPullbackAlong I.subschemeι
        (homogeneousEquationSection A N (F j) (hF j)))) =
      sectionPullbackAlong jW (homogeneousEquationSection A N (F j) (hF j)) at h
    rw [hz1] at h
    rw [← h]
    have h0 : sectionPullbackAlong j₀ (0 : (((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) (deg j))).val.obj (Opposite.op ⊤) : Type u)) = 0 := by
      unfold sectionPullbackAlong
      exact map_zero _
    exact (congrArg (fun z => ((AlgebraicGeometry.Scheme.Modules.pullbackComp j₀ I.subschemeι).app
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) (deg j))).hom.app ⊤ z) h0).trans
      (map_zero _)
  -- F_j on the pulled-back tautological coordinates vanishes
  let τ := AlgebraicGeometry.Scheme.totalSpaceHomEquiv V T (CategoryTheory.CategoryStruct.id T)
  let τc : Fin (N + 1) → ((((AlgebraicGeometry.Scheme.Modules.pullback p).obj A).val.obj (Opposite.op ⊤)) : Type u) :=
    fun i => (((AlgebraicGeometry.Scheme.Modules.pullback p).map
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) i)).val.app (Opposite.op ⊤)).hom τ
  have h5 := evalHomogeneousAtSections_pullback (k := k) jW
    ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) (F j) (hF j) τc
  have hFτ : evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A)
      (F j) (hF j) τc = homogeneousEquationSection A N (F j) (hF j) := rfl
  rw [hFτ, hz2] at h5
  have h6 : evalHomogeneousAtSections
      ((AlgebraicGeometry.Scheme.Modules.pullback jW).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A))
      (F j) (hF j) (fun i => sectionPullbackAlong jW (τc i)) = 0 := by
    rw [← h5]
    exact map_zero _
  -- the coordinates z_ℓ are the images of jW^*τ_ℓ under pullbackComp
  let Θ : (AlgebraicGeometry.Scheme.Modules.pullback jW).obj ((AlgebraicGeometry.Scheme.Modules.pullback p).obj A) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (jW ≫ p)).obj A :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp jW p).app A
  have hcoord : (fun ℓ => (((AlgebraicGeometry.Scheme.Modules.pullback (jW ≫ p)).map
        (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (jW ≫ p))
          (CategoryTheory.Over.homMk jW rfl))) =
      fun ℓ => ((Θ.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong jW (τc ℓ))) := by
    funext ℓ
    have hn := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_map V
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ) T jW (𝟙 T)
    rw [Category.comp_id] at hn
    exact hn
  rw [hcoord]
  exact evalHomogeneousAtSections_iso_eq_zero Θ (F j) (hF j)
    (fun i => sectionPullbackAlong jW (τc i)) h6

end
