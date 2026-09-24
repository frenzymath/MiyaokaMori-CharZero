import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeAdditiveShortExact
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.DegreeTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration

/-! # Additivity of the degree along a filtration

`deg E = ∑_i deg Q_i` for a filtration of a vector bundle on a smooth projective curve with
quotients `Q_i`; together with `deg E = d` this feeds the expansion in the proof of
Proposition 2.4 of the paper (Lemma 2.3).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

local instance {X : AlgebraicGeometry.Scheme.{u}} (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

private def exteriorOnePresheafIso {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf X M.val 1 ≅ M.val :=
  PresheafOfModules.isoMk
    (fun U => ModuleCat.exteriorPower.iso₁ (M.val.obj U)) (by
    intro U V i
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    change (ModuleCat.exteriorPower.iso₁ (M.val.obj V)).hom.hom
        (AlgebraicGeometry.Scheme.Modules.exteriorRestriction X M.val 1 i
          (ModuleCat.exteriorPower.mk v)) =
      (M.val.map i) ((ModuleCat.exteriorPower.iso₁ (M.val.obj U)).hom.hom
        (ModuleCat.exteriorPower.mk v))
    rw [AlgebraicGeometry.Scheme.Modules.exteriorRestriction_mk,
      ModuleCat.exteriorPower.iso₁_hom_apply,
      ModuleCat.exteriorPower.iso₁_hom_apply]
    rfl)

private def exteriorOneIso {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X M 1 ≅ M :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (exteriorOnePresheafIso M) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app M

private def exteriorZeroPresheafIso {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf X M.val 0 ≅
      (SheafOfModules.unit X.ringCatSheaf).val :=
  PresheafOfModules.isoMk
    (fun U => ModuleCat.exteriorPower.iso₀ (M.val.obj U)) (by
    intro U V i
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    change (ModuleCat.exteriorPower.iso₀ (M.val.obj V)).hom.hom
        (AlgebraicGeometry.Scheme.Modules.exteriorRestriction X M.val 0 i
          (ModuleCat.exteriorPower.mk v)) =
      ((SheafOfModules.unit X.ringCatSheaf).val.map i)
        ((ModuleCat.exteriorPower.iso₀ (M.val.obj U)).hom.hom
          (ModuleCat.exteriorPower.mk v))
    rw [AlgebraicGeometry.Scheme.Modules.exteriorRestriction_mk,
      ModuleCat.exteriorPower.iso₀_hom_apply,
      ModuleCat.exteriorPower.iso₀_hom_apply]
    exact (PresheafOfModules.unit_map_one X.ringCatSheaf.val i).symm)

private def exteriorZeroIso {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X M 0 ≅ SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (exteriorZeroPresheafIso M) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app
      (SheafOfModules.unit X.ringCatSheaf)

/-- The degree of a line bundle viewed as a vector bundle is its line-bundle degree. -/
theorem lineBundle_vector_degree {k : Type*} [Field k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety) :
    VectorBundle.degree L.toVectorBundle = L.degree := by
  rw [VectorBundle.degree_eq_lineBundle_degree_det]
  apply LineBundle.degree_congr
  dsimp [AlgebraicGeometry.VectorBundle.det]
  rw [L.rank_eq_one]
  exact exteriorOneIso L.toModules

private theorem vectorBundle_degree_eq_of_module_iso {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k}
    (E F : AlgebraicGeometry.VectorBundle C.toVariety)
    (hrank : E.rank = F.rank) (e : E.toModules ≅ F.toModules) :
    VectorBundle.degree E = VectorBundle.degree F := by
  rw [VectorBundle.degree_eq_lineBundle_degree_det, VectorBundle.degree_eq_lineBundle_degree_det]
  apply LineBundle.degree_congr
  dsimp only [AlgebraicGeometry.VectorBundle.det]
  exact AlgebraicGeometry.Scheme.Modules.moduleExteriorIso C.toScheme E.rank e ≪≫ eqToIso (by rw [hrank])

private theorem vectorBundle_degree_zero_of_rank_zero {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = 0) :
    VectorBundle.degree E = 0 := by
  rw [VectorBundle.degree_eq_lineBundle_degree_det, ← LineBundle.degree_one C]
  apply LineBundle.degree_congr
  dsimp only [AlgebraicGeometry.VectorBundle.det]
  rw [LineBundle.one_toModules]
  exact eqToIso (by rw [hE]) ≪≫ exteriorZeroIso E.toModules

private lemma fin_telescoping {r : ℕ} (a : Fin (r + 1) → ℤ) (q : Fin r → ℤ)
    (h0 : a 0 = 0)
    (hstep : ∀ i : Fin r, a i.succ = a i.castSucc + q i) :
    a (Fin.last r) = ∑ i : Fin r, q i := by
  induction r with
  | zero =>
      simpa using h0
  | succ r ihr =>
      let a' : Fin (r + 1) → ℤ := fun i => a i.castSucc
      let q' : Fin r → ℤ := fun i => q i.castSucc
      have h0' : a' 0 = 0 := by
        exact h0
      have hstep' : ∀ i : Fin r, a' i.succ = a' i.castSucc + q' i := by
        intro i
        dsimp [a', q']
        simpa using hstep i.castSucc
      have hi := ihr a' q' h0' hstep'
      calc
        a (Fin.last (r + 1)) = a (Fin.last r).succ := by rfl
        _ = a (Fin.last r).castSucc + q (Fin.last r) := hstep (Fin.last r)
        _ = (∑ i : Fin r, q i.castSucc) + q (Fin.last r) := by
          change a' (Fin.last r) + q (Fin.last r) = _
          rw [hi]
        _ = ∑ i : Fin (r + 1), q i := (Fin.sum_univ_castSucc q).symm

private theorem degree_step {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k}
    (E : AlgebraicGeometry.VectorBundle C.toVariety)
    (F : SubbundleFiltration E E.rank) (i : Fin E.rank) :
    VectorBundle.degree (F.sub i.succ) =
      VectorBundle.degree (F.sub i.castSucc) +
        LineBundle.degree (F.lineQuotient i) := by
  let S : CategoryTheory.ShortComplex C.toScheme.Modules :=
    CategoryTheory.ShortComplex.mk
      (F.incl i)
      (CategoryTheory.Limits.cokernel.π (F.incl i))
      (CategoryTheory.Limits.cokernel.condition _)
  have hS : S.ShortExact := by
    letI := F.mono i
    exact { exact := CategoryTheory.ShortComplex.exact_cokernel (F.incl i) }
  obtain ⟨q⟩ := F.quotient_iso i
  have h := VectorBundle.degree_add_of_shortExact hS
    (F.sub i.castSucc) (F.sub i.succ) (F.lineQuotient i).toVectorBundle
    (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _) q.symm
  simpa only [lineBundle_vector_degree] using h

theorem degree_eq_sum_lineQuotient_degrees {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} (E : AlgebraicGeometry.VectorBundle C.toVariety)
    (F : SubbundleFiltration E E.rank) :
    VectorBundle.degree E = ∑ i : Fin E.rank, LineBundle.degree (F.lineQuotient i) := by
  have hzero : VectorBundle.degree (F.sub (0 : Fin (E.rank + 1))) = 0 := by
    apply vectorBundle_degree_zero_of_rank_zero
      (F.sub (0 : Fin (E.rank + 1)))
    simpa using F.rank_eq (0 : Fin (E.rank + 1))
  have hstep : ∀ i : Fin E.rank,
      VectorBundle.degree (F.sub i.succ) =
        VectorBundle.degree (F.sub i.castSucc) +
          LineBundle.degree (F.lineQuotient i) := by
    intro i
    exact degree_step E F i
  have hsum := fin_telescoping
    (a := fun i : Fin (E.rank + 1) => VectorBundle.degree (F.sub i))
    (q := fun i : Fin E.rank => LineBundle.degree (F.lineQuotient i))
    hzero hstep
  have hlast : VectorBundle.degree (F.sub (Fin.last E.rank)) = VectorBundle.degree E := by
    apply vectorBundle_degree_eq_of_module_iso
      (F.sub (Fin.last E.rank)) E
      (by simpa using F.rank_eq (Fin.last E.rank))
      F.lastIso
  calc
    VectorBundle.degree E = VectorBundle.degree (F.sub (Fin.last E.rank)) := hlast.symm
    _ = ∑ i : Fin E.rank, LineBundle.degree (F.lineQuotient i) := hsum

end
