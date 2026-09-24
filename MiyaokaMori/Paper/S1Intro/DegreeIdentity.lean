import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegreeEqLineBundleDegreeDet
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.CanonicalDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.CurveDegreeIntersectionCompat
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.CyclePushforward
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.DetPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DetTangentAnticanonical
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegreePushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula

/-! # The degree identity `-K_X · f_*[C] = deg f^*T_X`

The identity `d = -K_X · f_*[C] = deg f^*T_X` used in §2 of the paper (the quantity `d` of the
main theorem): it is a theorem, not a definition, and follows from the projection formula together
with `det T_X ≅ ω_X^{-1}`.

`K_X` is a canonical divisor, i.e. any Cartier divisor `K` with `O_X(K) ≅ ω_X`; the intersection
number `-K · f_*[C]` depends only on the linear equivalence class of `K`. The main statement
`degree_identity` is stated for such a divisor; `degree_identity_canonicalBundle` is the same
identity written with the canonical bundle, `-(ω_X ⬝ f_*[C]) = -deg(c₁(ω_X) ∩ f_*[C])`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private def lineBundlePullbackIso {k : Type*} [Field k] {V W : Variety k}
    (g : V.toScheme ⟶ W.toScheme) {L M : LineBundle W}
    (e : L ≅ M) : LineBundle.pullback g L ≅ LineBundle.pullback g M :=
  lineBundleIsoOfModulesIso ((AlgebraicGeometry.Scheme.Modules.pullback g).mapIso
    (modulesIsoOfLineBundleIso e))

/-- The degree identity for a Cartier divisor `K` with `O_X(K) ≅ ω_X`: `(-K) · f_*[C] = deg f^*T_X`.
Proof: by the projection formula, `(-K) · f_*[C] = deg (f^*O(-K))`; moreover
`det f^*T_X ≅ f^*det T_X ≅ f^*O(-K)` (`det_tangentBundle_iso`) and `deg E = deg det E`. -/
theorem degree_identity_of_lineBundle_iso_canonicalBundle {k : Type*} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (C : SmoothProjectiveCurve k)
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (K : CartierDivisor X.toVariety) (hK : Nonempty (K.lineBundle ≅ canonicalBundle X)) :
    intersectionNumber X (-K) (curveCycleClassPushforward f)
      = VectorBundle.degree ((tangentBundle X).pullback f) := by
  letI hproper : AlgebraicGeometry.IsProper f := SmoothProjectiveCurve.isProper_of_isOver f
  change ChowGroup.degree X (capDivisor (-K) 0
    (curveCycleClassPushforward f)) = _
  let L : LineBundle C.toVariety :=
    LineBundle.pullback f ((-K).lineBundle)
  obtain ⟨D', hD'⟩ := LineBundle.exists_cartierDivisor C L
  obtain ⟨eD'⟩ := hD'
  let eMod : D'.lineBundle.toModules ≅ L.toModules :=
    { hom := eD'.hom.hom
      inv := eD'.inv.hom
      hom_inv_id := by
        have h := congrArg (fun q => q.hom) eD'.hom_inv_id
        change eD'.hom.hom ≫ eD'.inv.hom = 𝟙 D'.lineBundle.toModules at h
        exact h
      inv_hom_id := by
        have h := congrArg (fun q => q.hom) eD'.inv_hom_id
        change eD'.inv.hom ≫ eD'.hom.hom = 𝟙 L.toModules at h
        exact h }
  have hDmod : Nonempty (D'.lineBundle.toModules ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f).obj (-K).lineBundle.toModules) := by
    exact ⟨eMod⟩
  have hproj : chowPushforward f 0 (capDivisor D' 0 C.cycleClass) =
      capDivisor (-K) 0 (cyclePushforward f 1 C.cycleClass) := by
    exact projection_formula (X := C.toVariety) (Y := X.toVariety) f
      (-K) D' hDmod 0 C.cycleClass
  have hcycle : curveCycleClassPushforward f = cyclePushforward f 1 C.cycleClass := by
    rfl
  rw [hcycle, ← hproj]
  have hbase : f ≫ X.structureMorphism =
      C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    (inferInstance : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1
  let fC : C.toSmoothProjectiveVariety.toScheme ⟶ X.toScheme := f
  letI hproperC : AlgebraicGeometry.IsProper fC := by
    exact hproper
  let αC : ChowGroup C.toSmoothProjectiveVariety.toVariety 0 :=
    capDivisor D' 0 C.cycleClass
  have hdeg := ChowGroup.degree_chowPushforward (X := C.toSmoothProjectiveVariety)
    (Y := X) fC hbase αC
  have hdeg' : ChowGroup.degree X (chowPushforward f 0 (capDivisor D' 0 C.cycleClass)) =
      ChowGroup.degree C.toSmoothProjectiveVariety (capDivisor D' 0 C.cycleClass) := by
    change ChowGroup.degree X (chowPushforward f 0 (capDivisor D' 0 C.cycleClass)) =
      ChowGroup.degree C.toSmoothProjectiveVariety (capDivisor D' 0 C.cycleClass) at hdeg
    exact hdeg
  rw [hdeg']
  have hcurve := intersectionNumber_curve_eq_lineBundle_degree C D'
  have hcurve' : ChowGroup.degree C.toSmoothProjectiveVariety
      (capDivisor D' 0 C.cycleClass) = LineBundle.degree D'.lineBundle := by
    exact hcurve
  rw [hcurve']
  obtain ⟨eTX⟩ := det_tangentBundle_iso X K hK
  obtain ⟨eDet⟩ := AlgebraicGeometry.VectorBundle.det_pullback
    (X := C.toVariety) (Y := X.toVariety) f (tangentBundle X)
  let ePull := lineBundlePullbackIso (V := C.toVariety) (W := X.toVariety) f eTX
  let eDL : D'.lineBundle ≅
      (AlgebraicGeometry.VectorBundle.pullback f (tangentBundle X)).det :=
    eD' ≪≫ (eDet ≪≫ ePull).symm
  rw [VectorBundle.degree_eq_lineBundle_degree_det]
  exact LineBundle.degree_congr (modulesIsoOfLineBundleIso eDL)

/-- **The degree identity of the paper** (`d = -K_X · f_*[C] = deg f^*T_X`, §2): for every canonical
divisor `K` of `X` (`O_X(K) ≅ ω_X`), `-K · f_*[C] = deg f^*T_X`. -/
theorem degree_identity {k : Type*} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (C : SmoothProjectiveCurve k)
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (K : CartierDivisor X.toVariety) (hK : CartierDivisor.IsCanonical X K) :
    intersectionNumber X (-K) (curveCycleClassPushforward f)
      = VectorBundle.degree ((tangentBundle X).pullback f) :=
  degree_identity_of_lineBundle_iso_canonicalBundle X C f K hK

/-- The same identity with the canonical bundle `ω_X`:
`-(canonicalBundle X ⬝ f_*[C]) = deg f^*T_X`, where `canonicalBundle X ⬝ Z = deg(c₁(ω_X) ∩ Z)`.
Proof: pick any `K` with `O(K) ≅ ω_X` (`exists_cartierDivisor_lineBundle_iso_canonicalBundle`),
`-(ω_X ⬝ Z) = (-K) · Z`, then the divisor form. -/
theorem degree_identity_canonicalBundle {k : Type*} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (C : SmoothProjectiveCurve k)
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    -(canonicalBundle X ⬝ curveCycleClassPushforward f)
      = VectorBundle.degree ((tangentBundle X).pullback f) := by
  obtain ⟨K, hK, -⟩ := exists_cartierDivisor_lineBundle_iso_canonicalBundle X
  rw [← intersectionNumber_neg_of_lineBundle_iso_canonicalBundle X K hK]
  exact degree_identity_of_lineBundle_iso_canonicalBundle X C f K hK

end
