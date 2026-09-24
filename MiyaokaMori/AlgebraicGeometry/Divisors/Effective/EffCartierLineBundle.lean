import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffCartier
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOps
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.LocalDivisibility

/-! # The ideal sheaf and `O_X(D)` of an effective Cartier divisor are line bundles

For an effective Cartier divisor `D`, both the ideal sheaf `I_D` (as a module sheaf) and
`O_X(D) = I_D^∨` are line bundles; `D.lineBundle : X.LineBundle` is the packaged version.
"`I_D` is a line bundle" is a theorem here: on the affine open `V` of a local equation `a`, take
`x ∈ Γ(V, I_D)` with `ι(x) = a`; then `x` is a frame of `I_D` on `V` (`exists_frame_ideal`).
Surjectivity uses `IsAffineOpen.dvd_of_locally_dvd` (divisibility by a nonzerodivisor is local).
The canonical presentation is in `EffCartierCanonical`. Sources: Stacks 01WQ, 01WT, 01WX.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.EffCartier

variable {X : Scheme.{u}}

/-- `I_D` has a frame near every point.
Proof: take a local equation `(V, a)` (`exists_localEquation`) and `x ∈ Γ(V, I_D)` with `ι(x) = a`
(`range_idealIota`). For `W' ≤ V`: (injectivity) `r • x|_{W'} = 0` gives `r·a|_{W'} = 0`
(`idealIota_map` and linearity of `ι`), hence `r = 0` (`IsAffineOpen.res_mem_nonZeroDivisors`);
(surjectivity) given `y ∈ Γ(W', I_D)`, on every basic open `D(f) ≤ W'` of `V` we have
`I_D(D(f)) = (a|_{D(f)})` (`IdealSheafData.map_ideal_basicOpen`), so `ι(y)|_{D(f)} = r_f·a|` with `r_f`
unique by the nonzerodivisor property, hence compatible on overlaps; glue to `r ∈ Γ(X, W')` by the
sheaf property of `O_X`, and conclude `y = r • x|_{W'}` from injectivity of `ι` (`idealIota_injective`)
and the sheaf property of `I_D`. -/
theorem exists_frame_ideal (D : X.EffCartier) (p : X) :
    ∃ (W : X.Opens) (_ : p ∈ W) (e : Γ(D.ideal.toModules, W)),
      Modules.IsFrame D.ideal.toModules W e := by
  obtain ⟨V, hpV, a, ha, hI⟩ := D.exists_localEquation p
  obtain ⟨x, hx⟩ : ∃ x : Γ(D.ideal.toModules, V.1), idealIota D.ideal V.1 x = a := by
    have : a ∈ Set.range (idealIota D.ideal V.1) := by
      rw [range_idealIota, hI]; exact Ideal.subset_span rfl
    exact this
  have hiota : ∀ {W' : X.Opens} (h : W' ≤ V.1),
      idealIota D.ideal W' (D.ideal.toModules.res h x) = X.presheaf.map (homOfLE h).op a := by
    intro W' h
    rw [← hx]
    exact idealIota_map D.ideal (homOfLE h) x
  refine ⟨V.1, hpV, x, fun W' h ↦ ⟨?_, ?_⟩⟩
  · intro r r' hrr
    have hrr' : r • D.ideal.toModules.res h x = r' • D.ideal.toModules.res h x := hrr
    have h1 := congrArg (idealIota D.ideal W') hrr'
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, hiota h] at h1
    have hnzd := V.2.res_mem_nonZeroDivisors ha h
    have h2 : (r - r') * X.presheaf.map (homOfLE h).op a = 0 := by rw [sub_mul, h1, sub_self]
    exact sub_eq_zero.mp (mem_nonZeroDivisors_iff_right.mp hnzd _ h2)
  · intro y
    have hb : X.presheaf.map (homOfLE h).op a ∣ idealIota D.ideal W' y := by
      refine V.2.dvd_of_locally_dvd ha h _ fun q ↦ ?_
      obtain ⟨f, hfW, hqf⟩ := V.2.exists_basicOpen_le q (h q.2)
      have hBW : (X.affineBasicOpen f).1 ≤ W' := hfW
      refine ⟨(X.affineBasicOpen f).1, hBW, hqf, ?_⟩
      have hmem : idealIota D.ideal (X.affineBasicOpen f).1 (D.ideal.toModules.res hBW y) ∈
          D.ideal.ideal (X.affineBasicOpen f) := by
        have hrange : idealIota D.ideal (X.affineBasicOpen f).1 (D.ideal.toModules.res hBW y) ∈
            Set.range (idealIota D.ideal (X.affineBasicOpen f).1) := ⟨_, rfl⟩
        rw [range_idealIota] at hrange
        exact hrange
      rw [← D.ideal.map_ideal_basicOpen V f, hI, Ideal.map_span, Set.image_singleton] at hmem
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hmem
      exact ⟨c, (idealIota_map D.ideal (homOfLE hBW) y).symm.trans hc⟩
    obtain ⟨r, hr⟩ := hb
    refine ⟨r, idealIota_injective D.ideal W' ?_⟩
    show idealIota D.ideal W' (r • D.ideal.toModules.res h x) = idealIota D.ideal W' y
    rw [map_smul, smul_eq_mul, hiota h, hr, mul_comm]

/-- `I_D` is a line bundle (Stacks 01WQ). -/
instance ideal_isLineBundle (D : X.EffCartier) : D.ideal.toModules.IsLineBundle :=
  (Modules.isLineBundle_iff_exists_frame _).mpr D.exists_frame_ideal

/-- `O_X(D)` is a line bundle. -/
instance sheaf_isLineBundle (D : X.EffCartier) : D.sheaf.IsLineBundle :=
  Modules.dualSheaf_isLineBundle _

/-- The packaged line bundle `O_X(D)`. -/
def lineBundle (D : X.EffCartier) : X.LineBundle := .ofModules D.sheaf

@[simp] theorem lineBundle_toModules (D : X.EffCartier) : D.lineBundle.toModules = D.sheaf := rfl

end AlgebraicGeometry.Scheme.EffCartier

end
