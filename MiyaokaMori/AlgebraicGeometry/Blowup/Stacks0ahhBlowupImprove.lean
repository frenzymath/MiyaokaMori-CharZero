import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0ahhLengthSum
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agt
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupExceptionalInvertible
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0ahhBlowupImproveAssembly
import MiyaokaMori.AlgebraicGeometry.Blowup.PointBlowupLocalModel
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks0ahhBlowupImproveAway
import MiyaokaMori.RingTheory.Length.Stacks0ahhBlowupImproveArtinianPow

/-! # Stacks 0AGT globalized to a smooth projective surface

Globalization of Stacks 0AGT to a smooth projective surface: blowing up a closed point `x` of the
support of an ideal sheaf `I` with finite support factors `I·O_{W'}` as (effective Cartier divisor)
× (ideal sheaf `I'` with finite support lying over the support of `I`), and strictly decreases the
length sum. This is the induction step of Stacks 0AHH (`exists_pointBlowupTower_invertible`).

Source: Stacks 0AHH proof (second paragraph) + Stacks 0AGT + Stacks 0805 (blowup commutes with
flat base change) + Stacks 02OS/0807 (blowup is an isomorphism away from the centre).

The concrete inputs of `exists_pointBlowup_improve` are: Stacks 0AGT
(`blowup_regularLocalRing_dimTwo_improve`, on `A = O_{W,x}`), the local model
`pointBlowup.exists_localModel` (Stacks 0805 + flat preimmersions are stalk isomorphisms),
`comap_fromSpecStalk`, `blowup_exceptional_isInvertibleIdeal`, the stalk consequences of
`pointBlowup_isIso_away` and `𝔪ⁿ ⊆ I_x` from finite length
(`IsLocalRing.exists_maximalIdeal_pow_le_of_length_ne_top`); the bookkeeping of steps 4–6 is the
variable-level `exists_improve_of_localModel`, which uses the division of an ideal sheaf by an
invertible one (`exists_eq_mul_of_le_of_isInvertibleIdeal`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 0AGT, globalized** (Stacks 0AHH, induction step). Let `W` be a smooth projective
surface, `I` an ideal sheaf with finite support `T` and finite length sum (`lengthSum`), and
`x ∈ T` a closed point with `I_x ≠ O_{W,x}`. Let `π : W' = Bl_x W → W`. Then there are an
effective Cartier divisor `D` on `W'` and an ideal sheaf `I'` on `W'` such that
`I·O_{W'} = I_D · I'`, the support of `I'` is finite and maps into `T`, and the length sum of
`I'` over its support is strictly smaller than that of `I` over `T`.

**Proof.**
Write `A := O_{W,x}`, a two-dimensional regular local ring (`SmoothProjectiveSurface.stalk_regular_dim_two`),
`𝔪` its maximal ideal, `J := I_x ⊆ 𝔪` (`hxI`; the stalk
is local). Since `length_A(A/J) < ∞` (`hfin`, `length_ne_top_of_lengthSum_ne_top`), `A/J` is Artinian,
so `𝔪ⁿ ⊆ J` for some `n` (`IsLocalRing.exists_maximalIdeal_pow_le_of_length_ne_top`).

1. **Local model.** Let `g : Spec A → W` be the canonical flat morphism from the stalk
   (`Scheme.fromSpecStalk`, flat: `AlgebraicGeometry.Scheme.flat_fromSpecStalk`). The blowup of `W`
   along the vanishing ideal of `{x}` pulls back under `g` to the blowup `X := Bl_{J₀} Spec A`,
   `J₀ = (vanishingIdeal {x}).comap g = ofIdealTop 𝔪` (Stacks 0805,
   `blowup_flatBaseChange`; `pointBlowup.vanishingIdeal_comap_fromSpecStalk`). The projection
   `q : X → W'` satisfies `q ≫ π = b ≫ g`, hits every point of `π⁻¹(x)`, and is an isomorphism on
   stalks (flat preimmersion; `pointBlowup.exists_localModel`).
   Moreover `I·O_X = (I·O_{W'})·O_X` and `E·O_X = 𝔪·O_X` (`comap_comp`, `comap_fromSpecStalk`).
2. **Apply Stacks 0AGT** (`AlgebraicGeometry.blowup_regularLocalRing_dimTwo_improve`)
   to `(A, J, n)`: there are `d > 0` and an ideal sheaf `I'_X` on `X` with `J·O_X = E^d · I'_X` on every
   affine open, the support of `I'_X` is a finite set `T_X` of closed points of `X`, and
   `Σ_{y ∈ T_X} length(O_{X,y}/I'_{X,y}) < length_A(A/J)`.
3. **Exceptional divisor on `W'`.** `E := (vanishingIdeal {x}).comap π` is invertible
   (Stacks 02OS(2)/0806, `blowup_exceptional_isInvertibleIdeal`),
   with support `π⁻¹(x)`; so is `E^d` (`isInvertibleIdeal_pow`), and `D := (E^d, _)`.
4. **Define `I'` on `W'`.** `I·O_{W'} ≤ E^d` is checked on stalks (`le_of_forall_stalkIdeal_le`): off
   `π⁻¹(x)` the stalk of `E` is the unit ideal; on `π⁻¹(x)` transport the 0AGT equation along the
   stalk isomorphism of `q`. Divide (`exists_eq_mul_of_le_of_isInvertibleIdeal`):
   `I·O_{W'} = E^d · I'`. By cancellation on `X`
   (`eq_of_pow_mul_eq_pow_mul`, `comap_mul`) `I'_X = I'·O_X`.
5. **Support of `I'`.** `supp I' ⊆ supp(I·O_{W'}) = π⁻¹(T)` (`support_mul`, `support_comap`). Off
   `π⁻¹(x)`, `π` is injective (`pointBlowup.π_injOn`), so `supp I' ∖ π⁻¹(x)` injects into `T ∖ {x}`; on
   `π⁻¹(x)`, `supp I' ∩ π⁻¹(x) ⊆ q(T_X)` by the stalk isomorphism. Hence `supp I'` is finite.
6. **Length sum.** For `y ∈ supp I'` with `π y ≠ x`, `O_{W',y} ≅ O_{W,π y}` (`pointBlowup.isIso_stalkMap_π_of_ne`)
   carries `I'_y` to `I_{π y}` (`stalkIdeal_comap`, the stalk of `E^d` being trivial), so these terms are
   terms of `I` at `T ∖ {x}` (`Module.length_quotient_eq_of_bijective`, injectivity of `π`). For
   `y ∈ π⁻¹(x)`, choose `y' ∈ T_X` with `q y' = y`; `O_{W',y} ≅ O_{X,y'}` carries `I'_y` to `I'_{X,y'}`, so
   the sum of these terms is `≤ Σ_{T_X} < length_A(A/J)` (step 2). Adding the unchanged terms (finite
   by `hfin`) gives `I'.lengthSum T' < I.lengthSum T` (`exists_improve_of_localModel`).

Edge cases: `T = {x}` (then `supp I' ⊆ π⁻¹(x)`, fine); `d ≥ 1` is guaranteed by `J ⊆ 𝔪` (0AGT) but
is not needed for the conclusion. -/
theorem exists_pointBlowup_improve {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (I : W.toScheme.IdealSheafData)
    (hI : (I.support : Set W.toScheme).Finite) (hfin : I.lengthSum hI.toFinset ≠ ⊤)
    (x : W.toScheme) (hx : IsClosed ({x} : Set W.toScheme)) (hxI : I.stalkIdeal x ≠ ⊤) :
    ∃ (D : AlgebraicGeometry.EffectiveCartierDivisor (pointBlowup W x hx).toScheme)
      (I' : (pointBlowup W x hx).toScheme.IdealSheafData)
      (hI' : (I'.support : Set (pointBlowup W x hx).toScheme).Finite),
      I.comap (pointBlowup.π W x hx) = D.idealSheaf * I' ∧
      (∀ y ∈ I'.support, pointBlowup.π W x hx y ∈ I.support) ∧
      I'.lengthSum hI'.toFinset < I.lengthSum hI.toFinset := by
  classical
  have hx_mem : x ∈ I.support := (I.mem_support_iff_stalkIdeal_ne_top x).mpr hxI
  -- the local ring `A = O_{W,x}` and the hypotheses of 0AGT
  obtain ⟨hreg, hdim⟩ := W.stalk_regular_dim_two x hx
  have hIm : I.stalkIdeal x ≤ IsLocalRing.maximalIdeal (W.toScheme.presheaf.stalk x) :=
    IsLocalRing.le_maximalIdeal hxI
  have hlen : Module.length (W.toScheme.presheaf.stalk x)
      (W.toScheme.presheaf.stalk x ⧸ I.stalkIdeal x) ≠ ⊤ :=
    I.length_ne_top_of_lengthSum_ne_top hI.toFinset hfin (hI.mem_toFinset.mpr hx_mem)
  obtain ⟨n, hmI⟩ := IsLocalRing.exists_maximalIdeal_pow_le_of_length_ne_top (I.stalkIdeal x) hlen
  -- Stacks 0AGT on `Bl_𝔪 Spec A`
  obtain ⟨d, I'X, -, hprod, -, TX, hTX, -, hsumX⟩ :=
    AlgebraicGeometry.blowup_regularLocalRing_dimTwo_improve (W.toScheme.presheaf.stalk x) hdim
      (I.stalkIdeal x) n hmI hIm
  -- the local model `q : X → W'`
  obtain ⟨q, -, hIq, hVq, hq⟩ := pointBlowup.exists_localModel W x hx _
    (pointBlowup.vanishingIdeal_comap_fromSpecStalk_of W x hx).symm
  -- the exceptional ideal `E`
  obtain ⟨E, hEdef⟩ : ∃ E : (pointBlowup W x hx).toScheme.IdealSheafData,
      E = (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap
        (pointBlowup.π W x hx) := ⟨_, rfl⟩
  have hE : MiyaokaMori.Statement.IsInvertibleIdeal E := by
    rw [hEdef]
    exact AlgebraicGeometry.Scheme.blowup_exceptional_isInvertibleIdeal
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)
  have hEsupp : (E.support : Set (pointBlowup W x hx).toScheme) = pointBlowup.π W x hx ⁻¹' {x} := by
    rw [hEdef, AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    show pointBlowup.π W x hx ⁻¹' ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
      ⟨{x}, hx⟩).support : Set W.toScheme) = _
    rw [AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hEcq : E.comap q = _ :=
    (congrArg (fun K : (pointBlowup W x hx).toScheme.IdealSheafData => K.comap q) hEdef).trans hVq
  have hEq : MiyaokaMori.Statement.IsInvertibleIdeal (E.comap q) := by
    rw [hEcq]
    exact AlgebraicGeometry.Scheme.blowup_exceptional_isInvertibleIdeal _
  -- the 0AGT equation in terms of `q`
  have hprod' : ∀ U, ((I.comap (pointBlowup.π W x hx)).comap q).ideal U =
      (E.comap q).ideal U ^ d * I'X.ideal U := by
    intro U
    have hL := congrArg (fun K : (AlgebraicGeometry.Scheme.blowup _).left.IdealSheafData => K.ideal U) (hIq I)
    have hR := congrArg (fun K : (AlgebraicGeometry.Scheme.blowup _).left.IdealSheafData => K.ideal U) hEcq
    exact hL.trans ((hprod U).trans (congrArg (fun A => A ^ d * I'X.ideal U) hR.symm))
  have : AlgebraicGeometry.IsLocallyNoetherian (pointBlowup W x hx).toScheme :=
    Variety.isLocallyNoetherian (pointBlowup W x hx).toSmoothProjectiveVariety.toVariety
  exact AlgebraicGeometry.Scheme.IdealSheafData.exists_improve_of_localModel (pointBlowup.π W x hx) x
    I hI hfin hx_mem E hE hEsupp (pointBlowup.isIso_stalkMap_π_of_ne W x hx)
    (pointBlowup.π_injOn W x hx) q hq hEq d I'X hprod' TX hTX hsumX

end
