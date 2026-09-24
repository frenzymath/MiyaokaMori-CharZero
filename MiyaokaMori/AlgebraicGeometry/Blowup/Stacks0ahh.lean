import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerAvoiding
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks01wu
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0ahhLengthSum
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0ahhBlowupImprove
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0ahhTowerLemmas
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0ahhComapMul

/-! # Stacks 0AHH for surfaces: making an ideal sheaf with finite support invertible

Stacks 0AHH (surface case): for an ideal sheaf `I` with finite support on a smooth projective
surface `W`, after a sequence of blowups of closed points lying over `V(I)`, the pulled-back ideal
`I·O_{X_n}` becomes an invertible ideal sheaf (an effective Cartier divisor).

Source: Stacks 0AHH; second step of the proof of Stacks 0AHI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- In a Jacobson space every point of a finite closed set is closed: the subspace is a finite
Jacobson space, hence discrete (`JacobsonSpace.discreteTopology`), and the inclusion is a closed
embedding. (Stacks 0AHH, first line: "T is a finite set of closed points".) -/
theorem isClosed_singleton_of_mem_of_finite_of_isClosed {X : Type*} [TopologicalSpace X]
    [JacobsonSpace X] {T : Set X} (hT : IsClosed T) (hfin : T.Finite) {x : X} (hx : x ∈ T) :
    IsClosed ({x} : Set X) := by
  have : JacobsonSpace T := JacobsonSpace.of_isClosedEmbedding hT.isClosedEmbedding_subtypeVal
  have : Finite T := hfin.to_subtype
  have h : IsClosed ({⟨x, hx⟩} : Set T) := isClosed_discrete _
  have h2 := hT.isClosedEmbedding_subtypeVal.isClosedMap _ h
  simpa using h2

/-- Stacks 0AHH (surface case).

Source: Stacks 0AHH. The original is stated for finitely many two-dimensional regular closed points
of a Noetherian scheme; here it is specialized to a smooth projective surface (finite support ⇒ the
support consists of finitely many closed points, whose local rings are two-dimensional regular local
rings).

**Proof.**
1. The support `T := I.support` is finite (`hI`). `W` is a scheme of finite type over `k`, hence a
   Jacobson space, and every point of a finite closed set is closed
   (`isClosed_singleton_of_mem_of_finite_of_isClosed`, `LocallyOfFiniteType.jacobsonSpace`), so
   `T = {x_1, …, x_r}` is a finite set of closed points. Each `O_{W,x_i}` is a two-dimensional
   regular local ring.
2. Let `n_i := length_{O_{W,x_i}}(O_{W,x_i}/I_{x_i})` and `Σ_i n_i =: I.lengthSum hI.toFinset`. It
   is finite (`lengthSum_ne_top`: the support points are closed, so `O_{W,x_i}/I_{x_i}` is a
   zero-dimensional Noetherian local ring, Hopkins–Levitzki). **Induct on `Σ_i n_i ∈ ℕ∞`** by
   well-founded induction (`WellFoundedLT.induction`).
3. Base case `Σ n_i = 0`: at every `x ∈ T` the stalk ideal `I_x` is the whole ring
   (`lengthSum_eq_zero_iff`), while the stalk ideal at a support point is proper
   (`stalkIdeal_ne_top_of_mem_support`), so `T = ∅` and `I = O_W` (`support_eq_bot_iff`).
   Take `S = W`, `β = 𝟙` (the tower of length `0`) and `D = 0` (ideal sheaf `O_W`,
   `EffCartier.zero_ideal`).
4. Induction step: `T ≠ ∅`; pick `x ∈ T` (a closed point with `I_x ≠ O_{W,x}`). Let
   `W' = Bl_x W = pointBlowup W x hx` and `β₁ = pointBlowup.π W x hx`.
5. By the globalization `exists_pointBlowup_improve` of Stacks 0AGT there are an effective Cartier
   divisor `D₁` and an ideal sheaf `I'` on `W'` with `I·O_{W'} = I_{D₁}·I'`, the support `T'` of
   `I'` finite with `β₁(T') ⊆ T`, and the sum of lengths strictly smaller.
6. Apply the induction hypothesis to `(W', I')`: there is a tower of point blowups `β₂ : S → W'`
   with centres over `T'` such that `I'·O_S = I_{D₂}`. The pullback of `D₁` along the tower `β₂` is
   again an effective Cartier divisor `D₁'` (`IsBlowupTower.exists_effectiveCartierDivisor_comap`,
   Stacks 0809 step by step); let `D := D₁' + D₂` (Stacks 01WU). Then
   `I·O_S = (I·O_{W'})·O_S = (I_{D₁}·I')·O_S = I_{D₁'}·I_{D₂} = I_D`
   (`comap_comp`, `comap_mul`).
7. The tower `β := β₂ ≫ β₁` is a tower of point blowups (`IsBlowupTower.comp`) with all centres
   over `T` (`IsBlowupTowerAvoiding.comp_pointBlowup_π`: the centre `x` of `β₁` lies in `T`, the
   centres of `β₂` lie over `T'` and `β₁(T') ⊆ T`). -/
theorem exists_pointBlowupTower_invertible {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (I : W.toScheme.IdealSheafData)
    (hI : (I.support : Set W.toScheme).Finite) :
    ∃ (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ W.toScheme),
      IsBlowupTower β ∧ IsBlowupTowerAvoiding β ((I.support : Set W.toScheme)ᶜ) ∧
      ∃ D : AlgebraicGeometry.EffectiveCartierDivisor S.toScheme, D.idealSheaf = I.comap β := by
  suffices key : ∀ (n : ℕ∞) (W : SmoothProjectiveSurface k) (I : W.toScheme.IdealSheafData)
      (hI : (I.support : Set W.toScheme).Finite), I.lengthSum hI.toFinset = n →
      ∃ (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ W.toScheme),
        IsBlowupTower β ∧ IsBlowupTowerAvoiding β ((I.support : Set W.toScheme)ᶜ) ∧
        ∃ D : AlgebraicGeometry.EffectiveCartierDivisor S.toScheme, D.idealSheaf = I.comap β from
    key _ W I hI rfl
  intro n
  induction n using WellFoundedLT.induction with
  | ind n ih =>
  intro W I hI hn
  have hsub : (I.support : Set W.toScheme) ⊆ hI.toFinset := fun y hy => hI.mem_toFinset.mpr hy
  by_cases h0 : I.lengthSum hI.toFinset = 0
  · -- base case: `I = O_W`
    have hItop : I = ⊤ := I.eq_top_of_lengthSum_eq_zero hI.toFinset hsub h0
    refine ⟨W, 𝟙 _, IsBlowupTower.id W, ?_, 0, ?_⟩
    · unfold IsBlowupTowerAvoiding
      exact MiyaokaMori.Statement.IsPointBlowupSequenceOver.id
    · rw [hItop, AlgebraicGeometry.Scheme.IdealSheafData.comap_top]
      rfl
  · -- induction step
    have hne : (I.support : Set W.toScheme).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      apply h0
      rw [AlgebraicGeometry.Scheme.IdealSheafData.lengthSum_eq_zero_iff]
      intro y hy
      have : y ∈ (I.support : Set W.toScheme) := hI.mem_toFinset.mp hy
      rw [hemp] at this
      exact this.elim
    have : JacobsonSpace W.toScheme :=
      AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
        (W.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    have hclosed : ∀ y ∈ hI.toFinset, IsClosed ({y} : Set W.toScheme) := fun y hy =>
      isClosed_singleton_of_mem_of_finite_of_isClosed I.support.isClosed hI (hI.mem_toFinset.mp hy)
    have hfin : I.lengthSum hI.toFinset ≠ ⊤ := I.lengthSum_ne_top hI.toFinset hclosed hsub
    obtain ⟨x, hx⟩ := hne
    have hxc : IsClosed ({x} : Set W.toScheme) := hclosed x (hI.mem_toFinset.mpr hx)
    have hxI : I.stalkIdeal x ≠ ⊤ := I.stalkIdeal_ne_top_of_mem_support x hx
    obtain ⟨D₁, I', hI', hfac, hover, hlt⟩ := exists_pointBlowup_improve W I hI hfin x hxc hxI
    rw [hn] at hlt
    obtain ⟨S, β₂, hβ₂, havoid₂, D₂, hD₂⟩ := ih _ hlt (pointBlowup W x hxc) I' hI' rfl
    refine ⟨S, β₂ ≫ pointBlowup.π W x hxc, hβ₂.comp (pointBlowup.π_isBlowupTower W x hxc), ?_, ?_⟩
    · refine havoid₂.comp_pointBlowup_π x hxc (by simpa using hx) ?_
      intro a ha
      simp only [Set.mem_compl_iff, not_not] at ha ⊢
      exact hover a ha
    · obtain ⟨D₁', hD₁'⟩ := hβ₂.exists_effectiveCartierDivisor_comap D₁
      obtain ⟨D, hD⟩ := AlgebraicGeometry.EffectiveCartierDivisor.exists_add D₁' D₂
      refine ⟨D, ?_⟩
      have hDeq : D.idealSheaf = D₁'.idealSheaf * D₂.idealSheaf := by
        refine AlgebraicGeometry.Scheme.IdealSheafData.ext (funext fun U => ?_)
        rw [AlgebraicGeometry.Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
        exact hD U
      rw [hDeq, hD₁', hD₂, AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hfac,
        AlgebraicGeometry.Scheme.IdealSheafData.comap_mul]

end
