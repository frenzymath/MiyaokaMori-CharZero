import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambda
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite

/-! # Finite type and constant rank of a locally free family over `X × A¹`

Let `X` be a connected `k`-scheme and `𝒱` a locally free sheaf on `X × A¹` (Mathlib's `IsLocallyFree`
does not bound the rank). If for some `t ∈ k` the restriction `𝒱|_{λ=t}` is isomorphic to a locally
free sheaf `E` of finite type and constant rank `ρ`, then `𝒱` is of finite type and has rank `ρ` at
every point of `X × A¹`.

Proof sketch:
1. `X × A¹` is connected: Mathlib has `GeometricallyIrreducible (𝔸(n; S) ↘ S)` and
   `AffineSpace.isOpenMap_over`; geometrically irreducible ⇒ geometrically connected (irreducible
   fibres are connected), then `GeometricallyConnected.connectedSpace` (a geometrically connected open
   map over a connected base has connected source).
2. Let `Q(y)` := "`y` has an open neighbourhood `U` and a finite index type `I` with `|I| = ρ` and
   `(U.ι)^*𝒱 ≅ O_U^{(I)}`". `Q` is locally constant: take any trivialization `(U, I)` at `y`; for
   `z ∈ U`, `Q(z) ⇔ (I finite and |I| = ρ)`. (⇐) use `(U, I)`. (⇒) if `(U', I')` is a finite
   trivialization of rank `ρ` at `z`, then on `W = U ⊓ U'`, `O_W^{(I')} ≅ 𝒱|_W ≅ O_W^{(I)}`; at the
   stalk of `z`, `I` linearly independent elements in a finitely generated free module force `I`
   finite (`finite_of_epi_of_iso_free`), and `rankAtStalk_of_restrict_iso_free` twice gives
   `|I| = rk_z 𝒱 = |I'| = ρ`.
3. `Q` holds on the section `λ = t`: for `x ∈ X` and `y = sectionAt t x`, take a trivialization `(U, I)`
   at `y`, `V = sectionAt⁻¹ U ∋ x`, `g = resLE : V → U` with `g ≫ U.ι = V.ι ≫ sectionAt`. The
   compatibilities of pullback with composition and with equal morphisms (`pullbackComp`,
   `pullbackCongr`) give `(V.ι)^*E ≅ (V.ι)^*(sectionAt^*𝒱) ≅ g^*((U.ι)^*𝒱) ≅ g^*O^{(I)} ≅ O_V^{(I)}`;
   `E` of finite type ⇒ `I` finite (`finite_index_of_restrict_iso_free`), and `|I| = rk_x E = ρ`.
4. `X` connected is nonempty; take `x₀`. `A¹_X` connected and `Q` locally constant ⇒ `Q` holds
   everywhere (`IsLocallyConstant.apply_eq_of_preconnectedSpace`). Hence every point has an
   epimorphism from a finite free sheaf (finite type, `isFiniteType_of_epi_free_pullback`) and
   `rankAtStalk 𝒱 y = |I| = ρ`.

Used for the deformation to the split weighted bundle (§2 of the paper), where the family of the
fibres is only known to be locally free.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- A geometrically irreducible morphism is geometrically connected (every geometric fibre is
irreducible, hence connected). -/
theorem AlgebraicGeometry.GeometricallyConnected.of_geometricallyIrreducible
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.GeometricallyIrreducible f] :
    AlgebraicGeometry.GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have : IrreducibleSpace Z :=
    AlgebraicGeometry.GeometricallyIrreducible.geometrically_irreducibleSpace (f := f) y fst snd h
  infer_instance

/-- The affine line `A¹_X` over a connected scheme is connected. -/
theorem AlgebraicGeometry.Scheme.affineLineOver.connectedSpace (X : AlgebraicGeometry.Scheme.{u})
    [ConnectedSpace X] : ConnectedSpace (AlgebraicGeometry.Scheme.affineLineOver X) := by
  have hgc : GeometricallyConnected (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) :=
    GeometricallyConnected.of_geometricallyIrreducible _
  exact @GeometricallyConnected.connectedSpace _ _ (AffineSpace (ULift.{u} (Fin 1)) X ↘ X) hgc _
    (AffineSpace.isOpenMap_over X)

/-- Two trivializations at the same point: if one index type is finite, so is the other. -/
theorem AlgebraicGeometry.Scheme.Modules.finite_of_two_pullback_iso_free {Y : AlgebraicGeometry.Scheme.{u}}
    (M : Y.Modules) {U U' : Y.Opens} (I I' : Type u) [Finite I']
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (e' : (AlgebraicGeometry.Scheme.Modules.pullback U'.ι).obj M ≅
      SheafOfModules.free (R := U'.toScheme.ringCatSheaf) I')
    (y : Y) (hy : y ∈ U) (hy' : y ∈ U') : Finite I := by
  obtain ⟨eW⟩ := Scheme.Modules.pullback_iso_free_of_le M (inf_le_left : U ⊓ U' ≤ U) I e
  obtain ⟨eW'⟩ := Scheme.Modules.pullback_iso_free_of_le M (inf_le_right : U ⊓ U' ≤ U') I' e'
  have : Epi eW'.inv := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv eW')
  exact MiyaokaMori.FreeStalk.finite_of_epi_of_iso_free (Y := (U ⊓ U').toScheme) ⟨y, ⟨hy, hy'⟩⟩
    I' _ eW'.inv I eW

/-- There is a finite trivialization of rank `ρ` at the point `y`. -/
def AlgebraicGeometry.Scheme.Modules.HasFiniteTrivializationOfRank {Y : AlgebraicGeometry.Scheme.{u}}
    (M : Y.Modules) (ρ : ℕ) (y : Y) : Prop :=
  ∃ (U : Y.Opens) (I : Type u) (_ : Fintype I), y ∈ U ∧ Fintype.card I = ρ ∧
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)

/-- For a locally free sheaf, "there is a finite trivialization of rank `ρ`" is locally constant. -/
theorem AlgebraicGeometry.Scheme.Modules.isLocallyConstant_hasFiniteTrivializationOfRank
    {Y : AlgebraicGeometry.Scheme.{u}} (M : Y.Modules) [M.IsLocallyFree] (ρ : ℕ) :
    IsLocallyConstant (fun y : Y => AlgebraicGeometry.Scheme.Modules.HasFiniteTrivializationOfRank M ρ y) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y
  obtain ⟨U, I, hyU, ⟨e⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree M y
  have key : ∀ z ∈ U, Scheme.Modules.HasFiniteTrivializationOfRank M ρ z ↔
      ∃ _ : Fintype I, Fintype.card I = ρ := by
    intro z hz
    constructor
    · rintro ⟨U', I', hI', hzU', hcard, ⟨e'⟩⟩
      have : Finite I := Scheme.Modules.finite_of_two_pullback_iso_free M I I' e e' z hz hzU'
      let _ := Fintype.ofFinite I
      refine ⟨inferInstance, ?_⟩
      rw [← Scheme.Modules.rankAtStalk_of_restrict_iso_free M U I e z hz,
        Scheme.Modules.rankAtStalk_of_restrict_iso_free M U' I' e' z hzU', hcard]
    · rintro ⟨hI, hcard⟩
      exact ⟨U, I, hI, hz, hcard, ⟨e⟩⟩
  refine ⟨U, U.isOpen, hyU, fun z hz => ?_⟩
  exact propext ((key z hz).trans (key y hyU).symm)

/-- Points on the section `λ = t` have a finite trivialization of rank `ρ`: pull the trivialization at
`y = sectionAt t x` back to `X` along the section and compare with `E`. -/
theorem AlgebraicGeometry.Scheme.Modules.hasFiniteTrivializationOfRank_sectionAt
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (𝒱 : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) [𝒱.IsLocallyFree] (t : k)
    (E : X.Modules) [E.IsFiniteType] {ρ : ℕ}
    (hE : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = ρ)
    (e : SheafOfModules.restrictToLambda 𝒱 t ≅ E) (x : X) :
    AlgebraicGeometry.Scheme.Modules.HasFiniteTrivializationOfRank 𝒱 ρ
      ((AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).base x) := by
  set s := Scheme.affineLineOver.sectionAt X t with hs
  obtain ⟨U, I, hyU, ⟨eU⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree 𝒱 (s.base x)
  let V : X.Opens := s ⁻¹ᵁ U
  have hxV : x ∈ V := hyU
  let g : V.toScheme ⟶ U.toScheme := s.resLE U V le_rfl
  have hg : g ≫ U.ι = V.ι ≫ s := Scheme.Hom.resLE_comp_ι s le_rfl
  let eV : (Scheme.Modules.pullback V.ι).obj E ≅ SheafOfModules.free (R := V.toScheme.ringCatSheaf) I :=
    (Scheme.Modules.pullback V.ι).mapIso e.symm ≪≫
    (Scheme.Modules.pullbackComp V.ι s).app 𝒱 ≪≫
    (Scheme.Modules.pullbackCongr hg.symm).app 𝒱 ≪≫
    ((Scheme.Modules.pullbackComp g U.ι).app 𝒱).symm ≪≫
    (Scheme.Modules.pullback g).mapIso eU ≪≫
    Scheme.Modules.pullbackObjFreeIso g I
  have : Finite I := Scheme.Modules.finite_index_of_restrict_iso_free E V I eV x hxV
  let _ := Fintype.ofFinite I
  refine ⟨U, I, inferInstance, hyU, ?_, ⟨eU⟩⟩
  rw [← Scheme.Modules.rankAtStalk_of_restrict_iso_free E V I eV x hxV, hE x]

theorem AlgebraicGeometry.Scheme.Modules.isFiniteType_and_rank_of_restrictToLambda
    {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [ConnectedSpace X]
    (𝒱 : (AlgebraicGeometry.Scheme.affineLineOver X).Modules) [𝒱.IsLocallyFree] (t : k)
    (E : X.Modules) [E.IsLocallyFree] [E.IsFiniteType] {ρ : ℕ}
    (hE : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = ρ)
    (e : Nonempty (SheafOfModules.restrictToLambda 𝒱 t ≅ E)) :
    𝒱.IsFiniteType ∧ ∀ y : AlgebraicGeometry.Scheme.affineLineOver X,
      AlgebraicGeometry.Scheme.Modules.rankAtStalk 𝒱 y = ρ := by
  have : ConnectedSpace (Scheme.affineLineOver X) := Scheme.affineLineOver.connectedSpace X
  obtain ⟨e⟩ := e
  have hloc := Scheme.Modules.isLocallyConstant_hasFiniteTrivializationOfRank 𝒱 ρ
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hall : ∀ y, Scheme.Modules.HasFiniteTrivializationOfRank 𝒱 ρ y := by
    intro y
    have h0 := Scheme.Modules.hasFiniteTrivializationOfRank_sectionAt 𝒱 t E hE e x₀
    exact Eq.mpr (hloc.apply_eq_of_preconnectedSpace y _) h0
  refine ⟨?_, ?_⟩
  · refine Scheme.Modules.isFiniteType_of_epi_free_pullback 𝒱 fun y => ?_
    obtain ⟨U, I, hI, hyU, hcard, ⟨eU⟩⟩ := hall y
    exact ⟨U, I, inferInstance, eU.inv, hyU, @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv eU)⟩
  · intro y
    obtain ⟨U, I, hI, hyU, hcard, ⟨eU⟩⟩ := hall y
    rw [Scheme.Modules.rankAtStalk_of_restrict_iso_free 𝒱 U I eU y hyU, hcard]

end
