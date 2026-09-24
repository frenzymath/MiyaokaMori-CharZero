import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ExtensionLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAdditiveShortExact
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyTrivialFinite
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Abelian.CommSq

/-! # Extending a subbundle filtration by a line bundle

Given a short exact sequence `0 → L → E → Q → 0` on a smooth projective curve with `L` a line
bundle, if `Q` has a subbundle filtration with line bundle quotients and `rank E = rank Q + 1`, then
`E` has a subbundle filtration with line bundle quotients.

Proof sketch:
1. Let `p : E ⟶ Q` be the cokernel morphism of `L ⟶ E` composed with the given isomorphism. For each
   step `Q_j ⟶ Q` of the filtration of `Q` take the categorical pullback `E_j := E ×_Q Q_j`. The zero
   object is step `0`, `L` is step `1`, and the remaining steps are these preimages.
2. In an abelian category the pullback of an epimorphism is an epimorphism and kernels are preserved
   under pullback, so each step has a short exact sequence `0 → L → E_{j+1} → Q_j → 0`.
   `isLocallyFree_of_shortExact` and `rankAtStalk_add_of_shortExact` give that `E_{j+1}` is locally
   free of rank `j+1`.
3. Two adjacent pullback squares induce `cokernel (E_j ⟶ E_{j+1}) ⟶ cokernel (Q_{j-1} ⟶ Q_j)`; the
   pullback square makes it a monomorphism and the two vertical epimorphisms make it an epimorphism,
   so it is an isomorphism in the abelian category. Compose with the line bundle quotient
   isomorphisms of the filtration of `Q`.
4. The last step is the pullback along the identity of `Q`, hence isomorphic to `E`; assembling the
   fields gives `SubbundleFiltration E (rank E)`.

The middle term is of finite type by `isFiniteType_of_shortExact` (the local splitting argument of
`isLocallyFree_of_shortExact`, with `finite_index_of_restrict_iso_free` for the finiteness of the
index set).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry ZeroObject

noncomputable section

namespace SubbundleFiltration.ExtendByLine

/-! ## Categorical part: pullback of a short exact sequence, cokernels of a pullback square -/

section Categorical

variable {𝒜 : Type v} [Category.{w} 𝒜] [Abelian 𝒜]

/-- The pullback `0 → X₁ → X₂ ×_{X₃} Y → Y → 0` of a short complex `X₁ → X₂ → X₃` along
`g : Y ⟶ X₃`. -/
abbrev pullbackShortComplex (S : ShortComplex 𝒜) {Y : 𝒜} (g : Y ⟶ S.X₃) : ShortComplex 𝒜 :=
  ShortComplex.mk (pullback.lift S.f 0 (by rw [S.zero, zero_comp])) (pullback.snd S.g g)
    (pullback.lift_snd _ _ _)

/-- Pulling back a short exact sequence along a map into its third term gives a short exact
sequence (in an abelian category, the pullback of an epimorphism is an epimorphism, and the
horizontal kernels of a pullback square agree). -/
theorem pullbackShortComplex_shortExact {S : ShortComplex 𝒜} (hS : S.ShortExact) {Y : 𝒜}
    (g : Y ⟶ S.X₃) : (pullbackShortComplex S g).ShortExact := by
  have := hS.mono_f
  have hmono : Mono (pullbackShortComplex S g).f :=
    mono_of_mono_fac (pullback.lift_fst S.f 0 (by rw [S.zero, zero_comp]))
  have hepi : Epi (pullbackShortComplex S g).g := by
    have := hS.epi_g
    exact Abelian.epi_pullback_of_epi_f _ _
  refine ShortComplex.ShortExact.mk' ?_ hmono hepi
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  have h1 : Epi (kernel.lift S.g S.f S.zero) :=
    (ShortComplex.exact_iff_epi_kernel_lift S).1 hS.exact
  have sq := (IsPullback.of_hasPullback S.g g).flip
  have h2 : IsIso (kernel.map (pullback.snd S.g g) S.g (pullback.fst S.g g) g sq.w) :=
    isIso_kernel_map_of_isPullback sq
  have h3 : kernel.lift (pullbackShortComplex S g).g (pullbackShortComplex S g).f
      (pullbackShortComplex S g).zero ≫
        kernel.map (pullback.snd S.g g) S.g (pullback.fst S.g g) g sq.w =
      kernel.lift S.g S.f S.zero := by
    ext
    simp
    exact pullback.lift_fst _ _ _
  rw [← IsIso.eq_comp_inv] at h3
  rw [h3]
  infer_instance

/-- In an abelian category, for a pullback square whose right vertical map is an epimorphism,
the induced map on the cokernels of the horizontal maps is an isomorphism. -/
theorem isIso_cokernel_map_of_isPullback_of_epi {X₁ X₂ X₃ X₄ : 𝒜} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃}
    {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄} (sq : IsPullback t l r b) [Epi r] :
    IsIso (cokernel.map t b l r sq.w) := by
  have : Mono (cokernel.map t b l r sq.w) := Abelian.mono_cokernel_map_of_isPullback sq
  have : Epi (cokernel.map t b l r sq.w) := by
    have h : cokernel.π t ≫ cokernel.map t b l r sq.w = r ≫ cokernel.π b :=
      cokernel.π_desc _ _ _
    exact epi_of_epi_fac h
  exact isIso_of_mono_of_epi _

end Categorical

/-! ## Sheaf part: the zero bundle and finite type of extensions -/

section Sheaf

open AlgebraicGeometry

/-- The free sheaf on the empty index type is a zero object. -/
theorem isZero_free_pempty (Y : Scheme.{u}) :
    IsZero (SheafOfModules.free (R := Y.ringCatSheaf) PEmpty.{u + 1}) :=
  (IsInitial.ofUniqueHom (fun M => M.freeHomEquiv.symm PEmpty.elim)
    (fun M _ => M.freeHomEquiv.injective (funext fun i => i.elim))).isZero

/-- The pullback of the zero module is a zero object. -/
theorem isZero_pullback_zero (X : Scheme.{u}) :
    IsZero ((Scheme.Modules.pullback (⊤ : X.Opens).ι).obj (0 : X.Modules)) :=
  Functor.map_isZero _ (isZero_zero _)

/-- The pullback of the zero module along `⊤.ι` is isomorphic to the free sheaf on `PEmpty`. -/
def pullbackZeroIsoFree (X : Scheme.{u}) :
    (Scheme.Modules.pullback (⊤ : X.Opens).ι).obj (0 : X.Modules) ≅
      SheafOfModules.free (R := (⊤ : X.Opens).toScheme.ringCatSheaf) PEmpty.{u + 1} :=
  IsZero.iso (isZero_pullback_zero X) (isZero_free_pempty _)

/-- The zero module is locally free. -/
theorem isLocallyFree_zero (X : Scheme.{u}) : (0 : X.Modules).IsLocallyFree :=
  Scheme.Modules.isLocallyFree_of_pullback_iso_free _ fun _ =>
    ⟨⊤, PEmpty.{u + 1}, trivial, ⟨pullbackZeroIsoFree X⟩⟩

/-- The zero module is of finite type. -/
theorem isFiniteType_zero (X : Scheme.{u}) : (0 : X.Modules).IsFiniteType :=
  Scheme.Modules.isFiniteType_of_epi_free_pullback _ fun _ =>
    ⟨⊤, PEmpty.{u + 1}, inferInstance, (isZero_pullback_zero X).from_ _, trivial,
      epi_of_target_iso_zero _ (isZero_pullback_zero X).isoZero⟩

/-- The zero module has rank `0` at every point. -/
theorem rankAtStalk_zero (X : Scheme.{u}) (x : X) :
    Scheme.Modules.rankAtStalk (0 : X.Modules) x = 0 := by
  have h := Scheme.Modules.rankAtStalk_of_restrict_iso_free (0 : X.Modules) ⊤ PEmpty.{u + 1}
    (pullbackZeroIsoFree X) x trivial
  simpa using h

set_option linter.style.haveILetI false in
/-- The middle term of a short exact sequence of locally free sheaves of finite type is of
finite type: locally the sequence splits, so the middle term is locally isomorphic to the free
sheaf on the (finite) disjoint union of the two index types. -/
theorem isFiniteType_of_shortExact {X : Scheme.{u}} {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsLocallyFree] [S.X₁.IsFiniteType] [S.X₃.IsLocallyFree]
    [S.X₃.IsFiniteType] : S.X₂.IsFiniteType := by
  refine (Scheme.Modules.isLocallyFree_and_isFiniteType_of_restrict_free_finite _ fun x => ?_).2
  obtain ⟨U, hxU, σ, hσ⟩ := Scheme.Modules.shortExact_locallySplit hS x
  obtain ⟨U₁, I₁, hx₁, ⟨e₁⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree S.X₁ x
  obtain ⟨U₃, I₃, hx₃, ⟨e₃⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree S.X₃ x
  let V : X.Opens := U ⊓ U₁ ⊓ U₃
  have hxV : x ∈ V := ⟨⟨hxU, hx₁⟩, hx₃⟩
  obtain ⟨σ', hσ'⟩ := extLF.section_of_le S.g (inf_le_left.trans inf_le_left : V ≤ U) σ hσ
  obtain ⟨e₁'⟩ := Scheme.Modules.pullback_iso_free_of_le S.X₁
    (inf_le_left.trans inf_le_right : V ≤ U₁) I₁ e₁
  obtain ⟨e₃'⟩ := Scheme.Modules.pullback_iso_free_of_le S.X₃ (inf_le_right : V ≤ U₃) I₃ e₃
  have : Finite I₁ := Scheme.Modules.finite_index_of_restrict_iso_free S.X₁ V I₁ e₁' x hxV
  have : Finite I₃ := Scheme.Modules.finite_index_of_restrict_iso_free S.X₃ V I₃ e₃' x hxV
  have hSV := Scheme.Modules.shortExact_map_pullback_of_isOpenImmersion V.ι hS
  have := hSV.mono_f
  let spl : (S.map (Scheme.Modules.pullback V.ι)).Splitting :=
    ShortComplex.Splitting.ofExactOfSection _ hSV.exact σ' hσ' hSV.mono_f
  let G : WalkingPair → V.toScheme.Modules :=
    pairFunction ((Scheme.Modules.pullback V.ι).obj S.X₁) ((Scheme.Modules.pullback V.ι).obj S.X₃)
  let e₂ : (Scheme.Modules.pullback V.ι).obj S.X₂ ≅ biproduct G :=
    spl.isoBinaryBiproduct ≪≫
      biproduct.uniqueUpToIso G
        ((BinaryBicone.toBiconeIsBilimit _).symm (BinaryBiproduct.isBilimit _ _))
  let I : WalkingPair → Type u := fun i => WalkingPair.casesOn i I₁ I₃
  haveI hI : ∀ i, Finite (I i) := fun i => match i with
    | WalkingPair.left => inferInstanceAs (Finite I₁)
    | WalkingPair.right => inferInstanceAs (Finite I₃)
  obtain ⟨e⟩ := Scheme.Modules.biproduct_iso_free G I
    (fun i => match i with
      | WalkingPair.left => e₁'
      | WalkingPair.right => e₃')
  haveI hfin : Finite (Σ i, I i) := by infer_instance
  exact ⟨V.toScheme, V.ι, inferInstance, Σ i, I i, hfin, ⟨⟨x, hxV⟩, rfl⟩,
    ⟨(Scheme.Modules.restrictFunctorIsoPullback V.ι).app S.X₂ ≪≫ e₂ ≪≫ e⟩⟩

end Sheaf

/-! ## Geometric part: the extended filtration -/

section Geometric

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
  {E Q : AlgebraicGeometry.VectorBundle C.toVariety} {L : LineBundle C.toVariety} {r : ℕ}

/-- The inclusion `Q_j ⟶ Q` of the `j`-th step of a filtration into the whole bundle. -/
def toTop (F : SubbundleFiltration Q r) : ∀ j : Fin (r + 1), (F.sub j).toModules ⟶ Q.toModules :=
  Fin.reverseInduction F.lastIso.hom (fun j h => F.incl j ≫ h)

@[simp] theorem toTop_last (F : SubbundleFiltration Q r) :
    toTop F (Fin.last r) = F.lastIso.hom :=
  Fin.reverseInduction_last

@[simp] theorem toTop_castSucc (F : SubbundleFiltration Q r) (j : Fin r) :
    toTop F j.castSucc = F.incl j ≫ toTop F j.succ :=
  Fin.reverseInduction_castSucc j

theorem mono_toTop (F : SubbundleFiltration Q r) (j : Fin (r + 1)) : Mono (toTop F j) := by
  induction j using Fin.reverseInduction with
  | last => rw [toTop_last]; infer_instance
  | cast j _ => rw [toTop_castSucc]; have := F.mono j; exact mono_comp _ _

variable (i : L.toModules ⟶ E.toModules) (eQ : cokernel i ≅ Q.toModules)

/-- The projection `p : E ⟶ Q`. -/
def proj : E.toModules ⟶ Q.toModules := cokernel.π i ≫ eQ.hom

theorem epi_proj : Epi (proj i eQ) := by
  unfold proj
  infer_instance

/-- The short complex `L → E → Q`. -/
abbrev baseComplex : ShortComplex C.toScheme.Modules :=
  ShortComplex.mk i (proj i eQ) (by simp [proj])

theorem baseComplex_shortExact [Mono i] : (baseComplex i eQ).ShortExact := by
  have e : ShortComplex.mk i (cokernel.π i) (cokernel.condition i) ≅ baseComplex i eQ :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) eQ (by simp) (by simp [proj])
  rw [← ShortComplex.shortExact_iff_of_iso e]
  exact { exact := ShortComplex.exact_cokernel i }

/-- `E_j := E ×_Q Q_j`. -/
abbrev step (F : SubbundleFiltration Q r) (j : Fin (r + 1)) : C.toScheme.Modules :=
  pullback (proj i eQ) (toTop F j)

/-- The short complex `L → E_j → Q_j`. -/
abbrev stepComplex (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    ShortComplex C.toScheme.Modules :=
  pullbackShortComplex (baseComplex i eQ) (toTop F j)

theorem stepComplex_shortExact [Mono i] (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    (stepComplex i eQ F j).ShortExact :=
  pullbackShortComplex_shortExact (baseComplex_shortExact i eQ) _

theorem stepComplex_X₁_isLocallyFree (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    (stepComplex i eQ F j).X₁.IsLocallyFree := L.locallyFree

theorem stepComplex_X₁_isFiniteType (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    (stepComplex i eQ F j).X₁.IsFiniteType := L.isFiniteType

theorem stepComplex_X₃_isLocallyFree (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    (stepComplex i eQ F j).X₃.IsLocallyFree := (F.sub j).locallyFree

theorem stepComplex_X₃_isFiniteType (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    (stepComplex i eQ F j).X₃.IsFiniteType := (F.sub j).isFiniteType

theorem step_isLocallyFree [Mono i] (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    (step i eQ F j).IsLocallyFree := by
  have := stepComplex_X₁_isLocallyFree i eQ F j
  have := stepComplex_X₃_isLocallyFree i eQ F j
  have := stepComplex_X₃_isFiniteType i eQ F j
  exact AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_shortExact
    (stepComplex_shortExact i eQ F j)

theorem step_isFiniteType [Mono i] (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    (step i eQ F j).IsFiniteType := by
  have := stepComplex_X₁_isLocallyFree i eQ F j
  have := stepComplex_X₁_isFiniteType i eQ F j
  have := stepComplex_X₃_isLocallyFree i eQ F j
  have := stepComplex_X₃_isFiniteType i eQ F j
  exact isFiniteType_of_shortExact (stepComplex_shortExact i eQ F j)

theorem step_rankAtStalk [Mono i] (F : SubbundleFiltration Q r) (j : Fin (r + 1))
    (x : C.toScheme) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk (step i eQ F j) x = (j : ℕ) + 1 := by
  have := stepComplex_X₁_isLocallyFree i eQ F j
  have := stepComplex_X₁_isFiniteType i eQ F j
  have := stepComplex_X₃_isLocallyFree i eQ F j
  have := stepComplex_X₃_isFiniteType i eQ F j
  have h := AlgebraicGeometry.Scheme.Modules.rankAtStalk_add_of_shortExact
    (stepComplex_shortExact i eQ F j) x
  have hL : AlgebraicGeometry.Scheme.Modules.rankAtStalk L.toModules x = 1 := by
    rw [L.rankAtStalk_eq x, L.rank_eq_one]
  have hQ : AlgebraicGeometry.Scheme.Modules.rankAtStalk (F.sub j).toModules x = (j : ℕ) := by
    rw [(F.sub j).rankAtStalk_eq x, F.rank_eq j]
  change AlgebraicGeometry.Scheme.Modules.rankAtStalk (step i eQ F j) x =
      AlgebraicGeometry.Scheme.Modules.rankAtStalk L.toModules x +
        AlgebraicGeometry.Scheme.Modules.rankAtStalk (F.sub j).toModules x at h
  rw [h, hL, hQ, add_comm]

/-- `E_j` as a vector bundle of rank `j + 1`. -/
def stepBundle [Mono i] (F : SubbundleFiltration Q r) (j : Fin (r + 1)) :
    AlgebraicGeometry.VectorBundle C.toVariety where
  toModules := step i eQ F j
  rank := (j : ℕ) + 1
  locallyFree := step_isLocallyFree i eQ F j
  isFiniteType := step_isFiniteType i eQ F j
  rankAtStalk_eq := step_rankAtStalk i eQ F j

/-- The zero vector bundle. -/
def zeroBundle : AlgebraicGeometry.VectorBundle C.toVariety where
  toModules := 0
  rank := 0
  locallyFree := isLocallyFree_zero _
  isFiniteType := isFiniteType_zero _
  rankAtStalk_eq := rankAtStalk_zero _

/-- The map `E_j ⟶ E_{j+1}` induced by `Q_j ⟶ Q_{j+1}`. -/
def stepMap (F : SubbundleFiltration Q r) (j : Fin r) :
    step i eQ F j.castSucc ⟶ step i eQ F j.succ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ F.incl j)
    (by rw [pullback.condition, Category.assoc, ← toTop_castSucc])

theorem stepMap_isPullback (F : SubbundleFiltration Q r) (j : Fin r) :
    IsPullback (stepMap i eQ F j) (pullback.snd _ _) (pullback.snd _ _) (F.incl j) := by
  have h : stepMap i eQ F j ≫ pullback.fst (proj i eQ) (toTop F j.succ) =
      pullback.fst (proj i eQ) (toTop F j.castSucc) := pullback.lift_fst _ _ _
  refine IsPullback.of_right (h₁₂ := pullback.fst (proj i eQ) (toTop F j.succ))
    (v₁₃ := proj i eQ) (h₂₂ := toTop F j.succ) ?_ (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)
  rw [h, ← toTop_castSucc]
  exact IsPullback.of_hasPullback _ _

theorem mono_stepMap (F : SubbundleFiltration Q r) (j : Fin r) : Mono (stepMap i eQ F j) := by
  have := mono_toTop F j.castSucc
  exact mono_of_mono_fac (pullback.lift_fst _ _ _ :
    stepMap i eQ F j ≫ pullback.fst (proj i eQ) (toTop F j.succ) = _)

/-- `cokernel (E_j ⟶ E_{j+1}) ≅ cokernel (Q_j ⟶ Q_{j+1})`. -/
def stepCokernelIso (F : SubbundleFiltration Q r) (j : Fin r) :
    cokernel (stepMap i eQ F j) ≅ cokernel (F.incl j) :=
  haveI := epi_proj i eQ
  haveI := isIso_cokernel_map_of_isPullback_of_epi (stepMap_isPullback i eQ F j)
  asIso (cokernel.map _ _ _ _ (stepMap_isPullback i eQ F j).w)

/-- The last step `E_r = E ×_Q Q ≅ E`. -/
def lastStepIso (F : SubbundleFiltration Q r) : step i eQ F (Fin.last r) ≅ E.toModules :=
  have : IsIso (toTop F (Fin.last r)) := by rw [toTop_last]; infer_instance
  asIso (pullback.fst (proj i eQ) (toTop F (Fin.last r)))

/-- The steps of the extended filtration: `0, E_0, E_1, …, E_r`. -/
def newSub [Mono i] (F : SubbundleFiltration Q r) : Fin (r + 2) → AlgebraicGeometry.VectorBundle C.toVariety :=
  Fin.cases zeroBundle (fun j => stepBundle i eQ F j)

/-- The extended filtration of `E`. -/
def extended [Mono i] (F : SubbundleFiltration Q r) : SubbundleFiltration E (r + 1) where
  sub := newSub i eQ F
  incl := Fin.cases
    (motive := fun i' => (newSub i eQ F i'.castSucc).toModules ⟶ (newSub i eQ F i'.succ).toModules)
    (0 : (0 : C.toScheme.Modules) ⟶ step i eQ F 0) (fun j => stepMap i eQ F j)
  mono := by
    intro i'
    induction i' using Fin.cases with
    | zero => exact mono_of_source_iso_zero (0 : (0 : C.toScheme.Modules) ⟶ step i eQ F 0) (Iso.refl _)
    | succ j => exact mono_stepMap i eQ F j
  rank_eq := by
    intro i'
    induction i' using Fin.cases with
    | zero => rfl
    | succ j => rfl
  lastIso := lastStepIso i eQ F
  lineQuotient := Fin.cases ⟨stepBundle i eQ F 0, by simp [stepBundle]⟩ (fun j => F.lineQuotient j)
  quotient_iso := by
    intro i'
    induction i' using Fin.cases with
    | zero => exact ⟨cokernelZeroIsoTarget⟩
    | succ j => exact ⟨stepCokernelIso i eQ F j ≪≫ (F.quotient_iso j).some⟩

end Geometric

end SubbundleFiltration.ExtendByLine

theorem SubbundleFiltration.extendByLine {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k}
    (E Q : AlgebraicGeometry.VectorBundle C.toVariety)
    (L : LineBundle C.toVariety) (i : L.toModules ⟶ E.toModules) [Mono i]
    (eQ : cokernel i ≅ Q.toModules) (hr : E.rank = Q.rank + 1)
    (F : SubbundleFiltration Q Q.rank) :
    Nonempty (SubbundleFiltration E E.rank) := by
  rw [hr]
  exact ⟨SubbundleFiltration.ExtendByLine.extended i eQ F⟩

end
