import Mathlib

/-!
# 斉次イデアルによる商の次数付け

`A` が `ℳ : ℕ → Submodule k A` で次数付けされた `k`-代数、`I` が斉次イデアルのとき、
商 `A ⧸ I` は `𝒜 i = (ℳ i)` の像で次数付けされた環になる(`GradedRing`)。
Mathlib にこのバージョンではまだない構成なので、ブローアップの座標環 `k[x,y,t,u]/(x u - t y)` を
`Proj` に載せるために自前で用意する。
-/

open DirectSum

namespace GradedQuotient

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (ℳ : ℕ → Submodule k A) [GradedAlgebra ℳ] (I : Ideal A)

/-- 商の次数付け:`𝒜 i = π(ℳ i)`。 -/
def grading : ℕ → Submodule k (A ⧸ I) := fun i =>
  (ℳ i).map (Ideal.Quotient.mkₐ k I).toLinearMap

variable {ℳ I}

lemma mem_grading {i : ℕ} {a : A} (ha : a ∈ ℳ i) : Ideal.Quotient.mk I a ∈ grading ℳ I i :=
  Submodule.mem_map.mpr ⟨a, ha, rfl⟩

variable (ℳ I)

/-- `ℳ i → 𝒜 i`。 -/
def rho (i : ℕ) : ℳ i →ₗ[k] grading ℳ I i :=
  (Ideal.Quotient.mkₐ k I).toLinearMap.restrict (fun _ hx => Submodule.mem_map_of_mem hx)

/-- 分解してから各成分を商に送る写像 `A → ⨁ 𝒜 i`。 -/
noncomputable def phi : A →ₗ[k] ⨁ i, grading ℳ I i :=
  (DirectSum.toModule k ℕ _ (fun i => (DirectSum.lof k ℕ (fun j => grading ℳ I j) i).comp (rho ℳ I i))).comp
    (DirectSum.decomposeLinearEquiv ℳ).toLinearMap

lemma phi_coe (i : ℕ) (x : ℳ i) :
    phi ℳ I (x : A) = DirectSum.of (fun j => grading ℳ I j) i (rho ℳ I i x) := by
  have h : DirectSum.decompose ℳ (x : A) = DirectSum.lof k ℕ (fun j => ℳ j) i x := by
    rw [DirectSum.decompose_coe, DirectSum.lof_eq_of]
  change DirectSum.toModule k ℕ _ _ (DirectSum.decompose ℳ (x : A)) = _
  rw [h, DirectSum.toModule_lof]
  simp [DirectSum.lof_eq_of]

lemma coe_phi (a : A) :
    DirectSum.coeAddMonoidHom (grading ℳ I) (phi ℳ I a) = Ideal.Quotient.mk I a := by
  induction a using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous i x =>
    rw [phi_coe, DirectSum.coeAddMonoidHom_of]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

variable {ℳ I}

lemma phi_eq_zero (hI : ∀ (i : ℕ) (r : A), r ∈ I → (DirectSum.decompose ℳ r i : A) ∈ I) {p : A}
    (hp : p ∈ I) : phi ℳ I p = 0 := by
  classical
  rw [← DirectSum.sum_support_decompose ℳ p, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h0 : rho ℳ I i (DirectSum.decompose ℳ p i) = 0 := by
    apply Subtype.ext
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (hI i p hp)
  rw [phi_coe, h0, map_zero]

/-- `phi` を商に降ろした加法準同型。 -/
noncomputable def phiQ (hI : ∀ (i : ℕ) (r : A), r ∈ I → (DirectSum.decompose ℳ r i : A) ∈ I) :
    (A ⧸ I) →+ ⨁ i, grading ℳ I i :=
  (AddMonoidHom.liftOfSurjective (Ideal.Quotient.mk I : A →+* A ⧸ I).toAddMonoidHom
    Ideal.Quotient.mk_surjective).toFun
    ⟨(phi ℳ I).toAddMonoidHom, fun p hp => by
      have hp' : p ∈ I := by
        simpa [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem] using hp
      exact phi_eq_zero hI hp'⟩

lemma phiQ_mk (hI : ∀ (i : ℕ) (r : A), r ∈ I → (DirectSum.decompose ℳ r i : A) ∈ I) (a : A) :
    phiQ hI (Ideal.Quotient.mk I a) = phi ℳ I a := by
  unfold phiQ
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a

instance gradedMonoid : SetLike.GradedMonoid (grading ℳ I) where
  one_mem := mem_grading (SetLike.GradedOne.one_mem) |> fun h => by simpa using h
  mul_mem := fun i j a b ha hb => by
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hb
    refine Submodule.mem_map.mpr ⟨p * q, SetLike.mul_mem_graded hp hq, ?_⟩
    simp

/-- **斉次イデアルによる商は次数付き環**。 -/
noncomputable def gradedRing
    (hI : ∀ (i : ℕ) (r : A), r ∈ I → (DirectSum.decompose ℳ r i : A) ∈ I) :
    GradedRing (grading ℳ I) :=
  { gradedMonoid with
    decompose' := phiQ hI
    left_inv := fun b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [phiQ_mk]
      exact coe_phi ℳ I a
    right_inv := fun y => by
      induction y using DirectSum.induction_on with
      | zero => simp
      | of i x =>
        obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
        have hx : (x : A ⧸ I) = Ideal.Quotient.mk I p := hpx.symm
        rw [DirectSum.coeAddMonoidHom_of, hx, phiQ_mk, phi_coe ℳ I i ⟨p, hp⟩]
        congr 1
        exact Subtype.ext hpx
      | add y z hy hz => rw [map_add, map_add, hy, hz] }

end GradedQuotient
