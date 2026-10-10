import BlowupPoints

/-!
# ブローアップ(層9: irrelevant ideal)

`B = k[x,y,t,u]/(x u − t y)` の irrelevant ideal `B₊ = ⊕_{n>0} Bₙ` は `(t, u)` で生成される
(`irrelevant_eq_span`)。一般に、`A₀`-代数として `A` を生成する斉次元の集合 `S` に対し
`A₊ ≤ (S)` が成り立つ(`irrelevant_le_span`;Mathlib の `Proj.iSup_basicOpen_eq_top'` の証明の取り出し)。
-/

open MvPolynomial

section general

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- `A₀`-代数として `A` を生成する斉次元の集合 `S` について、`A₊ ≤ (S)`。 -/
lemma irrelevant_le_span (S : Set A) (hSn : ∀ s ∈ S, ∃ n, s ∈ 𝒜 n)
    (hS : Algebra.adjoin (𝒜 0) S = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ Ideal.span S := by
  classical
  intro x hx
  convert_to x - GradedRing.projZeroRingHom 𝒜 x ∈ _
  · rw [GradedRing.projZeroRingHom_apply, ← GradedRing.proj_apply,
      (HomogeneousIdeal.mem_irrelevant_iff _ _).mp hx, sub_zero]
  clear hx
  have hx : x ∈ Algebra.adjoin (𝒜 0) S := by rw [hS]; trivial
  clear hS
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨n, hn⟩ := hSn x hx
    rw [GradedRing.projZeroRingHom_apply]
    by_cases hn' : n = 0
    · rw [DirectSum.decompose_of_mem_same 𝒜 (hn' ▸ hn), sub_self]
      exact zero_mem _
    · rw [DirectSum.decompose_of_mem_ne 𝒜 hn hn', sub_zero]
      exact Ideal.subset_span hx
  | algebraMap r =>
    convert zero_mem (Ideal.span S)
    rw [sub_eq_zero]
    exact (DirectSum.decompose_of_mem_same 𝒜 r.2).symm
  | add x y hx hy _ _ =>
    rw [map_add, add_sub_add_comm]
    exact add_mem ‹_› ‹_›
  | mul x y hx hy hx' hy' =>
    convert add_mem (Ideal.mul_mem_left _ x hy')
      (Ideal.mul_mem_right (GradedRing.projZeroRingHom 𝒜 y) _ hx') using 1
    rw [map_mul]
    ring

end general

namespace Blowup

section irrelevant

variable (k : Type*) [Field k]

/-- `B` は `B₀`-代数として `t, u` で生成される。 -/
lemma adjoin_tu_eq_top :
    Algebra.adjoin (blowGrading k 0)
      ({Ideal.Quotient.mk (blowIdeal k) (X 2), Ideal.Quotient.mk (blowIdeal k) (X 3)} :
        Set (BlowRing k)) = ⊤ := by
  rw [eq_top_iff]
  rintro b -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  have h0 : ∀ q : MvPolynomial (Fin 4) k, q ∈ bigrading k 0 →
      Ideal.Quotient.mk (blowIdeal k) q ∈ Algebra.adjoin (blowGrading k 0)
        ({Ideal.Quotient.mk (blowIdeal k) (X 2), Ideal.Quotient.mk (blowIdeal k) (X 3)} :
          Set (BlowRing k)) := fun q hq =>
    Subalgebra.algebraMap_mem _ (⟨Ideal.Quotient.mk (blowIdeal k) q, GradedQuotient.mem_grading hq⟩ :
      blowGrading k 0)
  induction p using MvPolynomial.induction_on with
  | C c => exact h0 _ (C_mem k c)
  | add a b ha hb =>
    rw [map_add]
    exact add_mem ha hb
  | mul_X a i ha =>
    rw [map_mul]
    refine mul_mem ha ?_
    fin_cases i
    · exact h0 _ (X0_mem k)
    · exact h0 _ (X1_mem k)
    · exact Algebra.subset_adjoin (by simp)
    · exact Algebra.subset_adjoin (by simp)

/-- **irrelevant ideal は `(t, u)` で生成される**。 -/
theorem irrelevant_eq_span :
    (HomogeneousIdeal.irrelevant (blowGrading k)).toIdeal =
      Ideal.span {Ideal.Quotient.mk (blowIdeal k) (X 2), Ideal.Quotient.mk (blowIdeal k) (X 3)} := by
  apply le_antisymm
  · refine irrelevant_le_span (blowGrading k) _ ?_ (adjoin_tu_eq_top k)
    intro s hs
    rcases hs with rfl | rfl
    · exact ⟨1, mk_mem_blowGrading k (X2_mem k)⟩
    · exact ⟨1, mk_mem_blowGrading k (X3_mem k)⟩
  · rw [Ideal.span_le]
    intro s hs
    have hmem : ∀ g : MvPolynomial (Fin 4) k, g ∈ bigrading k 1 →
        Ideal.Quotient.mk (blowIdeal k) g ∈ (HomogeneousIdeal.irrelevant (blowGrading k)).toIdeal := by
      intro g hg
      change _ ∈ HomogeneousIdeal.irrelevant (blowGrading k)
      rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
        DirectSum.decompose_of_mem_ne (blowGrading k) (mk_mem_blowGrading k hg) (by norm_num)]
    rcases hs with rfl | rfl
    · exact hmem _ (X2_mem k)
    · exact hmem _ (X3_mem k)

end irrelevant

end Blowup
