import OMAReductions.R_Erdos420_erdos_420_parts_i_R1

-- Step Erdos420.erdos_420.parts.i.R1.H2: hypothesis H2 of reduction Erdos420.erdos_420.parts.i.R1
-- Credit: @Waxmell114514
-- H2 := ∀ a b p s : ℕ, p.Prime → 0 < s → s < p → a < s * p → s * p ≤ b →     (s + 1) * (σ 0 a.factorial) ≤ s * (σ 0 b.factorial)
-- The merged reduction already proves this as prime_gain_proof; this file records the step as closed.

theorem OMA.solution : OMA.R_Erdos420_erdos_420_parts_i_R1.H2 :=
  OMA.R_Erdos420_erdos_420_parts_i_R1.prime_gain_proof
