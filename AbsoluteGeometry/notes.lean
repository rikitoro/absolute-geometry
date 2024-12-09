import AbsoluteGeometry.Axioms


/- 命題1 与えられた線分 ab を一辺とする正三角形を書くことができる -/
theorem exists_regular_traiangle (a b : Point) (h : a ≠ b) :
  ∃ c, a-b ≡ b-c ∧ b-c ≡ c-a ∧ c-a ≡ a-b := by
  sorry
