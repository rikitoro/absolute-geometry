import AbsoluteGeometry.lemma

-- 点の型
axiom Point : Type
-- Betweenness : B a b c - 点 b が線分 ab の間にある
axiom B : Point → Point → Point → Prop
-- congruence : D a b c d - 線分 ab と線分 cd は合同である
axiom D : Point → Point → Point → Point → Prop

-- 共線的 (collinear)
def Col (a b c : Point) := B a b c ∨ B b c a ∨ B c a b

-- 相異なる3点
def Diff (a b c : Point) := a ≠ b ∧ b ≠ c ∧ c ≠ a


/-
  A 結合の公理群
-/

-- A1 共線的でない 3 点が存在する
axiom axiom_A1 :
  ∃ a b c,
  Diff a b c ∧ ¬ Col a b c

-- A2 与えれらた 2 点を通る直線は一本だけである
axiom axiom_A2 :
  ∀ a b c d,
  Col a b c ∧ Col a b d → Col a c d ∧ Col b c d


/-
  B 間の公理群
-/

-- B1 点 b が点 a と点 c の間にあるならば a, b, c は異なる 3 点である
axiom axiom_B1 :
  ∀ a b c,
  B a b c → Diff a b c

-- B2 点 b が点 a と点 c の間にあるならば b は c と a の間にある
axiom axiom_B2 :
  ∀ a b c,
  B a b c → B c b a

-- B3 2点a, b に対し B(a, x, b) を満たす点 x と B (a, b, y) を満たす点 y が存在する
axiom axiom_B3 :
  ∀ a b,
  a ≠ b → (∃ x, B a x b) ∧ ∃ y, B a b y

-- B4 3点 a, b, c が共線的ならばその中の 1 点だけが他の 2 点の間にある
axiom axiom_B4 :
  ∀ a b c,
  B a b c → ¬ B b a c ∧ ¬ B a c b

-- B5 パッシュの公理
axiom axiom_B5 :
  ∀ a b c p q,
  B a q b ∧ ¬ Col a b c ∧ ¬ Col p q a ∧ ¬ Col p q b ∧ ¬ Col p q c
  → ∃ x, B p q x ∧ (B a x c ∨ B b x c)


/-
  C 合同の公理群
-/


-- C1
axiom axiom_C1 :
  ∀ a p q,
  D a a p q → p = q

-- C2
axiom axiom_C2 :
  ∀ a b,
  D a b b a

-- C3
axiom axiom_C3 :
  ∀ a b p q r s,
  D a b p q → D a b r s → D p q r s


-- D a b c d を ⟨a,b⟩ ≡ ⟨c,d⟩ とあらわす
notation "⟨"a","b"⟩" " ≡ " "⟨"c","d"⟩" => D a b c d

lemma Congr.refl : ∀ a b, ⟨a, b⟩ ≡ ⟨a, b⟩ := by
  intro a b
  apply axiom_C3 b a
  . apply axiom_C2
  . apply axiom_C2

lemma Congr.symm : ∀ a b c d, ⟨a, b⟩ ≡ ⟨c, d⟩ → ⟨c, d⟩ ≡ ⟨a, b⟩ := by
  intro a b c d h
  apply axiom_C3 a b
  . exact h
  . apply Congr.refl

lemma Congr.trans :
  ∀ a b c d p q, ⟨a, b⟩ ≡ ⟨c, d⟩ ∧ ⟨c, d⟩ ≡ ⟨p, q⟩ → ⟨a, b⟩ ≡ ⟨p, q⟩ := by
  intro a b c d p q ⟨h1, h2⟩
  apply axiom_C3 c d
  . apply Congr.symm
    exact h1
  . exact h2


-- C4 線分の複写

-- C5 線分の和
