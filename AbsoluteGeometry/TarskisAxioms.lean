-- 点の型
axiom Point : Type
-- Betweenness : B a b c - 点 b が線分 ab の間にある
axiom B : Point → Point → Point → Prop
-- congruence : D a b c d - 線分 ab と線分 cd は合同である
axiom D : Point → Point → Point → Point → Prop

-- D a b c d を a-b ≡ c-d と表示 // ToDo 記法の結合優先度を適切に設定する必要あり
notation:75 a:76 "-" b:76 " ≡ " c:76 "-" d:76 => D a b c d

axiom axiom_T1 :
  ∀ a b,
  a-b ≡ b-a

axiom axiom_T2 :
  ∀ a b p q r s,
  a-b ≡ p-q ∧ a-b ≡ r-s → p-q ≡ r-s

axiom axiom_T3 :
  ∀ a b c,
  a-b ≡ c-c → a = b

axiom axiom_T4 :
  ∀ a b c q,
  ∃ x, B q a x ∧ a-x ≡ b-c

axiom axiom_T5 : -- five segments
  ∀ a b c d p q r s,
  a ≠ b ∧ B a b c ∧ B p q r ∧
  a-b ≡ p-q ∧ b-c ≡ q-r ∧ a-d ≡ p-s ∧ b-d ≡ q-s
  → c-d ≡ r-s

axiom axiom_T6 :
  ∀ a b,
  B a b a → a = b

axiom axiom_T7 : -- Pasch's axiom
  ∀ a b c p q,
  B a p c ∧ B b q c → ∃ x, B p x b ∧ B q x a

axiom axiom_T8 : -- dim ≥ 2
  ∃ a b c, ¬ B a b c ∧ ¬ B b c a ∧ ¬ B c a b

axiom axiom_T9 : -- dim ≤ 3
  ∀ a b c p q,
  p ≠ q ∧ a-p ≡ a-q ∧ b-p ≡ b-q ∧ c-p ≡ c-q
  → B a b c ∨ B b c a ∨ B c a b

axiom axiom_TCont (α β : Point → Prop) :
  (∃ a, ∀ x y, α x ∧ β y → B a x y) →
  ∃ b, ∀ x y, α x ∧ β y → B x b y



-----
#print axiom_T1
#print axiom_T2
#print axiom_T3
#print axiom_T4
#print axiom_T5
#print axiom_T6
#print axiom_T7
#print axiom_T8
#print axiom_T9
#print axiom_TCont
