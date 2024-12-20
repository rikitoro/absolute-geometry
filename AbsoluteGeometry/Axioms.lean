section basic_relations

-- 点の型
axiom Point : Type
-- Betweenness : B a b c - 点 b が線分 ab の間にある
axiom B : Point → Point → Point → Prop
-- congruence : D a b c d - 線分 ab と線分 cd は合同である
axiom D : Point → Point → Point → Point → Prop

end basic_relations

section auxiliary_defs_notations

-- 共線的 (collinear)
def Col (a b c : Point) := B a b c ∨ B b c a ∨ B c a b

-- 相異なる3点
def Diff (a b c : Point) := a ≠ b ∧ b ≠ c ∧ c ≠ a

-- 三角形の合同
-- TCongr a b c p q r -- △abc ≡ △pqr
def TCongr (a b c p q r : Point) :=
  D a b p q ∧ D b c q r ∧ D c a r p

-- D a b c d を a-b ≡ c-d と表示 // ToDo 記法の結合優先度を適切に設定する必要あり
notation:75 a:76 "-" b:76 " ≡ " c:76 "-" d:76 => D a b c d

-- TCongr a b c p q r を ⟨a, b, c⟩ ≡ ⟨p, q, r⟩ と表記
notation:75 "⟨" a:76 "," b:76 "," c:76 "⟩" " ≡ " "⟨" p:76 "," q:76 "," r:76 "⟩"
  => TCongr a b c p q r

end auxiliary_defs_notations

section axioms_A -- A 結合の公理群

-- A1 共線的でない 3 点が存在する
axiom axiom_A1 :
  ∃ a b c,
  Diff a b c ∧ ¬ Col a b c

-- A2 与えれらた 2 点を通る直線は一本だけである
axiom axiom_A2 :
  ∀ a b c d,
  Col a b c ∧ Col a b d → Col a c d ∧ Col b c d

end axioms_A

section axioms_B -- B 間の公理群

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

end axioms_B

section axioms_C -- C 合同の公理群

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

-- C4 線分の複写
axiom axiom_C4 :
  ∀ a b c p,
  a ≠ b ∧ c ≠ p → ∃ d, ∀ d', B p c d' ∧ D c d' a b ↔ d = d'

-- C5 線分の和
axiom axiom_C5 :
  ∀ a b c p q r,
  B a b c ∧ B p q r → D a b p q ∧ D b c q r → D a c p r

-- C6 5辺定理
axiom axiom_C6 :
  ∀ a b c d p q r s,
  TCongr a b c p q r → B a b d → B p q s → D b d q s
  → TCongr b d c q s r

end axioms_C

section axioms_CC -- 連続性公理
/-
  CC 円円交差
    与えられた 2 円 A, B において, もし B が A の内側の点を含み,
    また A の外側の点をも含むならば, A と B は交点を持つ．
-/

/- memo
  円A : c を中心とする半径 cp の円
    B c q p ∧ c-a ≡ c-q -- a が円 A の内側の点 (i.e. ca < cp)
    B c p r ∧ c-b ≡ c-r -- b が円 A の外側の点 (i.e. cb > cp)
  円B c' を中心とし円周上に点 a, b を含む (半径 c'a = c'b)
    c'-a ≡ c'-b
-/

axiom axiom_CC :
  ∀ c q p r c' a b,
  B c q p ∧ B c p r ∧ D c a c q ∧ D c b c r ∧ D c' a c' b
  → ∃ x, D c x c p ∧ D c' a c' x

end axioms_CC


-- ----------------------------------

section
-- 線分の合同の同値性についての定理群
theorem Congr.refl : ∀ a b, a-b ≡ a-b := by
  intro a b
  apply axiom_C3 b a
  . apply axiom_C2
  . apply axiom_C2

theorem Congr.symm : ∀ a b c d, a-b ≡ c-d → c-d ≡ a-b := by
  intro a b c d h
  apply axiom_C3 a b
  . exact h
  . apply Congr.refl

theorem Congr.trans :
  ∀ a b c d p q, a-b ≡ c-d ∧ c-d ≡ p-q → a-b ≡ p-q := by
  intro a b c d p q ⟨h1, h2⟩
  apply axiom_C3 c d
  . apply Congr.symm
    exact h1
  . exact h2

end

----

section notationTest
variable (a b c d p q r: Point)


#check a-b ≡ c-d
#check D a b c d

#check B a c b

#check ⟨a,b,c⟩ ≡ ⟨p, q, r⟩
#check TCongr a b c p q r


example :
  ∀ a b c p,
  a ≠ b ∧ c ≠ p → ∃ d, ∀ d', B p c d' ∧ c-d' ≡ a-b ↔ d = d' := by
  exact axiom_C4

example :
  ∀ a b c p q r,
  B a b c ∧ B p q r →
  a-b ≡ p-q ∧ b-c ≡ q-r → a-c ≡ p-r := by
  exact axiom_C5

example :
  ∀ a b c d p q r s,
  ⟨a, b, c⟩ ≡ ⟨p, q, r⟩ → B a b d → B p q s → b-d ≡ q-s
  → ⟨b, d, c⟩ ≡ ⟨q, s, r⟩ := by
  exact axiom_C6


example :
  ∀ c q p r c' a b,
  B c q p ∧ B c p r ∧ c-a ≡ c-q ∧ c-b ≡ c-r ∧ c'-a ≡ c'-b
  → ∃ x, c-x ≡ c-p ∧ c'-a ≡ c'-x := by
  exact axiom_CC

#print axiom_A1
#print axiom_A2
#print axiom_B1
#print axiom_B2
#print axiom_B3
#print axiom_B4
#print axiom_B5
#print axiom_C1
#print axiom_C2
#print axiom_C3
#print axiom_C4
#print axiom_C5
#print axiom_C6
#print axiom_CC

end notationTest
