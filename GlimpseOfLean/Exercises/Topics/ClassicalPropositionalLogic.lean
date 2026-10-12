import GlimpseOfLean.Library.Basic
open Set

namespace ClassicalPropositionalLogic

/- Let's try to implement a language of classical propositional logic.

Note that there is also version of this file for intuitionistic logic:
`IntuitionisticPropositionalLogic.lean`
-/


def Variable : Type := ℕ

/- We define propositional formula, and some notation for them. -/

inductive Formula : Type where
  | var : Variable → Formula
  | bot : Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula

open Formula
local notation:max (priority := high) "#" x:max => var x
local infix:30 (priority := high) " || " => disj
local infix:35 (priority := high) " && " => conj
local infix:28 (priority := high) " ⇒ " => impl
local notation (priority := high) "⊥" => bot

def neg (A : Formula) : Formula := A ⇒ ⊥
local notation:(max+2) (priority := high) "~" x:max => neg x
def top : Formula := ~⊥
local notation (priority := high) "⊤" => top
def equiv (A B : Formula) : Formula := (A ⇒ B) && (B ⇒ A)
local infix:29 (priority := high) " ⇔ " => equiv

/- Let's define truth w.r.t. a valuation, i.e. classical validity -/

@[simp]
def IsTrue (φ : Variable → Prop) : Formula → Prop
  | ⊥      => False
  | # P    => φ P
  | A || B => IsTrue φ A ∨ IsTrue φ B
  | A && B => IsTrue φ A ∧ IsTrue φ B
  | A ⇒ B => IsTrue φ A → IsTrue φ B


def Satisfies (φ : Variable → Prop) (Γ : Set Formula) : Prop := ∀ {A}, A ∈ Γ → IsTrue φ A
def Models (Γ : Set Formula) (A : Formula) : Prop := ∀ {φ}, Satisfies φ Γ → IsTrue φ A
local infix:27 (priority := high) " ⊨ " => Models
def Valid (A : Formula) : Prop := ∅ ⊨ A

/- Here are some basic properties of validity.

  | A ⇔ B => IsTrue φ (A ⇒ B) && IsTrue φ (B ⇒ A)


  The tactic `simp` will automatically simplify definitions tagged with `@[simp]` and rewrite
  using theorems tagged with `@[simp]`. -/

variable {φ : Variable → Prop} {A B : Formula}
@[simp] lemma isTrue_neg : IsTrue φ ~A ↔ ¬ IsTrue φ A := by simp [neg]

lemma isTrue_neg1 : IsTrue φ ~A → ¬ IsTrue φ A := by
  intro h
  unfold neg at h
  unfold IsTrue at h
  intro h1
  exact h h1

lemma isTrue_neg2 : IsTrue φ ~A → ¬ IsTrue φ A := by
  intro h1 h2
  have h3: False := h1 h2
  exact h3


lemma isTrue_neg3 : IsTrue φ ~A → ¬ IsTrue φ A := by
  intro h1
  by_contra h2
  exact h1 h2



@[simp] lemma isTrue_top : IsTrue φ ⊤ := by
  intro h1
  exact h1




@[simp] lemma isTrue_equiv : IsTrue φ (A ⇔ B) ↔ (IsTrue φ A ↔ IsTrue φ B) := by
  constructor
  . intro h
    unfold equiv at h
    constructor
    . exact h.left
    . exact h.right
  . intro h
    constructor
    . intro h1
      apply Iff.mp h h1
    . intro h2
      apply Iff.mpr h h2




/- As an exercise, let's prove (using classical logic) the double negation elimination principle.
  `by_contra h` might be useful to prove something by contradiction. -/

example : Valid (~~A ⇔ A) := by
  unfold Valid
  unfold equiv
  intro h1 h2
  constructor
  . intro h3
    by_contra h4
    exact h3 h4
  · intro h3 h4
    unfold neg at h4
    unfold IsTrue at h4
    apply h4
    exact h3



/- We will frequently need to add an element to a set. This is done using
the `insert` function: `insert A Γ` means `Γ ∪ {A}`. -/

@[simp] lemma satisfies_insert_iff : Satisfies φ (insert A Γ) ↔ IsTrue φ A ∧ Satisfies φ Γ := by
  simp [Satisfies]


lemma satisfies_insert_iff1 : Satisfies φ (insert A Γ) ↔ IsTrue φ A ∧ Satisfies φ Γ := by
  constructor
  . intro h1
    constructor
    . apply h1
      exact mem_insert A Γ
    . unfold Satisfies
      intro h2 h3
      apply h1
      apply mem_insert_of_mem
      exact h3
  . intro h1  x hx
    rcases hx with h2 | h3
    . rw[h2]
      have h6 : IsTrue φ A := by apply  And.left h1
      exact h6

    . apply h1.right
      exact h3






/- Let's define provability w.r.t. classical logic. -/
section
set_option hygiene false -- this is a hacky way to allow forward reference in notation
local infix:27 " ⊢ " => ProvableFrom

/- `Γ ⊢ A` is the predicate that there is a proof tree with conclusion `A` with assumptions from
  `Γ`. This is a typical list of rules for natural deduction with classical logic. -/
inductive ProvableFrom : Set Formula → Formula → Prop
  | ax      : ∀ {Γ A},   A ∈ Γ   → Γ ⊢ A
  | impI    : ∀ {Γ A B},  insert A Γ ⊢ B                → Γ ⊢ A ⇒ B
  | impE    : ∀ {Γ A B},           Γ ⊢ (A ⇒ B) → Γ ⊢ A  → Γ ⊢ B
  | andI    : ∀ {Γ A B},           Γ ⊢ A       → Γ ⊢ B  → Γ ⊢ A && B
  | andE1   : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ A
  | andE2   : ∀ {Γ A B},           Γ ⊢ A && B           → Γ ⊢ B
  | orI1    : ∀ {Γ A B},           Γ ⊢ A                → Γ ⊢ A || B
  | orI2    : ∀ {Γ A B},           Γ ⊢ B                → Γ ⊢ A || B
  | orE     : ∀ {Γ A B C}, Γ ⊢ A || B → insert A Γ ⊢ C → insert B Γ ⊢ C → Γ ⊢ C
  | botC    : ∀ {Γ A},   insert ~A Γ ⊢ ⊥                → Γ ⊢ A





end



local infix:27 (priority := high) " ⊢ " => ProvableFrom

/- A formula is provable if it is provable from an empty set of assumption. -/
def Provable (A : Formula) := ∅ ⊢ A

export ProvableFrom (ax impI impE botC andI andE1 andE2 orI1 orI2 orE )
variable {Γ Δ : Set Formula}

/- We define a simple tactic `apply_ax` to prove something using the `ax` rule. -/
syntax "solve_mem" : tactic
syntax "apply_ax" : tactic
macro_rules
  | `(tactic| solve_mem) =>
    `(tactic| first | apply mem_singleton | apply mem_insert |
                      apply mem_insert_of_mem; solve_mem
                    | fail "tactic \'apply_ax\' failed")
  | `(tactic| apply_ax)  => `(tactic| { apply ax; solve_mem })

/- To practice with the proof system, let's prove the following.
  You can either use the `apply_ax` tactic defined on the previous lines, which proves a goal that
  is provable using the `ax` rule.
  Or you can do it manually, using the following lemmas about insert.
```
  mem_singleton x : x ∈ {x}
  mem_insert x s : x ∈ insert x s
  mem_insert_of_mem y : x ∈ s → x ∈ insert y s
```
-/

-- Let’s first see an example using the `apply_ax` tactic
example : {A, B} ⊢ A && B := by
  apply andI
  . apply_ax
  . apply_ax

example : {A, B} ⊢ A && B := by
  apply andI
  . apply ax
    apply mem_insert A
  . apply ax
    apply mem_insert_of_mem A
    apply mem_singleton

-- And the same one done by hand in one go.
example : {A, B} ⊢ A && B := by
  exact andI (ax (mem_insert _ _)) (ax (mem_insert_of_mem _ (mem_singleton _)))


example : Provable (~~A ⇔ A) := by
  unfold Provable
  apply andI
  · apply impI
    apply botC
    apply impE (A := ~A)
    . apply_ax
    . apply_ax
  . apply impI
    apply impI
    apply impE (A := A)
    . apply_ax
    . apply_ax





/- Optional exercise: prove the law of excluded middle. -/

example : Provable (A || ~A) := by
  unfold Provable
  apply botC
  apply impE (A := A || ~A)
  · apply_ax
  . apply orI1
    apply botC
    apply impE (A := A || ~A)
    . apply_ax
    . apply orI2
      apply_ax






/- Optional exercise: prove one of the de-Morgan laws.
  If you want to say that the argument called `A` of the axiom `impE` should be `X && Y`,
  you can do this using `impE (A := X && Y)` -/


example : Provable (~(A && B) ⇔ ~A || ~B) := by
  apply andI
  . apply impI
    apply botC
    apply impE (A := A && B)
    . apply_ax
    . apply andI
      . apply botC
        apply impE (A := ~A || ~B)
        . apply_ax
        . apply orI1
          apply_ax
      . apply botC
        apply impE (A := ~A || ~B)
        . apply_ax
        . apply orI2
          apply_ax
  . apply impI
    apply impI
    apply orE (A := ~A) (B := ~B)
    . apply_ax
    . apply impE (A := A)
      . apply_ax
      . apply andE1
        apply_ax
    . apply impE (A := B)
      . apply_ax
      . apply andE2
        apply_ax


example : Provable (~(A && B) ⇔ ~A || ~B) := by
  unfold Provable
  apply andI
  . apply impI
    apply botC
    apply impE (A := A && B)
    . apply_ax
    . apply andI
      . apply botC
        apply impE (A := ~A || ~B)
        . apply_ax
        . apply orI1
          apply_ax
      . apply botC
        apply impE (A:= ~A || ~B)
        . apply_ax
        . apply orI2
          apply_ax
  . apply impI
    apply impI
    apply orE (A:= ~A ) (B := ~B)
    . apply_ax
    . apply impE (A:= A)
      . apply_ax
      . apply andE1
        apply_ax
    . apply impE (A:= B)
      . apply_ax
      . apply andE2
        apply_ax






/- You can prove the following using `induction` on `h`. You will want to tell Lean that you want
  to prove it for all `Δ` simultaneously using `induction h generalizing Δ`.
  Lean will mark created assumptions as inaccessible (marked with †)
  if you don't explicitly name them.
  You can name the last inaccessible variables using for example `rename_i ih` or
  `rename_i A B h ih`. Or you can prove a particular case using `case impI ih => <proof>`.
  You will probably need to use the lemma
  `insert_subset_insert : s ⊆ t → insert x s ⊆ insert x t`. -/


lemma weakening (h : Γ ⊢ A) (h2 : Γ ⊆ Δ) : Δ ⊢ A := by
  induction h generalizing Δ with
  | ax ih =>
    apply h2 at ih
    apply ax
    exact ih
  | impI h1 ih1 =>
    have a1 := ih1 (insert_subset_insert h2)
    apply impI
    exact a1

  | impE h1 h3 ih1 ih3 =>
    have a1 := ih1 h2
    have a2 := ih3 h2
    exact impE a1 a2
  | andI h1 h3 ih1 ih3 =>
    have a1 := ih1 h2
    have a2 := ih3 h2
    apply andI
    . exact a1
    . exact a2
  | andE1 h1 ih1 =>
    have a1 := ih1 h2
    apply andE1 at a1
    exact a1

  | andE2 h1 ih1 =>
    have a1 := ih1 h2
    apply andE2 at a1
    exact a1

  | orI1 h1 ih =>
    have a1 := ih h2
    apply orI1
    exact a1
  | orI2 h1 ih =>
     have a1 := ih h2
     apply orI2
     exact a1
  | orE h1 h3 h4 ih1 ih3 ih4 =>
     have a1 := ih1 h2
     have a2 := ih3 (insert_subset_insert h2)
     have a3 := ih4 (insert_subset_insert h2)
     exact orE a1 a2 a3
  | botC h ih =>
    have a1 := ih (insert_subset_insert h2)
    apply botC
    exact a1









/- Use the `apply?` tactic to find the lemma that states `Γ ⊆ insert x Γ`.
  You can click the blue suggestion in the right panel to automatically apply the suggestion. -/

lemma ProvableFrom.insert (h : Γ ⊢ A) : insert B Γ ⊢ A := by
  apply weakening h
  intro x hx
  right
  exact hx



/- Proving the deduction theorem is now easy. -/



lemma deduction_theorem (h : Γ ⊢ A) : insert (A ⇒ B) Γ ⊢ B := by
  apply impE (A:= A)
  . apply_ax
  . apply weakening h
    intro a ha
    apply mem_insert_of_mem (A ⇒ B)
    exact ha




lemma Provable.mp (h1 : Provable (A ⇒ B)) (h2 : Γ ⊢ A) : Γ ⊢ B := by
  unfold Provable at h1
  apply impE (A := A)
  . apply weakening h1
    intro _ hx
    apply False.elim
    exact hx
  . exact h2


example : ∅ ⊆ Γ := by
intro x h1
apply False.elim h1



/-- You will want to use the tactics `left` and `right` to prove a disjunction, and the
  tactic `cases h` if `h` is a disjunction to do a case distinction. -/
theorem soundness_theorem (h : Γ ⊢ A) : Γ ⊨ A := by
  induction h with
  | ax ih =>
     intro x hx
     apply hx at ih
     exact ih
  | impI h ih =>
    intro x h1 h2
    apply ih
    apply satisfies_insert_iff.mpr
    exact And.intro h2 h1
  | impE h1 h2 ih1 ih2 =>
    intro x hx
    have a1 := ih1 hx
    have a2 := ih2 hx
    exact a1 a2
  | andI h1 h2 h3 h4 =>
    intro x ih1
    have a1 := h3 ih1
    have a2 := h4 ih1
    exact And.intro a1 a2
  | andE1 hAB ih =>
      intro x hx
      have a1 := ih hx
      exact a1.left
  | andE2 hAB ih =>
    intro x hx
    have a1 := ih hx
    exact a1.right
  | orI1 hA ih =>
    intro x hx
    have a1 := ih hx
    exact Or.inl a1
  | orI2 hB ih =>
    intro x hx
    have a1 := ih hx
    exact Or.inr a1
  | orE hab hac hbc ihab ihac ihbc =>
    intro x hx
    cases ihab hx with
    | inl hA =>
      exact ihac (satisfies_insert_iff.mpr ⟨ hA, hx⟩ )
    | inr hB =>
      apply ihbc
      apply satisfies_insert_iff.mpr
      exact And.intro hB hx
  | botC h ih =>
    intro x hx
    by_contra hA
    apply ih
    apply satisfies_insert_iff.mpr
    constructor
    · exact isTrue_neg.mpr hA
    · exact hx








theorem valid_of_provable (h : Provable A) : Valid A := by
  unfold Provable at h
  unfold Valid
  apply soundness_theorem
  exact h




-- **********************  completeness ********************************


/-
  If you want, you can now try some longer projects.

  Prove completeness: if a formula is valid, then it is provable
  Here is one possible strategy for this proof:
  * If a formula is valid, then so is its negation normal form (NNF);
  * If a formula in NNF is valid, then so is its conjunctive normal form (CNF);
  * If a formula in CNF is valid then it is syntactically valid:
      all its clauses contain both `A` and `¬ A` in it for some `A` (or contain `⊤`);
  * If a formula in CNF is syntactically valid, then its provable;
  * If the CNF of a formula in NNF is provable, then so is the formula itself.
  * If the NNF of a formula is provable, then so is the formula itself.

-/



end ClassicalPropositionalLogic























/-


def IsNNF : Formula → Prop
  | ⊥         => True
  | # _       => True
  | (# _) ⇒ ⊥ => True
  | ⊥ ⇒ ⊥     => True
  | A && B    => IsNNF A ∧ IsNNF B
  | A || B    => IsNNF A ∧ IsNNF B
  | _         => False

theorem nnf_isNNF (A : Formula) : IsNNF (nnf A) ∧ IsNNF (nnfNeg A) := by
  induction A with
  | bot => simp [nnf, nnfNeg, IsNNF, top, neg]
  | var p => simp [nnf, nnfNeg, IsNNF, neg]
  | conj A B ihA ihB =>
      obtain ⟨h1, h2⟩ := ihA
      obtain ⟨h3, h4⟩ := ihB
      simp only [nnf, nnfNeg, IsNNF]
      constructor
      . constructor
        . exact h1
        . exact h3
      . constructor
        . exact h2
        . exact h4

  | disj A B ihA ihB =>
      obtain ⟨h1, h2⟩ := ihA
      obtain ⟨h3, h4⟩ := ihB
      simp only [nnf, nnfNeg, IsNNF]
      constructor
      . constructor
        . exact h1
        . exact h3
      . constructor
        . exact h2
        . exact h4

  | impl A B ihA ihB =>
      obtain ⟨h1, h2⟩ := ihA
      obtain ⟨h3, h4⟩ := ihB
      simp only [nnf, nnfNeg, IsNNF]
      constructor
      . constructor
        . exact h2
        . exact h3
      . constructor
        . exact h1
        . exact h4




theorem isClause_not_and {X Y : Formula} (h : IsClause (X && Y)) : False := by
  cases h with
  | lit hlit => simp [IsLiteral] at hlit


/-   cases hAB with
      | clause hc => exact absurd hc isClause_not_and
      | and h1 h2 => exact IsCNF.and (ih1 h1 hB) (ih2 h2 hB)   -/


theorem distribute_isCNF : ∀ (A B : Formula), IsCNF A → IsCNF B → IsCNF (distribute A B) := by
  intro A B
  induction A, B using distribute.induct
  next B B1 B2 h1 h2 =>
      intro h3 h4
      simp only [distribute]
      cases h3 with
      |clause hc =>




  next A B1 B2 hA ih1 ih2 =>
      intro hA' hBB
      simp only [distribute]
      cases hBB with
      | clause hc => exact absurd hc isClause_not_and
      | and h1 h2 => exact IsCNF.and (ih1 hA' h1) (ih2 hA' h2)
  next A B hA hB =>
      intro hA' hB'
      simp only [distribute]
      have hcA : IsClause A := by
        cases hA' with
        | top => exact IsClause.top
        | clause hc => exact hc
        | and h1 h2 => exact absurd rfl (by intro he; exact hA _ _ he)
      have hcB : IsClause B := by
        cases hB' with
        | top => exact IsClause.top
        | clause hc => exact hc
        | and h1 h2 => exact absurd rfl (by intro he; exact hB _ _ he)
      exact IsCNF.clause (IsClause.or hcA hcB)



theorem cnf_isCNF {A : Formula} (h : IsNNF A) : IsCNF (cnf A) := by
  induction A with
  | bot => exact IsCNF.clause IsClause.bot
  | var p => exact IsCNF.clause (IsClause.lit (by simp [cnf, IsLiteral]))
  | conj A B ihA ihB =>
      obtain ⟨hA, hB⟩ := h
      exact IsCNF.and (ihA hA) (ihB hB)
  | disj A B ihA ihB =>
      obtain ⟨hA, hB⟩ := h
      exact distribute_isCNF _ _ (ihA hA) (ihB hB)
  | impl A B ihA ihB =>
    simp only [cnf]
    cases A with
    | var p =>
      cases B with
      | bot => exact IsCNF.clause (IsClause.lit (by simp [IsLiteral]))
      | _ => exact absurd h (by simp [IsNNF])
    | bot =>
      cases B with
      | bot => exact IsCNF.top
      | _ => exact absurd h (by simp [IsNNF])
    | _ => exact absurd h (by simp [IsNNF])


theorem completeness {A : Formula} (h : Valid A) : Provable A := by
  have h1 : Valid (nnf A) := valid_nnf h                                  -- Lemma 1: valid A → valid (nnf A)
  have h2 : Valid (cnf (nnf A)) := valid_cnf h1                           -- Lemma 2: valid (nnf A) → valid (cnf (nnf A))
  have hCNF : IsCNF (cnf (nnf A)) := -- cnf_isCNF (nnf_isNNF A).1            -- helpers: nnf_isNNF + cnf_isCNF (uses distribute_isCNF)
  have h3 : ∀ {C}, IsClause C → IsConjunctOf C (cnf (nnf A)) → SyntacticallyValid C :=
    valid_syntacticallyValid h2                                           -- Lemma 3: valid CNF → every clause syntactically valid
  have h4 : Provable (cnf (nnf A)) :=
    provable_of_syntacticallyValid_cnf hCNF h3                            -- Lemma 4: all clauses syntactically valid → CNF provable
  have h5 : Provable (nnf A) := provable_of_cnf_provable h4               -- Lemma 5: Provable (cnf X) → Provable X
  exact provable_of_nnf_provable h5                                       -- Lemma 6: Provable (nnf A) → Provable A




****************************************************************************

theorem isClause_not_and {X Y : Formula} (h : IsClause (X && Y)) : False := by
  cases h with
  | lit hlit => simp [IsLiteral] at hlit



theorem distribute_isCNF : ∀ (A B : Formula), IsCNF A → IsCNF B → IsCNF (distribute A B) := by
  intro A B
  induction A, B using distribute.induct
  -- Case 1: first argument is (B1 ∧ B2)
  next B B1 B2 ih1 ih2 =>
      intro hAB  hB
      simp only [distribute]
      cases hAB with
      | clause hc =>
          have hfalse : False := isClause_not_and hc
          exact False.elim hfalse
      | and h1 h2 =>
          have left := ih1 h1 hB
          have right := ih2 h2 hB
          exact IsCNF.and left right
  -- Case 2: second argument is (B1 ∧ B2)
  next A B1 B2 hA ih1 ih2 =>
      intro hA' hBB
      simp only [distribute]
      cases hBB with
      | clause hc =>
          have hfalse : False := isClause_not_and hc
          exact False.elim hfalse
      | and h1 h2 =>
          have left := ih1 hA' h1
          have right := ih2 hA' h2
          exact IsCNF.and left right
  -- Case 3: neither argument is an "and"
  next A B hA hB =>
      intro hA' hB'
      simp only [distribute]
      have hcA : IsClause A := by
        cases hA' with
        | top =>
            exact IsClause.top
        | clause hc =>
            exact hc
        | and h1 h2 =>
            exfalso
            exact hA _ _ rfl
      have hcB : IsClause B := by
        cases hB' with
        | top =>
            exact IsClause.top
        | clause hc =>
            exact hc
        | and h1 h2 =>
            exfalso
            exact hB _ _ rfl
      have hor := IsClause.or hcA hcB
      exact IsCNF.clause hor




theorem isCNF_cnf_nnf (A : Formula) :
    IsCNF (cnf (nnf A)) ∧ IsCNF (cnf (nnfNeg A)) := by
  induction A with
  | bot =>
    constructor
    · exact IsCNF.clause IsClause.bot
    · exact IsCNF.top
  | var p =>
    constructor
    · apply IsCNF.clause
      apply IsClause.lit
      simp [nnf, cnf, IsLiteral]
    · apply IsCNF.clause
      apply IsClause.lit
      simp [nnfNeg, cnf, neg, IsLiteral]
  | conj A B ihA ihB =>
    obtain ⟨hA1, hA2⟩ := ihA
    obtain ⟨hB1, hB2⟩ := ihB
    constructor
    · exact IsCNF.and hA1 hB1
    · exact distribute_isCNF _ _ hA2 hB2
  | disj A B ihA ihB =>
      obtain ⟨ hA1, hA2 ⟩ := ihA
      obtain ⟨ hB1, hB2 ⟩ := ihB
      have a1 := distribute_isCNF _ _ hA1 hB1
      have a2 := IsCNF.and hA2 hB2
      constructor
      . simp [nnf, cnf]
        exact a1
      . simp [nnfNeg, cnf]
        exact a2
  | impl A B ihA ihB =>
      obtain ⟨ hA1, hA2⟩ := ihA
      obtain ⟨ hB1, hB2⟩ := ihB
      have a1 := distribute_isCNF _ _ hA2 hB1
      have a2 := IsCNF.and hA1 hB2
      constructor
      . exact a1
      . simp [nnfNeg, cnf]
        exact a2


-/
