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
  . intro h1 x hx
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

-- And the same one done by hand in one go.


/- Optional exercise: prove the law of excluded middle. -/






/- Optional exercise: prove one of the de-Morgan laws.
  If you want to say that the argument called `A` of the axiom `impE` should be `X && Y`,
  you can do this using `impE (A := X && Y)` -/





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

/- Negation Normal Form.
   `nnf A`     : an NNF formula equivalent to `A`
   `nnfNeg A`  : an NNF formula equivalent to `~A`
   -/


mutual
def nnf : Formula → Formula
  | ⊥      => ⊥
  | # p    => # p
  | A && B => nnf A && nnf B
  | A || B => nnf A || nnf B
  | A ⇒ B  => nnfNeg A || nnf B          -- A ⇒ B  ≡  ~A ∨ B

def nnfNeg : Formula → Formula
  | ⊥      => ⊤
  | # p    => ~(# p)
  | A && B => nnfNeg A || nnfNeg B        -- De Morgan: ~(A∧B) ≡ ~A ∨ ~B
  | A || B => nnfNeg A && nnfNeg B        -- De Morgan: ~(A∨B) ≡ ~A ∧ ~B
  | A ⇒ B  => nnf A && nnfNeg B           -- ~(A⇒B) ≡ A ∧ ~B
end



/- Correctness: `nnf A` really is equivalent to `A`, and `nnfNeg A` really is
   equivalent to `~A`. -/




theorem nnf_nnfNeg_correct {φ : Variable → Prop} (A : Formula) :
    (IsTrue φ (nnf A) ↔ IsTrue φ A) ∧ (IsTrue φ (nnfNeg A) ↔ ¬ IsTrue φ A) := by
  induction A with
  | bot =>
    constructor
    . unfold nnf
      constructor
      . intro h1
        exact h1
      . intro h1
        exact h1

    . unfold nnfNeg
      constructor
      . intro h1 h2
        exact h1 h2
      . intro h1
        by_contra h
        exact h h1


  | var p =>
    constructor
    . constructor
      . unfold nnf
        intro h
        exact h
      . unfold nnf
        intro h
        exact h
    . constructor
      . unfold nnfNeg
        intro h1 h2
        exact h1 h2
      . unfold nnfNeg
        intro h1 h2
        exact h1 h2


  | conj A B ih1 ih2 =>
    obtain ⟨ih1, ih1neg⟩ := ih1
    obtain ⟨ih2, ih2neg⟩ := ih2
    constructor
    · simp[IsTrue]
      simp [nnf]
      rw [ih1]
      rw [ih2]
    · unfold nnfNeg
      simp [IsTrue]
      rw[ih1neg]
      rw[ih2neg]
      constructor
      · intro h hA
        cases h with
        | inl hNA =>
            intro h3
            exact hNA hA
        | inr hNB =>
            exact hNB
      · intro h
        by_cases hA : IsTrue φ A
        · right
          exact h hA
        · left
          exact hA



  | disj A B ih1 ih2 =>
    obtain ⟨ ih1, ih1neg ⟩ := ih1
    obtain ⟨ ih2, ih2neg ⟩ := ih2
    constructor
    .
      simp [nnf]
      rw [ih1]
      rw [ih2]
    .
      simp [nnfNeg]
      rw [ih1neg]
      rw [ih2neg]


  | impl A B ih1 ih2 =>
    obtain ⟨ ih1, ih1neg ⟩ := ih1
    obtain ⟨ ih2, ih2neg ⟩ := ih2
    constructor
    . simp [nnf]
      rw [ih1neg]
      rw [ih2]
      tauto
    . simp [nnfNeg]
      rw [ih1]
      rw [ih2neg]





theorem isTrue_nnf {φ : Variable → Prop} (A : Formula) :
    IsTrue φ (nnf A) ↔ IsTrue φ A := by
  exact (nnf_nnfNeg_correct A).left


theorem isTrue_nnfNeg {φ : Variable → Prop} (A : Formula) :
    (IsTrue φ (nnfNeg A) ↔ ¬ IsTrue φ A) := by
  exact (nnf_nnfNeg_correct A).right

/-- **Lemma 1.** If `A` is valid, so is its negation normal form. -/


theorem valid_nnf (h : Valid A) : Valid (nnf A) := by
  intro x hx
  have a1 := h hx
  apply (isTrue_nnf A).mpr
  exact a1





-- ******************************** LEMMA 2 ******************************************

/- `distribute A B` computes a CNF formula equivalent to `A || B`, given that
   `A` and `B` are already in CNF.  -/

def distribute : Formula → Formula → Formula
  | A && B, C => distribute A C && distribute B C
  | A, B && C => distribute A B && distribute A C
  | A, B       => A || B

/- `cnf A` computes a CNF formula equivalent to `A`.
   when `A` is already in NNF (no `⇒`) -/


def cnf : Formula → Formula
  | ⊥      => ⊥
  | # p    => # p
  | A && B => cnf A && cnf B
  | A || B => distribute (cnf A) (cnf B)
  | A ⇒ B  => A ⇒ B






/-- Correctness of `distribute`: it really does compute `A || B`. -/



theorem distribute_correct {φ : Variable → Prop} (A B : Formula) :
    IsTrue φ (distribute A B) ↔ IsTrue φ A ∨ IsTrue φ B := by

  induction A, B using distribute.induct
  next B B1 B2 ih1 ih2 =>
      simp only [distribute, IsTrue]
      constructor
      · intro h
        rcases h with ⟨ hB1, hB2 ⟩
        have a1 := ih1.mp hB1
        have a2 := ih2.mp hB2
        rcases a1 with h1 | h2
        . rcases a2 with h3 | h4
          . have a3 := And.intro h1 h3
            exact Or.inl a3
          . exact Or.inr h4
        . rcases a2 with h3 | h4
          . exact Or.inr h2
          . exact Or.inr h4
      . intro h
        rcases h with ⟨h1, h2⟩ | hB
        . constructor
          . have h : IsTrue φ B ∨ IsTrue φ B2 := Or.inl h1
            have a1 : IsTrue φ (distribute B B2) := ih1.mpr h
            exact a1
          . have h : IsTrue φ B1 ∨ IsTrue φ B2 := Or.inl h2
            have a1 : IsTrue φ (distribute B1 B2) := ih2.mpr h
            exact a1
        . have a1 : IsTrue φ B ∨ IsTrue φ B2 := Or.inr hB
          have a2 : IsTrue φ B1 ∨ IsTrue φ B2 := Or.inr hB
          have a3 := ih1.mpr a1
          have a4 := ih2.mpr a2
          exact And.intro a3 a4
  next A B1 B2 hA ih1 ih2 =>
      simp only [distribute, IsTrue]
      constructor
      . intro h
        rcases h with  ⟨ h1 , h2 ⟩
        have a1 := ih1.mp h1
        have a2 := ih2.mp h2
        rcases a1 with hA1 | hB1     -- rintro (hA1 | ⟨hB1, hB2⟩)
        . exact Or.inl hA1
        . rcases a2 with hA2 | hB2
          . exact Or.inl hA2
          . have a3 := And.intro hB1 hB2
            exact Or.inr a3
      . intro h
        rcases h with hA1 | ⟨ hB1 , hB2⟩
        . have a1 : IsTrue φ A ∨ IsTrue φ B1 := Or.inl hA1
          have a2 : IsTrue φ A ∨ IsTrue φ B2 := Or.inl hA1
          have a3 : IsTrue φ (distribute A B1) := ih1.mpr a1
          have a4 : IsTrue φ (distribute A B2) := ih2.mpr a2
          exact And.intro a3 a4
        . have a1 : IsTrue φ A ∨ IsTrue φ B1 := Or.inr hB1
          have a2 : IsTrue φ A ∨ IsTrue φ B2 := Or.inr hB2
          have a3 : IsTrue φ (distribute A B1) := ih1.mpr a1
          have a4 : IsTrue φ (distribute A B2) := ih2.mpr a2
          exact And.intro a3 a4
  next A B hA hB =>
      simp only [distribute, IsTrue]






/-- Correctness of `cnf`: it really does compute the same truth value. -/

theorem isTrue_cnf {φ : Variable → Prop} (A : Formula) :
    IsTrue φ (cnf A) ↔ IsTrue φ A := by
  induction A with
  | bot => simp [cnf, IsTrue]
  | var p => simp [cnf, IsTrue]
  | conj A B ihA ihB =>
       simp [cnf]
       rw [ihA]
       rw[ihB]
  | disj A B ihA ihB =>
      simp only [cnf, IsTrue]
      rw [distribute_correct]
      rw [ihA]
      rw [ihB]
  | impl A B h1 h2 => simp [cnf]

/-- **Lemma 2.** If `A` is valid, so is its conjunctive normal form. -/

theorem valid_cnf (h : Valid A) : Valid (cnf A) := by
  unfold Valid
  intro x hx
  apply (isTrue_cnf A).mpr
  apply h at hx
  exact hx





-- *****************************  Lemma 3 ****************************************

/-- A literal is a variable `#p` or a negated variable `~#p`-/
def IsLiteral : Formula → Prop
  | # _        => True
  | (# _) ⇒ ⊥  => True
  | _          => False


/-- A clause is `⊥` , `⊤` , or built from literals using only `||`. -/

inductive IsClause : Formula → Prop
  | bot  : IsClause ⊥
  | top  : IsClause ⊤
  | lit  {X : Formula} (h : IsLiteral X) : IsClause X
  | or   {X Y : Formula} (hX : IsClause X) (hY : IsClause Y) : IsClause (X || Y)

/-- A CNF formula is `⊤`, a clause, or a conjunction of CNF formulas. -/


inductive IsCNF : Formula → Prop
  | top    : IsCNF ⊤
  | clause {X : Formula} (h : IsClause X) : IsCNF X
  | and    {X Y : Formula} (hX : IsCNF X) (hY : IsCNF Y) : IsCNF (X && Y)


/-- Variables occurring positively (as `#p`) in a formula. -/

def posAtoms : Formula → Set Variable
  | # p     => {p}
  | A || B  => posAtoms A ∪ posAtoms B
  | _       => ∅

/-- Variables occurring negatively (as `~#p`) in a formula. -/

def negAtoms : Formula → Set Variable
  | (# p) ⇒ ⊥ => {p}
  | A || B    => negAtoms A ∪ negAtoms B
  | _         => ∅

/-- Does `⊤` occur as a disjunct? -/

def hasTop : Formula → Prop
  | ⊥ ⇒ ⊥  => True          --  (`⊤ := ~⊥ := ⊥ ⇒ ⊥`)
  | A || B => hasTop A ∨ hasTop B
  | ?_     => False

/-- A clause is syntactically valid if it contains `⊤`, or some `p` with
    both `#p` and `~#p` occurring in it. -/

def SyntacticallyValid (C : Formula) : Prop :=
  hasTop C ∨ ∃ p, p ∈ posAtoms C ∧ p ∈ negAtoms C


/-- If `φ` falsifies every positive atom and satisfies every negative atom of `C`,
    then `φ` falsifies `C` itself. This is proved for a general `φ`, not one tied
    to `C` by construction — that's what lets the induction go through cleanly. -/



theorem falsify_aux {φ : Variable → Prop} {C : Formula} (hC : IsClause C)
    (h0 : ¬ hasTop C)
    (h1 : ∀ p, p ∈ posAtoms C → ¬ φ p)
    (h2 : ∀ p, p ∈ negAtoms C → φ p) :
    ¬ IsTrue φ C := by
  induction hC with
  | bot =>
      intro h
      exact h

  | top  =>
      have h : hasTop ⊤ := by simp [hasTop, top, neg] at h0
      exact False.elim (h0 h)


  | lit ih =>
    unfold IsLiteral at ih
    split at ih

    · next t =>
        have a1 := h1 t
        simp [posAtoms] at a1
        simp [IsTrue]
        exact a1

    · next p =>
        intro h3
        apply h3
        have a1 := h2 p
        simp [negAtoms] at a1
        simp [IsTrue]
        exact a1

    · simp at ih

  | or  hA hB ihA ihB =>
      rename_i X Y
      simp [IsTrue ]
      constructor
      . have h0A : ¬ hasTop X := by
          intro hX
          apply h0
          unfold hasTop
          exact Or.inl hX
        have h1A : ∀ p, p ∈ posAtoms X → ¬ φ p := by
          intro p hp
          apply h1 p
          unfold posAtoms
          exact Or.inl hp
        have h2A : ∀ p, p ∈ negAtoms X → φ p := by
          intro p hp
          apply h2 p
          exact Or.inl hp
        exact ihA h0A h1A h2A
      . have h0B : ¬ hasTop Y := by
          intro hY
          apply h0
          exact Or.inr hY
        have h1B : ∀ p, p ∈ posAtoms Y → ¬ φ p := by
          intro p hp
          apply h1 p
          exact Or.inr hp
        have h2B : ∀ p, p ∈ negAtoms Y → φ p := by
            intro p hp
            apply h2 p
            exact Or.inr hp
        exact ihB h0B h1B h2B





theorem exists_falsifying_valuation {C : Formula} (hC : IsClause C)
    (hnv : ¬ SyntacticallyValid C) :
    ∃ φ : Variable → Prop, ¬ IsTrue φ C := by
  refine ⟨ fun p => p ∈ negAtoms C, ?_ ⟩
  apply falsify_aux hC
  unfold SyntacticallyValid at hnv
  . intro h1
    exact hnv (Or.inl h1)
  . unfold SyntacticallyValid at hnv
    intro p h2 h3
    exact hnv (Or.inr ⟨ p, h2, h3 ⟩)
  . unfold SyntacticallyValid at hnv
    intro p hp
    exact hp







/-- `IsConjunctOf C A` means `C` appears as a top-level conjunct of `A`,
    i.e. `A` is built as a conjunction tree and `C` is one of its leaves. -/

inductive IsConjunctOf : Formula → Formula → Prop
  | self  {X : Formula} : IsConjunctOf X X
  | left  {X Y Z : Formula} : IsConjunctOf X Y → IsConjunctOf X (Y && Z)
  | right {X Y Z : Formula} : IsConjunctOf X Z → IsConjunctOf X (Y && Z)



theorem isTrue_of_isConjunctOf {φ : Variable → Prop} {C A : Formula}
    (h : IsConjunctOf C A) (hA : IsTrue φ A) : IsTrue φ C := by
  induction h with
  | self => exact hA
  | left hCY ih => exact ih hA.left
  | right hCZ ih => exact ih hA.right


theorem Satisfies_empty (φ : Variable → Prop) : Satisfies φ (∅ : Set Formula) := by
  intro A hA
  apply False.elim hA


/-- **Lemma 3.** If a CNF formula is valid, every clause in it is syntactically valid. -/

theorem valid_syntacticallyValid {A : Formula} (hvalid : Valid A) :
    ∀ {C}, IsClause C → IsConjunctOf C A → SyntacticallyValid C := by
  intro C h1 h2
  by_contra h3
  obtain ⟨φ, hφ⟩ := exists_falsifying_valuation h1 h3
  apply hφ
  apply isTrue_of_isConjunctOf h2
  apply hvalid
  exact Satisfies_empty φ




-- *********************** Lemma 4  ************************************************

theorem excluded_middle (A : Formula) : Provable (A || ~A) := by
  apply botC
  apply impE (A := A || ~A)
  · apply_ax
  . apply orI1
    apply botC
    apply impE (A := A || ~A)
    . apply_ax
    . apply orI2
      apply_ax


inductive IsDisjunctOf : Formula → Formula → Prop
  | self  {X : Formula} : IsDisjunctOf X X
  | left  {X Y Z : Formula} : IsDisjunctOf X Y → IsDisjunctOf X (Y || Z)
  | right {X Y Z : Formula} : IsDisjunctOf X Z → IsDisjunctOf X (Y || Z)

/-- If `X` is a leaf of `C`'s disjunction tree and `X` is provable (from Γ),
    so is all of `C` — build it up via `orI1`/`orI2` at each level. -/


theorem provable_of_isDisjunctOf {X C : Formula} {Γ : Set Formula}
    (h : IsDisjunctOf X C) (hX : Γ ⊢ X) : Γ ⊢ C := by
  induction h with
  | self => exact hX
  | left _ ih => exact orI1 ih
  | right _ ih => exact orI2 ih



theorem isDisjunctOf_of_mem_posAtoms {p : Variable} {C : Formula} (hC : IsClause C)
    (hp : p ∈ posAtoms C) : IsDisjunctOf (#p) C := by
  induction hC with
  | bot =>
      unfold posAtoms at hp
      simp at hp

  | top =>
      simp [posAtoms, top, neg] at hp

  | lit hlit =>
      rename_i X
      unfold IsLiteral at hlit
      split at hlit
      · next q =>
        simp [posAtoms] at hp
        rw [hp]
        exact IsDisjunctOf.self
      · rename_i y
        next q => simp [posAtoms] at hp
      · simp at hlit

  | or hA hB ihA ihB =>
      rename_i A B
      simp only [posAtoms] at hp
      rcases hp with h1 | h2
      · have a1 := ihA h1
        exact IsDisjunctOf.left a1
      · have a2 := ihB h2
        exact IsDisjunctOf.right a2

theorem isDisjunctOf_of_mem_negAtoms {p : Variable} {C : Formula} (hC : IsClause C)
    (hp : p ∈ negAtoms C) : IsDisjunctOf (~(#p)) C := by
  induction hC with
  | bot =>
    simp [negAtoms] at hp

  | top =>
    simp [negAtoms, top, neg] at hp

  | lit hlit =>
      rename_i X
      unfold IsLiteral at hlit
      split at hlit
      · next q => simp [negAtoms] at hp
      · next q =>
          simp [negAtoms] at hp
          rw [hp]
          exact IsDisjunctOf.self
      · simp at hlit

  | or hA hB ihA ihB =>
      simp only [negAtoms] at hp
      rcases hp with h1 | h2
      · exact IsDisjunctOf.left (ihA h1)
      · exact IsDisjunctOf.right (ihB h2)

/-- Provable ⊤ is immediate: ⊤ := ~⊥ := ⊥ ⇒ ⊥. -/

theorem provable_top : Provable (⊤ : Formula) := by
  unfold Provable
  apply impI
  apply_ax

theorem isDisjunctOf_top_of_hasTop {C : Formula} (hC : IsClause C) (ht : hasTop C) :
    IsDisjunctOf ⊤ C := by
  induction hC with
  | bot =>
    simp [hasTop] at ht

  | top =>
    exact IsDisjunctOf.self

  | lit hlit =>
    exfalso
    unfold IsLiteral at hlit
    unfold hasTop at ht
    split at hlit
    . simp_all
    . simp_all
    . simp_all

  | or hA hB ihA ihB =>
      simp only [hasTop] at ht
      rcases ht with h1 | h2
      · exact IsDisjunctOf.left (ihA h1)
      · exact IsDisjunctOf.right (ihB h2)


theorem provable_of_syntacticallyValid {C : Formula} (hC : IsClause C)
    (h1 : SyntacticallyValid C) : Provable C := by
  unfold Provable
  rcases h1 with ht | ⟨p, hp, hn⟩
  · have hDisj : IsDisjunctOf ⊤ C := by
      exact isDisjunctOf_top_of_hasTop hC ht
    have hTop : Provable ⊤ := by
      exact provable_top
    exact provable_of_isDisjunctOf hDisj hTop

  · have hDisjP : IsDisjunctOf (#p) C := isDisjunctOf_of_mem_posAtoms hC hp
    have hDisjN : IsDisjunctOf (~(#p)) C := isDisjunctOf_of_mem_negAtoms hC hn
    have hEM : (∅ : Set Formula) ⊢ (#p || ~(#p)) := excluded_middle (#p)
    have hCaseP : insert (#p) (∅ : Set Formula) ⊢ C :=
      provable_of_isDisjunctOf hDisjP (by apply_ax)
    have hCaseN : insert (~(#p)) (∅ : Set Formula) ⊢ C :=
      provable_of_isDisjunctOf hDisjN ( by apply_ax)
    have a1 := orE hEM hCaseP hCaseN
    exact a1







/-- **Lemma 4.** If every clause of a CNF formula is syntactically valid, the formula
    is provable. -/

theorem provable_of_syntacticallyValid_cnf {A : Formula} (hcnf : IsCNF A)
    (hsv : ∀ {C}, IsClause C → IsConjunctOf C A → SyntacticallyValid C) : Provable A := by
  induction hcnf with
  | top => exact provable_top

  | clause h1 =>
    rename_i y
    exact provable_of_syntacticallyValid h1 (hsv h1 IsConjunctOf.self)

  | and hA hB ihA ihB =>
    apply andI

    · apply ihA
      intro C hCl hConj
      apply hsv
      exact hCl
      exact IsConjunctOf.left hConj

    · apply ihB
      intro C hCl hConj
      apply hsv
      exact hCl
      exact IsConjunctOf.right hConj





#check Iff.mpr
--**************************** LEMMA 5 ******************************************************

theorem iffI {Γ A B} (h1 : insert A Γ ⊢ B) (h2 : insert B Γ ⊢ A) : Γ ⊢ (A ⇔ B) := by
  have a1 := impI h1
  have a2 := impI h2
  exact andI a1 a2

theorem iff_mp {Γ A B} (h : Γ ⊢ (A ⇔ B)) (ha : Γ ⊢ A) : Γ ⊢ B := by
  have a1 := andE1 h
  exact impE a1 ha


theorem iff_mpr {Γ A B} (h : Γ ⊢ (A ⇔ B)) (hb : Γ ⊢ B) : Γ ⊢ A := by
  have a1 := andE2 h
  exact impE a1 hb


theorem iff_refl (A : Formula) : Provable (A ⇔ A) := by
  unfold Provable
  apply iffI
  . apply_ax
  . apply_ax

theorem iff_trans {A B C : Formula} (h1 : Provable (A ⇔ B)) (h2 : Provable (B ⇔ C)) :
    Provable (A ⇔ C) := by
  unfold Provable at h1 h2 ⊢
  apply iffI
  . have hAB : insert A (∅ : Set Formula) ⊢ A ⇔ B := by
      apply weakening h1
      exact Set.empty_subset _
    have hBC : insert A (∅ : Set Formula) ⊢ B ⇔ C := by
      apply weakening h2
      exact Set.empty_subset _
    have hA : insert A (∅ : Set Formula) ⊢ A := by
      apply_ax
    have hB : insert A (∅ : Set Formula) ⊢ B := by
      apply iff_mp hAB
      exact hA
    have hC : insert A (∅ : Set Formula) ⊢ C := by
      apply iff_mp hBC
      exact hB
    exact hC
  . have hBC : insert C (∅ : Set Formula) ⊢ B ⇔ C := by
      apply weakening h2
      exact Set.empty_subset _
    have hAB : insert C (∅ : Set Formula) ⊢ A ⇔ B := by
      apply weakening h1
      exact Set.empty_subset _
    have hC : insert C (∅ : Set Formula) ⊢ C := by
      apply_ax
    have hB : insert C (∅ : Set Formula) ⊢ B := by
      apply iff_mpr hBC
      exact hC
    have hA : insert C (∅ : Set Formula) ⊢ A := by
      apply iff_mpr hAB
      exact hB
    exact hA




theorem iff_cong_and {A A' B B' : Formula}
    (h1 : Provable (A ⇔ A')) (h2 : Provable (B ⇔ B')) : Provable ((A && B) ⇔ (A' && B')) := by
  unfold Provable at h1 h2 ⊢
  apply iffI
  · have hA : insert (A && B) (∅ : Set Formula) ⊢ A := by
      apply andE1
      apply_ax
    have hB : insert (A && B) (∅ : Set Formula) ⊢ B := by
      apply andE2
      apply_ax
    have h3 : insert (A && B) (∅ : Set Formula) ⊢ A ⇔ A' := by
      apply weakening h1
      exact Set.empty_subset _
    have h4 : insert (A && B) (∅ : Set Formula) ⊢ B ⇔ B' := by
      apply weakening h2
      exact Set.empty_subset _
    have hA' : insert (A && B) (∅ : Set Formula) ⊢ A' := by
      apply iff_mp h3
      exact hA
    have hB' : insert (A && B) (∅ : Set Formula) ⊢ B' := by
      apply iff_mp h4
      exact hB
    apply andI
    · exact hA'
    · exact hB'
  · have hA' : insert (A' && B') (∅ : Set Formula) ⊢ A' := by
      apply andE1
      apply_ax
    have hB' : insert (A' && B') (∅ : Set Formula) ⊢ B' := by
      apply andE2
      apply_ax
    have h3 : insert (A' && B') (∅ : Set Formula) ⊢ A ⇔ A' := by
      apply weakening h1
      exact Set.empty_subset _
    have h4 : insert (A' && B') (∅ : Set Formula) ⊢ B ⇔ B' := by
      apply weakening h2
      exact Set.empty_subset _
    have hA : insert (A' && B') (∅ : Set Formula) ⊢ A := by
      apply iff_mpr h3
      exact hA'
    have hB : insert (A' && B') (∅ : Set Formula) ⊢ B := by
      apply iff_mpr h4
      exact hB'
    apply andI
    · exact hA
    · exact hB



/-

exact andI (iff_mpr (weakening h1 (Set.empty_subset _)) (andE1 (by apply_ax)))
                (iff_mpr (weakening h2 (Set.empty_subset _)) (andE2 (by apply_ax)))


-/

theorem iff_cong_or {A A' B B' : Formula}
    (h1 : Provable (A ⇔ A')) (h2 : Provable (B ⇔ B')) :
    Provable ((A || B) ⇔ (A' || B')) := by
  unfold Provable at h1 h2 ⊢
  apply iffI
  · -- Goal: insert (A || B) ∅ ⊢ A' || B'
    have hor : insert (A || B) (∅ : Set Formula) ⊢ A || B := by
      apply_ax
    -- case 1: assume A
    have caseA : insert A (insert (A || B) (∅ : Set Formula)) ⊢ A' || B' := by
      have h1w : insert A (insert (A || B) (∅ : Set Formula)) ⊢ (A ⇔ A') :=
        weakening h1 (Set.empty_subset _)
      have hA : insert A (insert (A || B) (∅ : Set Formula)) ⊢ A := by
        apply_ax
      have hA' : insert A (insert (A || B) (∅ : Set Formula)) ⊢ A' :=
        iff_mp h1w hA
      exact orI1 hA'
    -- case 2: assume B
    have caseB : insert B (insert (A || B) (∅ : Set Formula)) ⊢ A' || B' := by
      have h2w : insert B (insert (A || B) (∅ : Set Formula)) ⊢ (B ⇔ B') :=
        weakening h2 (Set.empty_subset _)
      have hB : insert B (insert (A || B) (∅ : Set Formula)) ⊢ B := by
        apply_ax
      have hB' : insert B (insert (A || B) (∅ : Set Formula)) ⊢ B' :=
        iff_mp h2w hB
      exact orI2 hB'
    exact orE hor caseA caseB
  · -- Goal: insert (A' || B') ∅ ⊢ A || B
    have hor : insert (A' || B') (∅ : Set Formula) ⊢ A' || B' := by
      apply_ax
    -- case 1: assume A'
    have caseA' : insert A' (insert (A' || B') (∅ : Set Formula)) ⊢ A || B := by
      have h1w : insert A' (insert (A' || B') (∅ : Set Formula)) ⊢ (A ⇔ A') :=
        weakening h1 (Set.empty_subset _)
      have hA' : insert A' (insert (A' || B') (∅ : Set Formula)) ⊢ A' := by
        apply_ax
      have hA : insert A' (insert (A' || B') (∅ : Set Formula)) ⊢ A :=
        iff_mpr h1w hA'
      exact orI1 hA
    -- case 2: assume B'
    have caseB' : insert B' (insert (A' || B') (∅ : Set Formula)) ⊢ A || B := by
      have h2w : insert B' (insert (A' || B') (∅ : Set Formula)) ⊢ (B ⇔ B') :=
        weakening h2 (Set.empty_subset _)
      have hB' : insert B' (insert (A' || B') (∅ : Set Formula)) ⊢ B' := by
        apply_ax
      have hB : insert B' (insert (A' || B') (∅ : Set Formula)) ⊢ B :=
        iff_mpr h2w hB'
      exact orI2 hB
    exact orE hor caseA' caseB'





theorem distrib_or_and {C D E : Formula} :
    Provable ((C || (D && E)) ⇔ ((C || D) && (C || E))) := by
  unfold Provable
  apply iffI
  · -- Goal: insert (C || (D && E)) ∅ ⊢ (C || D) && (C || E)
    have hor : insert (C || (D && E)) (∅ : Set Formula) ⊢ C || (D && E) := by
      apply_ax
    -- case 1: assume C
    have caseC : insert C (insert (C || (D && E)) (∅ : Set Formula)) ⊢ (C || D) && (C || E) := by
      have hC : insert C (insert (C || (D && E)) (∅ : Set Formula)) ⊢ C := by
        apply_ax
      have hCD : insert C (insert (C || (D && E)) (∅ : Set Formula)) ⊢ C || D :=
        orI1 hC
      have hCE : insert C (insert (C || (D && E)) (∅ : Set Formula)) ⊢ C || E :=
        orI1 hC
      exact andI hCD hCE
    -- case 2: assume D && E
    have caseDE : insert (D && E) (insert (C || (D && E)) (∅ : Set Formula)) ⊢ (C || D) && (C || E) := by
      have hDE : insert (D && E) (insert (C || (D && E)) (∅ : Set Formula)) ⊢ D && E := by
        apply_ax
      have hD : insert (D && E) (insert (C || (D && E)) (∅ : Set Formula)) ⊢ D :=
        andE1 hDE
      have hE : insert (D && E) (insert (C || (D && E)) (∅ : Set Formula)) ⊢ E :=
        andE2 hDE
      have hCD : insert (D && E) (insert (C || (D && E)) (∅ : Set Formula)) ⊢ C || D :=
        orI2 hD
      have hCE : insert (D && E) (insert (C || (D && E)) (∅ : Set Formula)) ⊢ C || E :=
        orI2 hE
      exact andI hCD hCE
    exact orE hor caseC caseDE
  · -- Goal: insert ((C || D) && (C || E)) ∅ ⊢ C || (D && E)
    have hand : insert ((C || D) && (C || E)) (∅ : Set Formula) ⊢ (C || D) && (C || E) := by
      apply_ax
    have hCD : insert ((C || D) && (C || E)) (∅ : Set Formula) ⊢ C || D :=
      andE1 hand
    -- case 1: assume C
    have caseC : insert C (insert ((C || D) && (C || E)) (∅ : Set Formula)) ⊢ C || (D && E) := by
      have hC : insert C (insert ((C || D) && (C || E)) (∅ : Set Formula)) ⊢ C := by
        apply_ax
      exact orI1 hC
    -- case 2: assume D, then split on C || E
    have caseD : insert D (insert ((C || D) && (C || E)) (∅ : Set Formula)) ⊢ C || (D && E) := by
      have hand' : insert D (insert ((C || D) && (C || E)) (∅ : Set Formula)) ⊢ (C || D) && (C || E) := by
        apply_ax
      have hD : insert D (insert ((C || D) && (C || E)) (∅ : Set Formula)) ⊢ D := by
        apply_ax
      have hCE : insert D (insert ((C || D) && (C || E)) (∅ : Set Formula)) ⊢ C || E :=
        andE2 hand'
      -- case 2a: assume C
      have caseDC : insert C (insert D (insert ((C || D) && (C || E)) (∅ : Set Formula))) ⊢ C || (D && E) := by
        have hC : insert C (insert D (insert ((C || D) && (C || E)) (∅ : Set Formula))) ⊢ C := by
          apply_ax
        exact orI1 hC
      -- case 2b: assume E
      have caseDE : insert E (insert D (insert ((C || D) && (C || E)) (∅ : Set Formula))) ⊢ C || (D && E) := by
        have hD2 : insert E (insert D (insert ((C || D) && (C || E)) (∅ : Set Formula))) ⊢ D := by
          apply_ax
        have hE : insert E (insert D (insert ((C || D) && (C || E)) (∅ : Set Formula))) ⊢ E := by
          apply_ax
        have hDE : insert E (insert D (insert ((C || D) && (C || E)) (∅ : Set Formula))) ⊢ D && E :=
          andI hD2 hE
        exact orI2 hDE
      exact orE hCE caseDC caseDE
    exact orE hCD caseC caseD









theorem distrib_and_or {C D E : Formula} :
    Provable (((D && E) || C) ⇔ ((D || C) && (E || C))) := by
  unfold Provable
  apply iffI
  · -- Goal: insert ((D && E) || C) ∅ ⊢ (D || C) && (E || C)
    have hor : insert ((D && E) || C) (∅ : Set Formula) ⊢ (D && E) || C := by
      apply_ax
    -- case 1: assume D && E
    have caseDE : insert (D && E) (insert ((D && E) || C) (∅ : Set Formula))
     ⊢ (D || C) && (E || C) := by
      have hDE : insert (D && E) (insert ((D && E) || C) (∅ : Set Formula)) ⊢ D && E := by
        apply_ax
      have hD : insert (D && E) (insert ((D && E) || C) (∅ : Set Formula)) ⊢ D :=
        andE1 hDE
      have hE : insert (D && E) (insert ((D && E) || C) (∅ : Set Formula)) ⊢ E :=
        andE2 hDE
      have hDC : insert (D && E) (insert ((D && E) || C) (∅ : Set Formula)) ⊢ D || C :=
        orI1 hD
      have hEC : insert (D && E) (insert ((D && E) || C) (∅ : Set Formula)) ⊢ E || C :=
        orI1 hE
      exact andI hDC hEC
    -- case 2: assume C
    have caseC : insert C (insert ((D && E) || C) (∅ : Set Formula))
    ⊢ (D || C) && (E || C) := by
      have hC : insert C (insert ((D && E) || C) (∅ : Set Formula)) ⊢ C := by
        apply_ax
      have hDC : insert C (insert ((D && E) || C) (∅ : Set Formula)) ⊢ D || C :=
        orI2 hC
      have hEC : insert C (insert ((D && E) || C) (∅ : Set Formula)) ⊢ E || C :=
        orI2 hC
      exact andI hDC hEC
    exact orE hor caseDE caseC
  · -- Goal: insert ((D || C) && (E || C)) ∅ ⊢ (D && E) || C
    have hand : insert ((D || C) && (E || C)) (∅ : Set Formula)
    ⊢ (D || C) && (E || C) := by
      apply_ax
    have hDC : insert ((D || C) && (E || C)) (∅ : Set Formula) ⊢ D || C :=
      andE1 hand
    -- case 1: assume D, then split on E || C
    have caseD : insert D (insert ((D || C) && (E || C)) (∅ : Set Formula))
     ⊢ (D && E) || C := by
      have hand' : insert D (insert ((D || C) && (E || C)) (∅ : Set Formula))
      ⊢ (D || C) && (E || C) := by
        apply_ax
      have hEC : insert D (insert ((D || C) && (E || C)) (∅ : Set Formula)) ⊢ E || C :=
        andE2 hand'
      -- case 1a: assume E
      have caseDE : insert E (insert D (insert ((D || C) && (E || C)) (∅ : Set Formula)))
       ⊢ (D && E) || C := by
        have hD : insert E (insert D (insert ((D || C) && (E || C)) (∅ : Set Formula)))
        ⊢ D := by
          apply_ax
        have hE : insert E (insert D (insert ((D || C) && (E || C)) (∅ : Set Formula))) ⊢ E := by
          apply_ax
        have hDE : insert E (insert D (insert ((D || C) && (E || C)) (∅ : Set Formula)))
        ⊢ D && E :=
          andI hD hE
        exact orI1 hDE
      -- case 1b: assume C
      have caseDC : insert C (insert D (insert ((D || C) && (E || C)) (∅ : Set Formula)))
       ⊢ (D && E) || C  := by
        have hC : insert C (insert D (insert ((D || C) && (E || C)) (∅ : Set Formula))) ⊢ C := by
          apply_ax
        exact orI2 hC
      exact orE hEC caseDE caseDC
    -- case 2: assume C
    have caseC : insert C (insert ((D || C) && (E || C)) (∅ : Set Formula)) ⊢ (D && E) || C := by
      have hC : insert C (insert ((D || C) && (E || C)) (∅ : Set Formula)) ⊢ C := by
        apply_ax
      exact orI2 hC
    exact orE hDC caseD caseC


theorem distribute_provable_correct (A B : Formula) : Provable ((A || B) ⇔ distribute A B) := by
  induction A, B using distribute.induct
  next B B1 B2 ih1 ih2 =>
      simp only [distribute]
      exact iff_trans distrib_and_or (iff_cong_and ih1 ih2)
  next A B1 B2 hA ih1 ih2 =>
      simp only [distribute]
      exact iff_trans distrib_or_and (iff_cong_and ih1 ih2)
  next A B hA hB =>
      simp only [distribute]
      exact iff_refl (A || B)




theorem cnf_provable_correct (A : Formula) : Provable (A ⇔ cnf A) := by
  induction A with
  | bot => exact iff_refl _

  | var p => exact iff_refl _

  | conj A B ihA ihB =>
      exact iff_cong_and ihA ihB

  | disj A B ihA ihB =>
      -- Step 1: replace A and B by their CNFs inside the disjunction
      have step1 : Provable ((A || B) ⇔ (cnf A || cnf B)) :=
        iff_cong_or ihA ihB

      -- Step 2: distribute the disjunction of the two CNFs
      have step2 := distribute_provable_correct (cnf A) (cnf B)
      -- step2 : Provable ((cnf A || cnf B) ⇔ distribute (cnf A) (cnf B))

      -- Step 3: chain the two equivalences
      have step3 := iff_trans step1 step2
      -- step3 : Provable ((A || B) ⇔ distribute (cnf A) (cnf B))

      -- Step 4: cnf (A || B) unfolds to distribute (cnf A) (cnf B), so this closes the goal
      exact step3

  | impl A B h1 h2 => exact iff_refl _

/-- **Lemma 5**, in the direction the completeness chain actually needs. -/

theorem provable_of_cnf_provable {A : Formula} (h : Provable (cnf A)) : Provable A := by
  unfold Provable at h ⊢
  exact iff_mpr (cnf_provable_correct A) h






-- ***************************** Lemma 6  ******************************************

theorem exfalso' {Γ : Set Formula} {A : Formula} (h : Γ ⊢ ⊥) : Γ ⊢ A :=
  botC (weakening h (Set.subset_insert _ _))



theorem demorgan_and_mp {A B : Formula} : Provable (~(A && B) ⇒ (~A || ~B)) := by
  unfold Provable
  apply impI
  apply botC
  have hA : insert (~(~A || ~B)) (insert (~(A && B)) (∅:Set Formula)) ⊢ A := by
    apply botC
    have hnA : insert (~A) (insert (~(~A || ~B)) (insert (~(A && B)) (∅ : Set Formula))) ⊢ ~A := by
      apply_ax
    have hor : insert (~A) (insert (~(~A || ~B)) (insert (~(A && B)) (∅ : Set Formula))) ⊢ ~A || ~B :=
      orI1 hnA
    have hnor : insert (~A) (insert (~(~A || ~B)) (insert (~(A && B)) (∅ : Set Formula))) ⊢ ~(~A || ~B) := by
      apply_ax
    exact impE hnor hor
  have hB : insert (~(~A|| ~B)) (insert (~(A && B)) (∅ : Set Formula)) ⊢ B := by
    apply botC
    have hnB : insert (~B) (insert (~(~A || ~B)) (insert (~(A && B)) (∅ : Set Formula))) ⊢ ~B := by
      apply_ax
    have hor : insert (~B) (insert (~(~A || ~B)) (insert (~(A && B)) (∅ : Set Formula))) ⊢ (~A || ~B) := by
      exact orI2 hnB
    have hnor : insert (~B) (insert (~(~A || ~B)) (insert (~(A && B)) (∅ : Set Formula))) ⊢ ~(~A || ~B) := by
      apply_ax
    exact impE hnor hor
  have h1 := andI hA hB
  apply impE (A := (A && B))
  . apply_ax
  . exact h1





theorem demorgan_and_mpr {A B : Formula} : Provable ((~A || ~B) ⇒ ~(A && B)) := by
  unfold Provable
  apply impI
  apply impI
  apply orE (A:= ~A) (B:= ~B)
  . apply_ax
  . apply impE (A:= A)
    . apply_ax
    . have h1 : insert (~A) (insert (A && B) (insert (~A || ~B) ∅)) ⊢ (A && B) := by
        apply_ax
      have h2 : insert (~A) (insert (A && B) (insert (~A || ~B) ∅)) ⊢ A := by
        exact andE1 h1
      exact h2
  . apply impE (A:= B)
    . apply_ax
    . have h1 : insert (~B) (insert (A && B) (insert (~A || ~B) ∅)) ⊢ (A && B) := by
        apply_ax
      have h2 : insert (~B) (insert (A && B) (insert (~A || ~B) ∅)) ⊢ B := by
        exact andE2 h1
      exact h2



/-

unfold Provable; apply iffI
  · exact impE (weakening demorgan_and_mp (Set.empty_subset _)) (by apply_ax)
  · exact impE (weakening demorgan_and_mpr (Set.empty_subset _)) (by apply_ax)


-/


theorem demorgan_and {A B : Formula} : Provable (~(A && B) ⇔ (~A || ~B)) := by
  unfold Provable
  apply iffI
  . have h1 : insert (~(A && B)) (∅ : Set Formula) ⊢
        (~(A && B)) ⇒ (~A || ~B) := by
      exact weakening (demorgan_and_mp  (A := A) (B := B)) (Set.empty_subset _)
    have h2 : insert (~(A && B)) (∅ : Set Formula) ⊢
        (~(A && B)) := by apply_ax
    exact impE h1 h2
  . have h1 : insert (~A || ~B) (∅ : Set Formula) ⊢
        (~A || ~B) ⇒  (~(A && B)):= by
      exact weakening (demorgan_and_mpr  (A := A) (B := B)) (Set.empty_subset _)
    have h2 : insert (~A || ~B) (∅ : Set Formula) ⊢
        (~A || ~B):= by apply_ax
    exact impE h1 h2





theorem demorgan_or_mp {A B : Formula} : Provable (~(A || B) ⇒ (~A && ~B)) := by
  unfold Provable
  apply impI
  apply andI
  . apply impI
    apply impE (by apply_ax)
    apply orI1
    apply_ax
  · apply impI
    apply impE (by apply_ax)
    apply orI2
    apply_ax




theorem demorgan_or_mpr {A B : Formula} : Provable ((~A && ~B) ⇒ ~(A || B)) := by
  unfold Provable
  apply impI
  apply impI
  apply orE (A := A) (B:= B)
  . apply_ax
  . apply impE (A:= A)
    . have h1 : insert A (insert (A || B) (insert (~A && ~B) ∅)) ⊢ (~A && ~B) := by
        apply_ax
      have h2 : insert A (insert (A || B) (insert (~A && ~B) ∅)) ⊢ A ⇒ ⊥ := by
        exact andE1 h1
      exact h2
    . apply_ax
  . apply impE (A:= B)
    . have h1 : insert B (insert (A || B) (insert (~A && ~B) ∅)) ⊢ (~A && ~B) := by
        apply_ax
      have h2 : insert B (insert (A || B) (insert (~A && ~B) ∅)) ⊢ B ⇒ ⊥ := by
        exact andE2 h1
      exact h2
    . apply_ax




theorem demorgan_or {A B : Formula} : Provable (~(A || B) ⇔ (~A && ~B)) := by
  unfold Provable
  apply iffI
  . have h1 : insert ~(A || B) (∅) ⊢ (~(A || B)) ⇒ (~A && ~B) := by
      apply weakening (demorgan_or_mp (A:= A) (B:= B)) (Set.empty_subset _)
    have h2 : insert ~(A || B) (∅) ⊢ (~(A || B)) := by apply_ax
    exact impE h1 h2
  . have h1 : insert (~A && ~B) (∅) ⊢ (~A && ~B) ⇒ ~(A || B) := by
      apply weakening (demorgan_or_mpr (A:= A) (B:= B)) (Set.empty_subset _)
    have h2 : insert (~A && ~B) (∅) ⊢ (~A && ~B):= by apply_ax
    exact impE h1 h2






theorem impl_iff_mp {A B : Formula} : Provable ((A ⇒ B) ⇒ (~A || B)) := by
  unfold Provable
  apply impI
  apply botC
  have hA : insert (~(~A || B)) (insert (A ⇒ B) (∅:Set Formula)) ⊢ A := by
    apply botC
    exact impE (by apply_ax) (orI1 (by apply_ax))
  have hB : insert (~(~A || B)) (insert (A ⇒ B) (∅:Set Formula)) ⊢ B := by
    apply impE (by apply_ax) hA
  exact impE (by apply_ax) (orI2 hB)




theorem impl_iff_mpr {A B : Formula} : Provable ((~A || B) ⇒ (A ⇒ B)) := by
  unfold Provable
  apply impI
  apply orE (A:= ~A) (B:= B)
  . apply_ax
  . apply impI
    apply botC
    apply impE (A:= A)
    . apply_ax
    . apply_ax
  . apply impI
    apply_ax




theorem impl_iff {A B : Formula} : Provable ((A ⇒ B) ⇔ (~A || B)) := by
  unfold Provable
  apply iffI
  . have h1 : insert (A ⇒ B) (∅ : Set Formula) ⊢
        (A ⇒ B) ⇒ (~A || B) := by
      exact weakening (impl_iff_mp (A := A) (B := B)) (Set.empty_subset _)
    have h2 : insert (A ⇒ B) (∅ : Set Formula) ⊢
        A ⇒ B := by apply_ax
    apply impE h1 h2
  . have h1 : insert (~A || B) (∅ : Set Formula) ⊢
        (~A || B) ⇒ (A ⇒ B) := by
      exact weakening (impl_iff_mpr (A := A) (B := B)) (Set.empty_subset _)
    have h2 : insert (~A || B) (∅ : Set Formula) ⊢
        ~A || B := by apply_ax
    exact impE h1 h2





theorem not_impl_mp {A B : Formula} : Provable (~(A ⇒ B) ⇒ (A && ~B)) := by
  unfold Provable
  apply impI
  apply andI
  . apply botC
    have hAB : insert (~A) (insert (~(A ⇒ B)) (∅:Set Formula)) ⊢ (A ⇒ B) := by
      apply impI
      apply botC
      apply impE (A:= A)
      . apply_ax
      . apply_ax
    exact impE (by apply_ax) hAB
  . apply impI
    have hAB : insert B (insert (~(A ⇒ B)) (∅:Set Formula)) ⊢ (A ⇒ B) := by
      apply impI
      apply_ax
    exact impE (by apply_ax) hAB




theorem not_impl_mpr {A B : Formula} : Provable ((A && ~B) ⇒ ~(A ⇒ B)) := by
  unfold Provable
  apply impI
  apply impI
  have h1 : insert (A ⇒ B) (insert (A && ~B) (∅:Set Formula)) ⊢ (A ⇒ B) := by apply_ax
  have h2 : insert (A ⇒ B) (insert (A && ~B) (∅:Set Formula)) ⊢ (A && ~B) := by apply_ax
  have h3 : insert (A ⇒ B) (insert (A && ~B) (∅:Set Formula)) ⊢ (A) := by
    exact andE1 h2
  have h4 : insert (A ⇒ B) (insert (A && ~B) (∅:Set Formula)) ⊢ (B) := by
    exact impE h1 h3
  have h5 : insert (A ⇒ B) (insert (A && ~B) (∅:Set Formula)) ⊢ (~B) := by
    exact andE2 h2
  exact impE h5 h4



theorem not_impl_iff {A B : Formula} : Provable (~(A ⇒ B) ⇔ (A && ~B)) := by
  unfold Provable
  apply iffI
  . have h1 : insert (~(A ⇒ B)) (∅ : Set Formula )  ⊢ (~(A ⇒ B)) ⇒ A && ~B := by
      apply (weakening not_impl_mp ) (Set.empty_subset _)
    have h2 : insert (~(A ⇒ B)) (∅ : Set Formula )  ⊢ (~(A ⇒ B)):= by apply_ax
    exact impE h1 h2
  . have h1 : insert (A && ~B ) (∅ : Set Formula )  ⊢ A && ~B  ⇒ (~(A ⇒ B)) := by
      apply (weakening not_impl_mpr ) (Set.empty_subset _)
    have h2 : insert (A && ~B) (∅ : Set Formula )  ⊢ (A && ~B):= by apply_ax
    exact impE h1 h2




theorem nnf_nnfNeg_provable_correct (A : Formula) :
    Provable (A ⇔ nnf A) ∧ Provable (~A ⇔ nnfNeg A) := by
  unfold Provable
  induction A with
  | bot =>
      constructor
      . apply iffI
        . apply_ax
        . simp [nnf]
          apply_ax
      . apply iffI
        . simp [nnfNeg]
          apply_ax
        . simp [nnfNeg]
          apply_ax

  | var p =>
      constructor
      . apply iffI
        . simp [nnf]
          apply_ax
        . simp [nnf]
          apply_ax
      . apply iffI
        . simp [nnfNeg]
          apply_ax
        . simp [nnfNeg]
          apply_ax

  | conj A B ihA ihB =>
      obtain ⟨ h1, h2 ⟩ := ihA
      obtain ⟨ h3, h4 ⟩ := ihB
      simp [nnf, nnfNeg]
      constructor
      . exact iff_cong_and h1 h3
      . have h5 : Provable ((~A || ~B) ⇔ (nnfNeg A || nnfNeg B)) := by
          exact iff_cong_or h2 h4
        exact iff_trans demorgan_and h5


  | disj A B ihA ihB =>
      obtain ⟨h1, h2⟩ := ihA
      obtain ⟨h3, h4⟩ := ihB
      simp only [nnf, nnfNeg]
      constructor
      . exact iff_cong_or h1 h3
      . have h5 : Provable ((~A && ~B) ⇔ (nnfNeg A && nnfNeg B)) := by
          exact iff_cong_and h2 h4
        exact iff_trans demorgan_or h5

  | impl A B ihA ihB =>
      obtain ⟨h1, h2⟩ := ihA
      obtain ⟨h3, h4⟩ := ihB
      simp only [nnf, nnfNeg]
      constructor
      . have h5 : Provable ((~A || B) ⇔ (nnfNeg A || nnf B)) := by
          exact iff_cong_or h2 h3
        have h6 : Provable ( (A ⇒ B)⇔ (~A || B)) := by
          exact impl_iff
        exact iff_trans h6 h5
      . have h5 : Provable ((A && ~B) ⇔ (nnf A && nnfNeg B)) := by
          exact iff_cong_and h1 h4
        have h6 : Provable ( ~(A ⇒ B)⇔ (A && ~B)) := by
          exact not_impl_iff
        exact iff_trans h6 h5



/-- **Lemma 6.** -/
theorem provable_of_nnf_provable {A : Formula} (h : Provable (nnf A)) : Provable A := by
  have h1:= (nnf_nnfNeg_provable_correct A).1
  unfold Provable at h h1 ⊢
  exact iff_mpr h1 h


-- ************************ completeness ***************************************

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




theorem completeness {A : Formula} (h : Valid A) : Provable A := by
  have h1 : Valid (nnf A) := valid_nnf h                                  -- Lemma 1: valid A → valid (nnf A)
  have h2 : Valid (cnf (nnf A)) := valid_cnf h1                           -- Lemma 2: valid (nnf A) → valid (cnf (nnf A))
  have hCNF : IsCNF (cnf (nnf A)) := (isCNF_cnf_nnf A).1                  -- helper: cnf (nnf A) is in CNF
  have h3 : ∀ {C}, IsClause C → IsConjunctOf C (cnf (nnf A)) → SyntacticallyValid C :=
    valid_syntacticallyValid h2                                           -- Lemma 3: valid CNF → every clause syntactically valid
  have h4 : Provable (cnf (nnf A)) :=
    provable_of_syntacticallyValid_cnf hCNF h3                           -- Lemma 4: all clauses syntactically valid → CNF provable
  have h5 : Provable (nnf A) := provable_of_cnf_provable h4               -- Lemma 5: Provable (cnf X) → Provable X
  have h6:= provable_of_nnf_provable h5                                   -- Lemma 6: Provable (nnf A) → Provable A
  exact h6



end ClassicalPropositionalLogic
