#eval 42+19
#eval 42+19









#eval String.append "Hello, " "Lean!"


#eval String.append "great " (String.append "oak " "tree")






#eval String.append "A" (String.append "B" "C")

#eval String.append (String.append "A" "B") "C"

#eval if 3 == 3 then 5 else 7

#eval if 3 == 4 then "equal" else "not equal"


#check (1 - 2 : Int)

#check (0 - 0 : Int )

def hello := "Hello"

def lean : String := "Lean"
#eval String.append hello (String.append " " hello)

def add1 (n : Nat) : Nat := n + 1
#eval add1 9

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

#eval maximum (2) (4)
#eval maximum (5 + 8) (2 * 7)



-- ************************one function *******************************

def joinStringsWith (sep : String) (s1 : String) (s2 : String) : String :=
  s1 ++ sep ++ s2

#eval joinStringsWith ", " "one" "and another"

#check joinStringsWith

-- other **************************************************

def volume (h : Nat) (w : Nat) (d : Nat) : Nat :=
  h*w*d

#eval volume (2) (3) (4)

#check volume


/-








-/



-- ********************* structures *************************************************








structure Point where
  x : Float
  y : Float


def mul (p1 : Point) (p2: Point) : Point :=
  {x := p1.x *p2.x, y := p1.y * p2.y}

#eval mul { x:= 2.1,  y:= 2.1} { x:= 1.0 , y:= 1.0}


def origin : Point := { x := 1.0, y := 2.0 }
#eval origin

#eval origin.x
#eval origin.y

#check origin.x
#check origin.y

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }



def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }


structure Point3D where
  x : Float
  y : Float
  z : Float


def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }


def spaceBetween (before : String) (after : String) : String :=
  before ++ " " ++ after

#eval spaceBetween "hello" "world"


def volumeA (p1 : Point3D) : Float :=
   p1.x * p1.y * p1.z

#eval volumeA { x:= 2.0 , y := 2.0 , z := 2.0}



#check { x:= 2.0 , y := 2.0 , z := 2.0 : Point3D}



def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }

#eval zeroX { x:= 2.0 , y:=  3.0}


-- *************** 1.4.3 exerxise*******************

structure RectangularPrism where
  h : Float
  w : Float
  d : Float

def volumeB (p1 : RectangularPrism ) : Float :=
 p1.h * p1.w * p1.d

#eval volumeB { h := 2.0 , w:= 2.0 , d := 2.0}


structure Segment where
  x : Float
  y : Float

def length (p1: Segment) : Float :=
  p1.y - p1.x

#eval length { x:= 5.0, y := 10.0}



-- ********* Datatypes and Patterns **********

/-

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat


inductive Bool where
  | false : Bool
  | true : Bool

-/



def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false

#eval isZero 4


def pred (n : Nat) : Int :=
  match n with
  | Nat.zero => -1
  | Nat.succ k => k

#eval pred 0


def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

#eval even 7



def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops k)

#eval evenLoops 4





open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h1

  by_cases hp : p

  · have hqr := h1 hp
    cases hqr with
    | inl hq =>
        left
        intro h2
        exact hq

    | inr hr =>
        right
        intro h3
        exact hr

  · left
    intro hp'
    exact False.elim (hp hp')




example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h1
  by_cases hp : p

  · right
    intro hq
    exact h1 ⟨hp, hq⟩

  · left
    exact hp



example : ¬(p → q) → p ∧ ¬q := by
  intro h1
  constructor

  · by_cases hp : p
    · exact hp
    · exfalso
      apply h1
      intro hp'
      exact False.elim (hp hp')

  · intro hq
    apply h1
    intro hp
    exact hq



example : (p → q) → (¬p ∨ q) := by
  intro h1
  by_cases hp : p
  . have a1 := h1 hp
    apply Or.intro_right
    exact a1
  . apply Or.intro_left
    exact hp



example : (¬q → ¬p) → (p → q) := by
  intro h1 h2
  apply byContradiction
  intro h3
  have h4 := h1 h3
  exact h4 h2



example : p ∨ ¬p := by
  by_cases hp : p
  . apply Or.intro_left
    exact hp
  . apply Or.intro_right
    exact hp



example : (((p → q) → p) → p) := by
  intro h1

  by_cases hp : p

  · exact hp

  · apply h1
    intro hp'
    exact False.elim (hp hp')



example : (((p → q) → p) → p) := by
  intro h1
  by_cases hp : p
  . exact hp
  . apply h1
    intro h2
    apply byContradiction
    intro h3
    exact hp h2


-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro h1 h2
    apply h1
    exact And.left h2
    exact And.right h2
  . intro h1 h2 h3
    apply h1
    exact And.intro h2 h3




example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro h1
    constructor
    . intro h2
      apply h1
      exact Or.intro_left q h2
    . intro h2
      apply h1
      exact Or.intro_right p h2
  . intro h1 h2
    apply Or.elim h2
    . intro h3
      apply h1.left
      exact h3
    . intro h3
      apply h1.right
      exact h3



example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro h1
    by_cases hp : p
    . exfalso
      apply h1
      exact Or.intro_left q hp
    . constructor
      . exact hp
      . intro h2
        exfalso
        apply h1
        exact Or.intro_right p h2
  . intro h1 h2
    have a1 := And.left h1
    have a2 := And.right h1
    apply Or.elim h2
    . exact a1
    . exact a2

/-




-/

example : (p → q) → (¬q → ¬p) := by
  intro h1 h2 h3
  have a1 := h1 h3
  exact h2 a1


example : (¬p ∨ q) → (p → q) := by
  intro h1 h2
  apply Or.elim h1
  . intro h3
    apply byContradiction
    intro h4
    exact h3 h2
  . intro h3
    exact h3


example : p ∧ ¬q → ¬(p → q) := by
  intro h1
  have a1 := And.left h1
  have a2 := And.right h1
  intro h2
  have a3 := h2 a1
  exact a2 a3

example : ¬p → (p → q) := by
  intro h1
  intro h2
  apply byContradiction
  intro h3
  have a1 := h1 h2
  exact a1














-- ***************  FIRST ORDER LOGIC ******************

/-


-/



variable (U : Type)
variable (P : U → Prop)

example (y : U) (h : P y) : ∃ x, P x := by
  exact Exists.intro y h


variable (U : Type)
variable (P : U → Prop)
variable (Q : Prop)

example (h1 : ∃ x, P x) (h2 : ∀ x, P x → Q) : Q :=
Exists.elim h1
  (fun (y : U) (h : P y) ↦
  have h3 : P y → Q := h2 y
  show Q from h3 h)



example (h1 : ∃ x, P x) (h2 : ∀ x, P x → Q) : Q := by
  obtain ⟨y, h⟩ := h1
  have h3 : P y → Q := h2 y
  exact h3 h



 example (h1 : ∃ x, P x) (h2 : ∀ x, P x → Q) : Q := by
  apply Exists.elim h1
  intro y h
  have h3 : P y → Q := h2 y
  exact h3 h



variable (U : Type)
variable (A B : U → Prop)

example : (∃ x, A x ∧ B x) → ∃ x, A x :=
fun h1 : ∃ x, A x ∧ B x ↦
Exists.elim h1
  (fun y (h2 : A y ∧ B y) ↦
  have h3 : A y := And.left h2
  show ∃ x, A x from Exists.intro y h3)



example : (∃ x, A x ∧ B x) → ∃ x, A x := by
  intro h1
  apply Exists.elim h1
  intro y h
  have h3 : A y := And.left h
  exact Exists.intro y h3



example : (∃ x, A x ∨ B x) → (∃ x, A x) ∨ (∃ x, B x) :=
fun h1 : ∃ x, A x ∨ B x ↦
Exists.elim h1 $
fun y (h2 : A y ∨ B y) ↦
Or.elim h2
  (fun h3 : A y ↦
    have h4 : ∃ x, A x := Exists.intro y h3
    show (∃ x, A x) ∨ (∃ x, B x) from Or.inl h4)
  (fun h3 : B y ↦
    have h4 : ∃ x, B x := Exists.intro y h3
    show (∃ x, A x) ∨ (∃ x, B x) from Or.inr h4)



example : (∃ x, A x ∨ B x) → (∃ x, A x) ∨ (∃ x, B x) := by
  intro h1
  apply Exists.elim h1
  intro y h2
  apply Or.elim h2
  . intro h3
    exact Or.inl (Exists.intro y h3)
  . intro h3
    exact Or.inr (Exists.intro y h3)



example : (∀ x, A x → ¬ B x) → ¬ ∃ x, A x ∧ B x :=
fun h1 : ∀ x, A x → ¬ B x ↦
fun h2 : ∃ x, A x ∧ B x ↦
Exists.elim h2 $
fun x (h3 : A x ∧ B x) ↦
have h4 : A x := And.left h3
have h5 : B x := And.right h3
have h6 : ¬ B x := h1 x h4
show False from h6 h5




example : (∀ x, A x → ¬ B x) → ¬ ∃ x, A x ∧ B x := by
  intro h1
  intro h2
  apply Exists.elim h2
  intro y h3
  have h4 : A y := And.left h3
  have h5 : B y := And.right h3
  have h6 : ¬ B y := h1 y h4
  exact h6 h5




variable (U : Type)
variable (u : U)
variable (P : Prop)

example : (∃x : U, P) ↔ P :=
Iff.intro
  (fun h1 : ∃x, P ↦
    Exists.elim h1 $
    fun x (h2 : P) ↦
    h2)
  (fun h1 : P ↦
    ⟨u, h1⟩)



example : (∃x : U, P) ↔ P := by
  constructor
  . intro h1
    apply Exists.elim h1
    intro y h2
    exact h2
  . intro h1
    apply Exists.intro
    exact h1
    exact u


example : x = x := by rfl

example : y = x → y = z → x = z := by
intro h1 h2
rw [h1] at h2
exact h2



example (h1 : ∀ x, A x → B x) (h2 : ∀ x, A x) : ∀ x, B x := by
  intro y
  apply h1
  apply h2



section
  variable (U : Type)
  variable (A B : U → Prop)

  example : (∀ x, A x ∧ B x) → ∀ x, A x := by
  intro h1 y
  apply And.left (h1 y)

end



section
  variable (U : Type)
  variable (A B C : U → Prop)

  variable (h1 : ∀ x, A x ∨ B x)
  variable (h2 : ∀ x, A x → C x)
  variable (h3 : ∀ x, B x → C x)

  example : ∀ x, C x := by
    intro y
    apply Or.elim (h1 y)
    . intro h4
      exact h2 y h4
    . intro h4
      exact h3 y h4



end


open Classical   -- not needed, but you can use it

-- This is an exercise from Chapter 4. Use it as an axiom here.
axiom not_iff_not_self (P : Prop) : ¬ (P ↔ ¬ P)

example (Q : Prop) : ¬ (Q ↔ ¬ Q) :=
not_iff_not_self Q

section
  variable (Person : Type)
  variable (shaves : Person → Person → Prop)
  variable (barber : Person)
  variable (h : ∀ x, shaves barber x ↔ ¬ shaves x x)

  -- Show the following:
  example : False := by
    have h1 := h barber
    have h2 := not_iff_not_self (shaves barber barber)
    exact h2 h1


end


  variable (U : Type)
  variable (A B : U → Prop)

  example : (∃ x, A x) → ∃ x, A x ∨ B x := by
    intro h1
    apply Exists.elim h1
    intro x hA
    apply Exists.intro x
    exact Or.inl hA




section
  variable (U : Type)
  variable (A B : U → Prop)

  variable (h1 : ∀ x, A x → B x)
  variable (h2 : ∃ x, A x)

  example : ∃ x, B x := by
    apply Exists.elim h2
    intro x h3
    apply Exists.intro x
    exact h1 x h3



end


variable (U : Type)
variable (A B C : U → Prop)

example (h1 : ∃ x, A x ∧ B x) (h2 : ∀ x, B x → C x) :
    ∃ x, A x ∧ C x := by
  apply Exists.elim h1
  intro x hx
  have a1 : B x := And.right hx
  have a2 : C x := h2 x a1
  have a3 : A x := And.left hx
  apply Exists.intro x
  exact And.intro a3 a2


variable (U : Type)
variable (A B C : U → Prop)

example : (¬ ∃ x, A x) → ∀ x, ¬ A x := by
  intro h1 x h2
  exact h1 (Exists.intro x h2)



example : (∀ x, ¬ A x) → ¬ ∃ x, A x := by
  intro h1 h2
  apply Exists.elim h2
  intro x hx
  exact h1 x hx


variable (U : Type)
variable (R : U → U → Prop)

example : (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y := by
  intro h1
  apply Exists.elim h1
  intro x hx
  intro y
  apply Exists.intro x
  exact hx y



theorem foo {A : Type} {a b c : A} : a = b → c = b → a = c := by
  intro h1 h2
  rw[h1]
  exact Eq.symm h2


-- notice that you can now use foo as a rule. The curly braces mean that
-- you do not have to give A, a, b, or c

section
  variable (A : Type)
  variable (a b c : A)

  example (h1 : a = b) (h2 : c = b) : a = c :=
  foo h1 h2
end

section
  variable {A : Type}
  variable {a b c : A}

  -- replace the sorry with a proof, using foo and rfl, without using eq.symm.
  theorem my_symm (h : b = a) : a = b := by
    exact Eq.symm h

  -- now use foo and my_symm to prove transitivity
  theorem my_trans (h1 : a = b) (h2 : b = c) : a = c := by
    rw[h1]
    exact h2
end


