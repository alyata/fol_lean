import fol

-- example 1a: A language of natural numbers with the constant symbols `zero` and `one`
-- and the function symbols `succ` and `add`
inductive natFuncs : ℕ → Type
| zero : natFuncs 0
| one : natFuncs 0
| succ : natFuncs 1
| add : natFuncs 2

inductive natRels : ℕ → Type
| equals : natRels 2

def natLanguage : Language := ⟨natFuncs, natRels⟩
-- End Example

-- Example 1b: shorthand for each function/constant symbol in natLanguage of example 1a
def zero : FOLTerm natLanguage := FOLTerm.func natFuncs.zero fin.empty
def one : FOLTerm natLanguage := FOLTerm.func natFuncs.one fin.empty
def succ (arg : FOLTerm natLanguage) : FOLTerm natLanguage := 
FOLTerm.func natFuncs.succ (arg :: fin.empty)
def add (arg1 arg2 : FOLTerm natLanguage) : FOLTerm natLanguage := 
FOLTerm.func natFuncs.add (arg1 :: arg2 :: fin.empty)
def equ (arg1 arg2 : FOLTerm natLanguage) : FOLPred natLanguage := 
FOLPred.pred natRels.equals (arg1 :: arg2 :: fin.empty)
-- End Example

-- Example 2a: model for the natural number language of example 1a
def natFuncSemantics (n : ℕ) (c : natFuncs n) : (fin.vec n ℕ → ℕ) :=
match n, c with
| 0, natFuncs.zero := (λ_, 0)
| 0, natFuncs.one  := (λ_, 1)
| 1, natFuncs.succ := (λargs, args 0 + 1)
| 2, natFuncs.add  := (λargs, args 0 + args 1)
end

def natRelSemantics (n : ℕ) (c : natRels n) : (fin.vec n ℕ → Prop) :=
match n, c with
| 2, natRels.equals := (λargs, args 0 = args 1)
end

def natModel : Model natLanguage :=
{domain := ℕ, terms := natFuncSemantics, preds := natRelSemantics}
-- End Example

-- Example 2b: interpreting a ground term in the natural language using the natural model
def interpretNatTerm (t : FOLTerm natLanguage) : ℕ :=
termSemantics natModel (λi, nat.zero) t

#reduce interpretNatTerm $ succ (add one one)

example : interpretNatTerm (succ (add one one)) = 3 :=
rfl
-- End Example

-- Example 2c: interpreting a ground predicate and proving the predicate
def interpretNatPred (p : FOLPred natLanguage) : Prop :=
predSemantics natModel (λi, nat.zero) p

#reduce interpretNatPred $ equ one (succ zero)

example : interpretNatPred (equ one (succ zero)) ↔ (1 = 1) :=
iff.rfl

example : interpretNatPred (equ one (succ zero)) :=
rfl
-- End Example

-- Example 2d: interpreting some sentences and proving the sentences
def interpretNatFormula (f : FOLFormula natLanguage) : Prop :=
formulaSemantics natModel (λi, nat.zero) f

def natRefl : FOLFormula natLanguage := 
∀_(FOLFormula.pred $ equ (FOLTerm.var 0) (FOLTerm.var 0))

#reduce interpretNatFormula natRefl

example : interpretNatFormula natRefl :=
by {intro, exact rfl}

def natSymm : FOLFormula natLanguage := 
∀_∀_((FOLFormula.pred $ equ (FOLTerm.var 0) (FOLTerm.var 1))
     _→_(FOLFormula.pred $ equ (FOLTerm.var 1) (FOLTerm.var 0)))

#reduce interpretNatFormula natSymm

example : interpretNatFormula natSymm :=
begin
intros x y h,
exact h.symm
end
-- End Example