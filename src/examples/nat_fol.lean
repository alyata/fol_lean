import fol

set_option pp.beta true

namespace fol_nat

open fol

-- example 1a: A language of natural numbers with the constant symbols `zero` and `one`
-- and the function symbols `succ` and `add`
inductive funcs : ℕ → Type
| zero : funcs 0
| one : funcs 0
| succ : funcs 1
| add : funcs 2

inductive preds : ℕ → Type
| equals : preds 2

def L : language := ⟨funcs, preds⟩
-- End Example

-- Example 1b: shorthand for each function/constant symbol in L of example 1a
def zero : term L := term.func funcs.zero fin.empty
def one : term L := term.func funcs.one fin.empty
def succ (arg : term L) : term L := 
term.func funcs.succ (arg :: fin.empty)
def add (arg1 arg2 : term L) : term L := 
term.func funcs.add (arg1 :: arg2 :: fin.empty)
def equ (arg1 arg2 : term L) : atom L := 
atom.atom preds.equals (arg1 :: arg2 :: fin.empty)
-- End Example

-- Example 2a: model for the natural number language of example 1a
def interpret_func (n : ℕ) (c : funcs n) : (fin.vec n ℕ → ℕ) :=
match n, c with
| 0, funcs.zero := (λ_, 0)
| 0, funcs.one  := (λ_, 1)
| 1, funcs.succ := (λargs, args 0 + 1)
| 2, funcs.add  := (λargs, args 0 + args 1)
end

def interpret_pred (n : ℕ) (c : preds n) : (fin.vec n ℕ → Prop) :=
match n, c with
| 2, preds.equals := (λargs, args 0 = args 1)
end

def M : model L :=
{domain := ℕ, funcs := interpret_func, preds := interpret_pred}
-- End Example

-- Example 2b: interpreting a ground term in the natural language using the natural model
def interpret_term (t : term L) : ℕ :=
term.valuation M (λi, nat.zero) t

#reduce interpret_term $ succ (add one one)

example : interpret_term (succ (add one one)) = 3 :=
rfl
-- End Example

-- Example 2c: interpreting a ground predicate and proving the predicate
def interpret_atom (p : atom L) : Prop :=
atom.valuation M (λi, nat.zero) p

#reduce interpret_atom $ equ one (succ zero)

example : interpret_atom (equ one (succ zero)) ↔ (1 = 1) :=
iff.rfl

example : interpret_atom (equ one (succ zero)) :=
rfl
-- End Example

-- Example 2d: interpreting some sentences and proving the sentences
def interpret_formula (f : formula L) : Prop :=
formula.valuation M (λi, nat.zero) f

def reflexivity : formula L := 
∀_(A_ (equ (term.var 0) (term.var 0)))

#reduce interpret_formula reflexivity

example : interpret_formula reflexivity :=
by {intro, exact rfl}

def symmetry : formula L := 
∀_∀_((A_ (equ (term.var 0) (term.var 1)))
     _→_(A_ (equ (term.var 1) (term.var 0))))

#reduce interpret_formula symmetry

example : interpret_formula symmetry :=
begin
intros x y h,
exact h.symm
end

-- End Example

end fol_nat