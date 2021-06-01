import utils.finvec

set_option pp.beta true

-- Syntax of First-Order Logic
structure Language : Type 1 :=
(functions : ℕ → Type) (relations : ℕ → Type)

-- First Order Terms
inductive FOLTerm (L : Language) : Type
| var  : ℕ → FOLTerm
| func : ∀ {n : ℕ} (name : L.functions n) (args : fin.vec n FOLTerm), FOLTerm

-- First Order Formulas
inductive FOLPred (L : Language) : Type
| pred :  ∀ {n : ℕ} (name : L.relations n) (args : fin.vec n (FOLTerm L)), FOLPred

inductive FOLFormula (L : Language) : Type
| bottom : FOLFormula
| top : FOLFormula
| pred : FOLPred L → FOLFormula
| eq : FOLTerm L → FOLTerm L → FOLFormula
| and : FOLFormula → FOLFormula → FOLFormula
| or : FOLFormula → FOLFormula → FOLFormula
| imply : FOLFormula → FOLFormula → FOLFormula
| not : FOLFormula → FOLFormula
| for_all : FOLFormula → FOLFormula
| exist : FOLFormula → FOLFormula

notation `⨯` := FOLFormula.bottom -- \cross
notation `✓` := FOLFormula.top -- \check
infixr `_=_`: 88 := FOLFormula.eq
infixr `_∧_`: 60 := FOLFormula.and
infixr `_∨_`: 61 := FOLFormula.or
infixr `_→_`: 62 := FOLFormula.imply
prefix `!_`: max := FOLFormula.not
prefix `∀_`: 110 := FOLFormula.for_all
prefix `∃_`: 110 := FOLFormula.exist

inductive FOLBoundedT (L : Language) : ℕ → Type
| var  : ∀{b : ℕ}, ℕ → FOLBoundedT b
| func : ∀{b n : ℕ} (name : L.functions n) (args : fin.dvec n (FOLBoundedT)), 
         FOLBoundedT b

inductive FOLBoundedP (L : Language) : ℕ → Type
| pred : ∀ {b n : ℕ} (name : L.relations n) (args : fin.dvec n (FOLBoundedT L)), 
         FOLBoundedP b

-- n is supposed to represent an upper bound of free variables
-- i.e. all free variables that occur must be strictly below n
inductive FOLBoundedF (L : Language) : ℕ → Type
| bottom : ∀n, FOLBoundedF n
| top : ∀n, FOLBoundedF n
| pred : ∀n, FOLBoundedP L n → FOLBoundedF n
| eq : ∀n, FOLTerm L → FOLTerm L → FOLBoundedF n
| and : ∀{n}, FOLBoundedF n → FOLBoundedF n → FOLBoundedF n
| or : ∀{n}, FOLBoundedF n → FOLBoundedF n → FOLBoundedF n
| imply : ∀{n}, FOLBoundedF n → FOLBoundedF n → FOLBoundedF n
| not : ∀{n}, FOLBoundedF n → FOLBoundedF n
| for_all : ∀{n}, FOLBoundedF (n + 1) → FOLBoundedF n
| exist : ∀{n}, FOLBoundedF (n + 1) → FOLBoundedF n

-- Semantics of First-Order Logic

/- Given a language L, a model interprets:
  * each function symbol (with arity n) in L as a mapping U^n → U
  * each relation symbol (with arity n) in L as a proposition over n arguments from U
  where U is the domain of the model -/
structure Model (L : Language) :=
(domain : Type)
(terms : ∀ {n}, L.functions n → (fin.vec n domain → domain))
(preds : ∀ {n}, L.relations n → (fin.vec n domain → Prop)) 

def termSemantics {L : Language} (m : Model L)
                  (varSemantics : ℕ → m.domain) : FOLTerm L → m.domain
| (FOLTerm.var n)           := varSemantics n
| (FOLTerm.func name args) := (m.terms name) (λi, termSemantics (args i))

def predSemantics {L : Language} (m : Model L)
                  (varSemantics : ℕ → m.domain) : FOLPred L → Prop
| (FOLPred.pred name args) := (m.preds name) (λi, (termSemantics m varSemantics) (args i))

def shift {L : Language} {m : Model L} 
          (varSemantics : ℕ → m.domain) (x : m.domain) : (ℕ → m.domain)
| 0       := x
| (n + 1) := varSemantics n

def formulaSemantics {L : Language} (m : Model L) :
                     (ℕ → m.domain) → FOLFormula L → Prop
| vars ⨯ := false
| vars ✓ := true
| vars (FOLFormula.pred p) := predSemantics m vars p
| vars (t₁ _=_ t₂) := (termSemantics m vars t₁) = (termSemantics m vars t₂)
| vars (f₁ _∧_ f₂) := (formulaSemantics vars f₁) ∧ (formulaSemantics vars f₂)
| vars (f₁ _∨_  f₂) := (formulaSemantics vars f₁) ∧ (formulaSemantics vars f₂)
| vars (f₁ _→_ f₂) := (formulaSemantics vars f₁) → (formulaSemantics vars f₂)
| vars (!_f) := ¬ (formulaSemantics vars f)
| vars (∀_f) := ∀(x : m.domain), formulaSemantics (shift vars x) f
| vars (∃_f) := ∃(x : m.domain), formulaSemantics (shift vars x) f