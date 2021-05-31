import utils.finvec

set_option pp.beta true

-- Syntax of First-Order Logic
structure Language : Type 1 :=
(functions : ℕ → Type) (relations : ℕ → Type)

-- First Order Terms
inductive FOLTerm (L : Language) : Type
| var : ℕ → FOLTerm
| func : ∀ {n : ℕ} (name : L.functions n) (args : fin.vec FOLTerm n), FOLTerm

constant isBoundedTerm : ∀{L : Language}, ℕ → FOLTerm L → Prop

axiom varisBoundedTerm {L : Language} {n k : ℕ} 
                      : k < n → isBoundedTerm n (FOLTerm.var k : FOLTerm L)

axiom funcisBoundedTerm {L : Language} {n k : ℕ} {name : L.functions k} 
                       {args : fin.vec (FOLTerm L) k}
                       : (∀{i : fin k}, (isBoundedTerm n (args i))) 
                         → isBoundedTerm n (FOLTerm.func name args)

-- First Order Formulas
inductive FOLPred (L : Language) : Type
| pred :  ∀ {n : ℕ} (name : L.relations n) (args : fin.vec (FOLTerm L) n), FOLPred

constant isBoundedPred : ∀{L : Language}, ℕ → FOLPred L → Prop

axiom predisBoundedPred {L : Language} {n k : ℕ} {name : L.relations k} 
                       {args : fin.vec (FOLTerm L) k}
                       : (∀{i : fin k}, (isBoundedTerm n (args i))) 
                         → isBoundedPred n (FOLPred.pred name args)

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

-- This says a formula has no free variables above n
inductive isBoundedFormula {L : Language} : ℕ → FOLFormula L → Prop
| bottom : ∀n,                        isBoundedFormula n (⨯ : FOLFormula L)
| top : ∀n,                           isBoundedFormula n (✓ : FOLFormula L)
| pred : ∀n {p : FOLPred L},        isBoundedPred n p 
                                    → isBoundedFormula n (FOLFormula.pred p)
| eq : ∀n {t₁ t₂ : FOLTerm L},       isBoundedTerm n t₁ ∧isBoundedTerm n t₂ 
                                    → isBoundedFormula n (t₁ _=_ t₂)
| and : ∀n {f₁ f₂ : FOLFormula L},   isBoundedFormula n f₁ → isBoundedFormula n f₂
                                    → isBoundedFormula n (f₁ _∧_ f₂)
| or : ∀n {f₁ f₂ : FOLFormula L},    isBoundedFormula n f₁ → isBoundedFormula n f₂ 
                                    → isBoundedFormula n (f₁ _∨_ f₂)
| imply : ∀n {f₁ f₂ : FOLFormula L}, isBoundedFormula n f₁ → isBoundedFormula n f₂ 
                                    → isBoundedFormula n (f₁ _→_ f₂)
| not : ∀n {f : FOLFormula L},      isBoundedFormula n f
                                    → isBoundedFormula n (!_ f)
| for_all : ∀n {f : FOLFormula L},  isBoundedFormula (n + 1) f
                                    → isBoundedFormula n (∀_ f)
| exist : ∀n {f : FOLFormula L},    isBoundedFormula (n + 1) f
                                    → isBoundedFormula n (∃_ f)

-- n is supposed to represent the number of free variables 
inductive FOLSentence (L : Language) : ℕ → Type
| bottom : ∀n, FOLSentence n
| top : ∀n, FOLSentence n
| pred : ∀n, FOLPred L → FOLSentence n
| eq : ∀n, FOLTerm L → FOLTerm L → FOLSentence n
| and : ∀{n}, FOLSentence n → FOLSentence n → FOLSentence n
| or : ∀{n}, FOLSentence n → FOLSentence n → FOLSentence n
| imply : ∀{n}, FOLSentence n → FOLSentence n → FOLSentence n
| not : ∀{n}, FOLSentence n → FOLSentence n
| for_all : ∀{n}, FOLSentence (n + 1) → FOLSentence n
| exist : ∀{n}, FOLSentence (n + 1) → FOLSentence n

-- Semantics of First-Order Logic

/- Given a language L, a model interprets:
  * each function symbol (with arity n) in L as a mapping U^n → U
  * each relation symbol (with arity n) in L as a proposition over n arguments from U
  where U is the domain of the model -/
structure Model (L : Language) :=
(domain : Type)
(terms : ∀ {n}, L.functions n → (fin.vec domain n → domain))
(preds : ∀ {n}, L.relations n → (fin.vec domain n → Prop)) 

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