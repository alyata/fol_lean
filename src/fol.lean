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
prefix `P_` : max := FOLFormula.pred
infixr `_=_`: 88 := FOLFormula.eq
infixr `_∧_`: 60 := FOLFormula.and
infixr `_∨_`: 61 := FOLFormula.or
infixr `_→_`: 62 := FOLFormula.imply
prefix `!_`: max := FOLFormula.not
prefix `∀_`: 110 := FOLFormula.for_all
prefix `∃_`: 110 := FOLFormula.exist

inductive FOLBoundedT (L : Language) : ℕ → Type
| var  : ∀(i : ℕ), FOLBoundedT (i + 1)
| func : ∀{n : ℕ} (name : L.functions n) {f : fin n → ℕ}
         (args : fin.dvec n (λi, FOLBoundedT (f i))), 
         FOLBoundedT (fin.max f)

def FOLClosedTerm (L : Language) : Type := FOLBoundedT L 0

-- i.e. Given a FOLTerm, return a bound value k and a term bounded by k
def FOLTerm.toBoundedT {L : Language} : FOLTerm L → Σ{k : ℕ}, FOLBoundedT L k
| (FOLTerm.var i) := ⟨i + 1, FOLBoundedT.var i⟩
| (FOLTerm.func name args)
  := let bArgs := (λi, (args i).toBoundedT) 
     in ⟨fin.max $ fin.unzip_left bArgs, FOLBoundedT.func name (fin.unzip_right bArgs)⟩

inductive FOLBoundedP (L : Language) : ℕ → Type
| pred : ∀{n : ℕ} (name : L.relations n) {f : fin n → ℕ}
         (args : fin.dvec n (λi, FOLBoundedT L (f i))), 
         FOLBoundedP (fin.max f)

def FOLClosedPred (L : Language) : Type := FOLBoundedP L 0

def FOLPred.toBoundedP {L : Language} : FOLPred L → Σ{k : ℕ}, FOLBoundedP L k
| (FOLPred.pred name args) := 
  let bArgs := (λi, (args i).toBoundedT) 
  in  ⟨fin.max $ fin.unzip_left bArgs, FOLBoundedP.pred name (fin.unzip_right bArgs)⟩

-- n is supposed to represent an upper bound of free variables
-- i.e. all free variables that occur must be strictly below n
inductive FOLBoundedF (L : Language) : ℕ → Type
| bottom : FOLBoundedF 0
| top : FOLBoundedF 0
| pred : ∀{n}, FOLBoundedP L n → FOLBoundedF n
| eq : ∀{n m}, FOLBoundedT L n → FOLBoundedT L m → FOLBoundedF (max n m)
| and : ∀{n m}, FOLBoundedF n → FOLBoundedF m → FOLBoundedF (max n m)
| or : ∀{n m}, FOLBoundedF n → FOLBoundedF m → FOLBoundedF (max n m)
| imply : ∀{n m}, FOLBoundedF n → FOLBoundedF m → FOLBoundedF (max n m)
| not : ∀{n}, FOLBoundedF n → FOLBoundedF n
| for_all : ∀{n}, FOLBoundedF n → FOLBoundedF (n - 1)
| exist : ∀{n}, FOLBoundedF n → FOLBoundedF (n - 1)

def FOLFormula.toBoundedF {L : Language} : FOLFormula L → Σk : ℕ, FOLBoundedF L k
| ⨯ := ⟨0, FOLBoundedF.bottom⟩
| ✓ := ⟨0, FOLBoundedF.top⟩
| (FOLFormula.pred p) := p.toBoundedP.map id (@FOLBoundedF.pred L)
| (t₁ _=_ t₂) := 
  let bt₁ := t₁.toBoundedT, bt₂ := t₂.toBoundedT
  in  ⟨max bt₁.fst bt₂.fst, FOLBoundedF.eq bt₁.snd bt₂.snd⟩
| (f₁ _∧_ f₂) :=
  let bf₁ := f₁.toBoundedF, bf₂ := f₂.toBoundedF
  in  ⟨max bf₁.fst bf₂.fst, FOLBoundedF.and bf₁.snd bf₂.snd⟩
| (f₁ _∨_ f₂) :=
  let bf₁ := f₁.toBoundedF, bf₂ := f₂.toBoundedF
  in  ⟨max bf₁.fst bf₂.fst, FOLBoundedF.or bf₁.snd bf₂.snd⟩
| (f₁ _→_ f₂) :=
  let bf₁ := f₁.toBoundedF, bf₂ := f₂.toBoundedF
  in  ⟨max bf₁.fst bf₂.fst, FOLBoundedF.imply bf₁.snd bf₂.snd⟩
| (!_ f) := f.toBoundedF.map id (@FOLBoundedF.not L)
| (∀_ f) := f.toBoundedF.map (λn, n - 1) (@FOLBoundedF.for_all L)
| (∃_ f) := f.toBoundedF.map (λn, n - 1) (@FOLBoundedF.exist L)

def FOLSentence (L : Language) : Type := FOLBoundedF L 0

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