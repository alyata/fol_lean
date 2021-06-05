import utils.finvec

set_option pp.beta true

namespace fol

-- Syntax of First-Order Logic
structure language : Type 1 :=
(funcs : ℕ → Type) (preds : ℕ → Type)

-- First Order Terms
inductive term (L : language) : Type
| var  : ℕ → term
| func : ∀ {n : ℕ} (name : L.funcs n) (args : fin.vec n term), term

-- First Order Formulas
inductive atom (L : language) : Type
| atom : ∀ {n : ℕ} (name : L.preds n) (args : fin.vec n (term L)), atom

inductive formula (L : language) : Type
| bottom  : formula
| top     : formula
| atom    : atom L → formula
| eq      : term L → term L → formula
| and     : formula → formula → formula
| or      : formula → formula → formula
| imply   : formula → formula → formula
| not     : formula → formula
| for_all : formula → formula
| exist   : formula → formula

notation `⨯`      := formula.bottom -- \cross
notation `✓`      := formula.top -- \check
prefix `A_` : max := formula.atom
infixr `_=_`: 88  := formula.eq
infixr `_∧_`: 60  := formula.and
infixr `_∨_`: 61  := formula.or
infixr `_→_`: 62  := formula.imply
prefix `!_`: max  := formula.not
prefix `∀_`: 110  := formula.for_all
prefix `∃_`: 110  := formula.exist

-- bounded representations of terms and formulas such that the type carries
-- a parameter n such that all *free* variables occuring in the term/formula
-- are less than n.

inductive bounded_term (L : language) : ℕ → Type
| var  : ∀(i : ℕ), bounded_term (i + 1)
| func : ∀{n : ℕ} {f : fin n → ℕ} (name : L.funcs n)
         (args : fin.dvec n (λi, bounded_term (f i))), 
         bounded_term (fin.max f)

def closed_term (L : language) : Type := bounded_term L 0

-- Given an unbounded term, return a bound value k and a term bounded by k
def term.to_bounded {L : language} : term L → Σ{k : ℕ}, bounded_term L k
| (term.var i) := ⟨i + 1, bounded_term.var i⟩
| (term.func name args) :=
  let b_args := (λi, (args i).to_bounded) 
  in ⟨fin.max $ fin.unzip_left b_args, bounded_term.func name (fin.unzip_right b_args)⟩

inductive bounded_atom (L : language) : ℕ → Type
| atom : ∀{n : ℕ} {f : fin n → ℕ} (name : L.preds n)
         (args : fin.dvec n (λi, bounded_term L (f i))), 
         bounded_atom (fin.max f)

def closed_atom (L : language) : Type := bounded_atom L 0

def atom.to_bounded {L : language} : atom L → Σ{k : ℕ}, bounded_atom L k
| (atom.atom name args) := 
  let b_args := (λi, (args i).to_bounded)
  in  ⟨fin.max $ fin.unzip_left b_args, bounded_atom.atom name (fin.unzip_right b_args)⟩

inductive bounded_formula (L : language) : ℕ → Type
| bottom  : bounded_formula 0
| top     : bounded_formula 0
| atom    : ∀{n}, bounded_atom L n → bounded_formula n
| eq      : ∀{n m}, bounded_term L n → bounded_term L m → bounded_formula (max n m)
| and     : ∀{n m}, bounded_formula n → bounded_formula m → bounded_formula (max n m)
| or      : ∀{n m}, bounded_formula n → bounded_formula m → bounded_formula (max n m)
| imply   : ∀{n m}, bounded_formula n → bounded_formula m → bounded_formula (max n m)
| not     : ∀{n}, bounded_formula n → bounded_formula n
| for_all : ∀{n}, bounded_formula n → bounded_formula (n - 1)
| exist   : ∀{n}, bounded_formula n → bounded_formula (n - 1)

notation `:⨯`      := bounded_formula.bottom -- \cross
notation `:✓`      := bounded_formula.top -- \check
prefix `:A_` : max := bounded_formula.atom
infixr `_:=_`: 88  := bounded_formula.eq
infixr `_:∧_`: 60  := bounded_formula.and
infixr `_:∨_`: 61  := bounded_formula.or
infixr `_:→_`: 62  := bounded_formula.imply
prefix `:!_`: max  := bounded_formula.not
prefix `:∀_`: 110  := bounded_formula.for_all
prefix `:∃_`: 110  := bounded_formula.exist

def formula.to_bounded {L : language} : formula L → Σk : ℕ, bounded_formula L k
| ⨯                   := ⟨0, :⨯⟩
| ✓                   := ⟨0, :✓⟩
| (formula.atom p)    := let bp := p.to_bounded in ⟨bp.fst, :A_ bp.snd⟩
| (t₁ _=_ t₂)          := let bt₁ := t₁.to_bounded, bt₂ := t₂.to_bounded
                         in  ⟨max bt₁.fst bt₂.fst, bt₁.snd _:=_ bt₂.snd⟩
| (f₁ _∧_ f₂)          := let bf₁ := f₁.to_bounded, bf₂ := f₂.to_bounded
                         in  ⟨max bf₁.fst bf₂.fst, bf₁.snd _:∧_ bf₂.snd⟩
| (f₁ _∨_ f₂)          := let bf₁ := f₁.to_bounded, bf₂ := f₂.to_bounded
                         in  ⟨max bf₁.fst bf₂.fst, bf₁.snd _:∨_ bf₂.snd⟩
| (f₁ _→_ f₂)          := let bf₁ := f₁.to_bounded, bf₂ := f₂.to_bounded
                         in  ⟨max bf₁.fst bf₂.fst, bf₁.snd _:→_ bf₂.snd⟩
| (!_ f)              := let bf := f.to_bounded in ⟨bf.fst, :!_ bf.snd⟩
| (∀_ f)              := let bf := f.to_bounded in ⟨bf.fst - 1, :∀_ bf.snd⟩
| (∃_ f)              := let bf := f.to_bounded in ⟨bf.fst - 1, :∃_ bf.snd⟩

def sentence (L : language) : Type := bounded_formula L 0

-- Semantics of First-Order Logic

/- Given a language L, a model interprets:
  * each function symbol (with arity n) in L as a mapping U^n → U
  * each relation symbol (with arity n) in L as a proposition over n arguments from U
  where U is the domain of the model -/
structure model (L : language) :=
(domain : Type)
(funcs : ∀ {n}, L.funcs n → (fin.vec n domain → domain))
(preds : ∀ {n}, L.preds n → (fin.vec n domain → Prop)) 

def term.valuation {L : language} (m : model L)
                  (var_assignment : ℕ → m.domain) : term L → m.domain
| (term.var n)          := var_assignment n
| (term.func name args) := (m.funcs name) (λi, term.valuation (args i))

def atom.valuation {L : language} (m : model L)
                  (var_assignment : ℕ → m.domain) : atom L → Prop
| (atom.atom name args) := (m.preds name) (λi, (term.valuation m var_assignment) (args i))

def shift {L : language} {m : model L} 
          (var_assignment : ℕ → m.domain) (x : m.domain) : (ℕ → m.domain)
| 0       := x
| (n + 1) := var_assignment n

def formula.valuation {L : language} (m : model L) :
                     (ℕ → m.domain) → formula L → Prop
| vars ⨯ := false
| vars ✓ := true
| vars (formula.atom p) := atom.valuation m vars p
| vars (t₁ _=_ t₂) := (term.valuation m vars t₁) = (term.valuation m vars t₂)
| vars (f₁ _∧_ f₂) := (formula.valuation vars f₁) ∧ (formula.valuation vars f₂)
| vars (f₁ _∨_  f₂) := (formula.valuation vars f₁) ∧ (formula.valuation vars f₂)
| vars (f₁ _→_ f₂) := (formula.valuation vars f₁) → (formula.valuation vars f₂)
| vars (!_f) := ¬ (formula.valuation vars f)
| vars (∀_f) := ∀(x : m.domain), formula.valuation (shift vars x) f
| vars (∃_f) := ∃(x : m.domain), formula.valuation (shift vars x) f

end fol