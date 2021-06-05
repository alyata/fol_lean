import data.fin

namespace fin

def to_nat {n : ℕ} : fin n → ℕ := (fin.fin_to_nat n).coe

def vec (n : ℕ) (U : Type) : Type := fin n → U
def dvec (n : ℕ) (U : fin n → Type) : Type := ∀(k : fin n), U k

def vec_to_dvec {n : ℕ} {U : Type} (v : vec n U) : dvec n (λ_, U) := v

def map {U V: Type} {n : ℕ} (f : U → V) (v : vec n U) : vec n V :=
λi, f (v i)

def max' {n : ℕ} (vec : vec (n + 1) ℕ) : fin (n + 1) → ℕ :=
λfn, subtype.rec_on fn 
(λm p, nat.rec_on m
  (vec 0) -- Base Case
  (λk ih, max (vec (k + 1)) ih) -- Inductive Case
)
--The more readable version of max' but that causes timeouts when used for #reduce computation
--| ⟨0, _⟩      := vec 0
--| ⟨k + 1, hk⟩ := max (vec (k + 1)) (max' ⟨k, k.lt_succ_self.trans hk⟩)

def max {n : ℕ} : (vec n ℕ) → ℕ :=
match n with
| 0       := λv, 0
| (k + 1) := λv, @max' k v (last k)
end

def unzip_left {n : ℕ} {U : Type} {V : U → Type} (v : vec n (Σx : U, V x)) 
              : vec n U :=
λi, (v i).fst

def unzip_right {n : ℕ} {U : Type} {V : U → Type} (v : vec n (Σx : U, V x)) 
                    : dvec n (V ∘ (unzip_left v)) :=
λi, (v i).snd

def empty {U : Type} : vec 0 U := (λi, i.elim0)

infixr `::` := cons

end fin