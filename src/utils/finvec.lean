import data.fin

def fin.to_nat {n : ℕ} : fin n → ℕ := (fin.fin_to_nat n).coe

def fin.vec (n : ℕ) (U : Type) : Type := fin n → U
def fin.dvec (n : ℕ) (U : ℕ → Type) : Type := ∀(k : fin n), U (fin.to_nat k)

def fin.vec_to_dvec {n : ℕ} {U : Type} (v : fin.vec n U) : fin.dvec n (λ_, U) := v

def fin.map {U V: Type} {n : ℕ} (f : U → V) (v : fin.vec n U) : fin.vec n V :=
λi, f (v i)

def fin.empty {U : Type} : fin.vec 0 U := (λi, i.elim0)

infixr `::` := fin.cons