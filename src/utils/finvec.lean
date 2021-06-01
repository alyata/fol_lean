import data.fin

def fin.to_nat {n : ℕ} : fin n → ℕ := (fin.fin_to_nat n).coe

def fin.vec (n : ℕ) (U : Type) : Type := fin n → U
def fin.dvec (n : ℕ) (U : fin n → Type) : Type := ∀(k : fin n), U k

def fin.vec_to_dvec {n : ℕ} {U : Type} (v : fin.vec n U) : fin.dvec n (λ_, U) := v

def fin.map {U V: Type} {n : ℕ} (f : U → V) (v : fin.vec n U) : fin.vec n V :=
λi, f (v i)

def fin.max' {n : ℕ} (vec : fin.vec (n + 1) ℕ) : fin (n + 1) → ℕ
| ⟨0, _⟩     := vec 0
| ⟨k + 1, hk⟩ := max (vec (k + 1)) (fin.max' ⟨k, k.lt_succ_self.trans hk⟩)

def fin.max {n : ℕ} : (fin.vec n ℕ) → ℕ :=
match n with
| 0 := λv, 0
| (k + 1) := λv, @fin.max' k v (fin.last k)
end

def fin.unzip_left {n : ℕ} {U : Type} {V : U → Type} (v : fin.vec n (Σx : U, V x)) 
              : fin.vec n U :=
λi, (v i).fst

def fin.unzip_right {n : ℕ} {U : Type} {V : U → Type} (v : fin.vec n (Σx : U, V x)) 
                    : fin.dvec n (V ∘ (fin.unzip_left v)) :=
λi, (v i).snd

def fin.empty {U : Type} : fin.vec 0 U := (λi, i.elim0)

infixr `::` := fin.cons