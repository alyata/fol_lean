import data.fin

def fin.vec (U : Type) (n : ℕ) : Type := fin n → U

def fin.map {U V: Type} {n : ℕ} (f : U → V) (v : fin.vec U n) : fin.vec V n :=
λi, f (v i)

def fin.empty {U : Type} : fin.vec U 0 := (λi, i.elim0)

infixr `::` := fin.cons