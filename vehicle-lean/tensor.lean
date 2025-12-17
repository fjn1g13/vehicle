inductive Tensor (a:Type) : (d:List Nat) -> Type
  | scalar : a -> Tensor a []
  | tensor : {d:Nat} -> {ds:List Nat} -> (Fin d -> Tensor a ds) -> Tensor a (d::ds)

def extract (t:Tensor a []) : a :=
  match t with
  | Tensor.scalar v => v

def unwrap {d:Nat} {ds:List Nat} (t:Tensor a (d::ds)) (i:Fin d) : Tensor a ds :=
  match t with
  | Tensor.tensor t' => (t' i)

def s0 : Tensor Nat [] := Tensor.scalar 1
def s1 : Tensor Nat [2] := Tensor.tensor (fun x => Tensor.scalar x.val)
def s2 : Tensor Nat [5, 10] := Tensor.tensor (fun x => Tensor.tensor (fun y => Tensor.scalar (x.val * y.val)))

#eval extract (unwrap (unwrap s2 3) 7)

def pointwise (f:a -> b -> c) (ta:Tensor a ds) (tb:Tensor b ds) : Tensor c ds :=
  match ds, ta, tb with
  | [], Tensor.scalar va, Tensor.scalar vb => Tensor.scalar (f va vb)
  | _::_, Tensor.tensor fa, Tensor.tensor fb => Tensor.tensor (fun i => pointwise f (fa i) (fb i))

def s22 := pointwise (. + .) s2 s2

#eval extract (unwrap (unwrap s22 3) 7)

-- TODO: make a MathLib project; for now, def props manually
def Symmetric (f:a -> a -> b) := ∀a b, f a b = f b a

def pointwise_symm : Symmetric (a := Tensor a ds) (pointwise (f := fun x y => x = y)) :=
  fun ta tb =>
    match ds, ta, tb with
    | [], Tensor.scalar va, Tensor.scalar vb => by
      repeat rw [pointwise]
      conv =>
        lhs
        rw [Eq.comm]
    | _::_, Tensor.tensor fa, Tensor.tensor fb => by
      repeat rw [pointwise]
      rw [Tensor.tensor.injEq]
      funext i
      apply pointwise_symm
