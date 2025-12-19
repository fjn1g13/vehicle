inductive Tensor (a:Type) : (ds:List Nat) -> Type
  | scalar : a -> Tensor a []
  | tensor : {d:Nat} -> {ds:List Nat} -> (Fin d -> Tensor a ds) -> Tensor a (d::ds)

-- indexing into a Tensor
def LegalIndex (ds:List Nat) (is:List Nat) : Prop :=
  match ds, is with
  | [], [] => True
  | d::ds, i::is => i < d ∧ LegalIndex ds is
  | _, _ => False

def Index (ds:List Nat) := { is : List Nat // LegalIndex ds is }

def index (t:Tensor a ds) (is:List Nat) (legal:LegalIndex ds is) :=
  match ds, is, t with
  | [], [], Tensor.scalar v => v
  | _::_, i::is, Tensor.tensor f => index (f ⟨i, legal.left⟩) is legal.right

def index' (t:Tensor a ds) (is:Index ds) :=
  index t is.val is.property

syntax "check_legal_index" : tactic
macro_rules
| `(tactic|check_legal_index) => `(tactic| (
  repeat (apply And.intro; omega)
  exact True.intro
))

syntax "legal_index" term : tactic
macro_rules
| `(tactic|legal_index $is:term) => `(tactic| (
  apply Subtype.mk $is
  repeat (apply And.intro; omega)
  exact True.intro
))

example : LegalIndex [10, 5] [2, 3] := by check_legal_index
example : Index [10, 5] := by legal_index [2, 3]

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
#eval index s2 [3, 7] (by check_legal_index)
#eval index' s2 (by legal_index [3, 7]) -- TODO: really want this to be an elaborator so we don't need the `by`, but it works


def pointwise (f:a -> b -> c) (ta:Tensor a ds) (tb:Tensor b ds) : Tensor c ds :=
  match ds, ta, tb with
  | [], Tensor.scalar va, Tensor.scalar vb => Tensor.scalar (f va vb)
  | _::_, Tensor.tensor fa, Tensor.tensor fb => Tensor.tensor (fun i => pointwise f (fa i) (fb i))

def s22 := pointwise (. + .) s2 s2

#eval extract (unwrap (unwrap s22 3) 7)

-- TODO: make a MathLib project; for now, def props manually
def Symmetric (f:a -> a -> b) := ∀a b, f a b = f b a

-- TODO: this should take a reflexive relation
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
