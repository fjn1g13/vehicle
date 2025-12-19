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

-- TODO: prove properties about this?
def unwrap_index {d:Nat} {ds:List Nat} (is:Index (d::ds)) : Index ds :=
  let ⟨is, his⟩ := is
  match is with
  | _::is => ⟨is, his.right⟩

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


def project (f:a -> b) (t:Tensor a ds) : Tensor b ds :=
  match ds, t with
  | [], Tensor.scalar v => Tensor.scalar (f v)
  | _::_, Tensor.tensor fa => Tensor.tensor (fun i => project f (fa i))


-- TODO: make a MathLib project; for now, def props manually
def Commutative (f:a -> a -> b) := ∀a b, f a b = f b a

theorem pointwise_comm {f:a -> a -> b} (f_comm:Commutative f) : Commutative (a := Tensor a ds) (pointwise f) :=
  fun ta tb =>
    match ds, ta, tb with
    | [], Tensor.scalar va, Tensor.scalar vb => by
      repeat rw [pointwise]
      rw [f_comm]
    | _::_, Tensor.tensor fa, Tensor.tensor fb => by
      repeat rw [pointwise]
      rw [Tensor.tensor.injEq]
      funext i
      apply pointwise_comm f_comm

-- distributivity of indexing over pointwise: probably more useful proving random properties over pointwise
theorem index_pointwise (f:a -> b -> c) (ta:Tensor a ds) (tb:Tensor b ds) (is:Index ds)
  : index' (pointwise f ta tb) is = f (index' ta is) (index' tb is) :=
  have ⟨is, his⟩ := is
  match ds, ta, tb, is with
  | [], Tensor.scalar va, Tensor.scalar vb, [] => rfl
  | _::_, Tensor.tensor fa, Tensor.tensor fb, i::is => by
    rw [pointwise]
    repeat rw [index', index]
    exact index_pointwise _ _ _ ⟨is, his.right⟩

def Transitive (R:a -> a -> Prop) := ∀{a b c}, R a b -> R b c -> R a c

-- index of pointwise is transitive (pointwise is transitive )
theorem index_pointwise_transitive {R:a -> a -> Prop} (R_trans:Transitive R) (is:Index ds)
  : Transitive (fun ta tb => index' (pointwise R ta tb) is) := by
  intro a b c hab hbc
  rw [index_pointwise] at *
  exact R_trans hab hbc


-- distributivity of indexing into projection
theorem index_project (f:a -> b) (t:Tensor a ds) (is:Index ds)
  : index' (project f t) is = f (index' t is) :=
  have ⟨is, his⟩ := is
  match ds, t, is with
  | [], Tensor.scalar v, [] => rfl
  | _::_, Tensor.tensor fa, i::is => by
    rw [project]
    repeat rw [index', index]
    exact index_project f _ ⟨is, his.right⟩

-- tensor builders
def const_tensor (ds:List Nat) (v:a) : Tensor a ds :=
  match ds with
  | [] => Tensor.scalar v
  | _::ds =>
    Tensor.tensor (fun _ => const_tensor ds v)

theorem index_const_tensor {ds:List Nat} (v:a) (is:Index ds) : index' (const_tensor ds v) is = v :=
  let ⟨is, his⟩ := is
  match ds, is with
  | [], [] => rfl
  | _::ds, _::is => by
    rw [const_tensor]
    rw [index', index]
    have hi := index_const_tensor v ⟨is, his.right⟩
    rw [index'] at hi
    rw [hi]

def unwrap_f_index {d:Nat} {ds:List Nat} (f:Index (d::ds) -> a) (i:Fin d) (is:Index ds) : a :=
  f ⟨i.val::is.val, ⟨i.isLt, is.property⟩⟩

def init_tensor {ds:List Nat} (f:Index ds -> a) : Tensor a ds :=
  match ds with
  | [] => Tensor.scalar (f ⟨[], True.intro⟩)
  | _::_ =>
    Tensor.tensor (fun i => init_tensor (unwrap_f_index f i))

theorem index_init_tensor {ds:List Nat} (f:Index ds -> a) (is:Index ds) : index' (init_tensor f) is = f is :=
  let ⟨is, his⟩ := is
  match ds, is with
  | [], [] => by rfl
  | d::ds, i::is => by
    rw [init_tensor]
    rw [index', index]
    have hi := index_init_tensor (unwrap_f_index f ⟨i, his.left⟩) ⟨is, his.right⟩
    rw [index'] at hi
    rw [hi]
    rfl
