-- Indexes
def LegalIndex (ds:List Nat) (is:List Nat) : Prop :=
  match ds, is with
  | [], [] => True
  | d::ds, i::is => i < d ∧ LegalIndex ds is
  | _, _ => False

syntax "check_legal_index" : tactic
macro_rules
| `(tactic|check_legal_index) => `(tactic| (
  repeat (apply And.intro; omega)
  exact True.intro
))

def Index (ds:List Nat) := { is : List Nat // LegalIndex ds is }

syntax "legal_index" term : tactic
macro_rules
| `(tactic|legal_index $is:term) => `(tactic| (
  apply Subtype.mk $is
  repeat (apply And.intro; omega)
  exact True.intro
))

theorem legal_index_length (is:List Nat) (his:LegalIndex ds is) : is.length = ds.length :=
  match ds, is with
  | [], [] => rfl
  | d::ds, i::is => by
    repeat rw [List.length_cons]
    apply Nat.add_one_inj.mpr
    exact legal_index_length is his.right

theorem length_Index (is:Index ds) : is.val.length = ds.length :=
  legal_index_length is.val is.property

-- Tensor
def Tensor a ds := Index ds -> a

def constT ds (v:a) : Tensor a ds :=
  fun _ => v

def stack (ts:List (Tensor a ds)) : Tensor a (ts.length::ds) :=
  sorry


-- Transforms
def projectT (f:a -> b) (t:Tensor a ds) : Tensor b ds :=
  fun is => f (t is)

def pointwiseT  (f:a -> b -> c) (ta:Tensor a ds) (tb:Tensor b ds) : Tensor c ds :=
  fun is => f (ta is) (tb is)


-- Transform Properties
def Commutative (f:a -> a -> b) := ∀{x y}, f x y = f y x

theorem commutative_pointwiseT (f:a -> a -> b) (comm_f:Commutative f) : Commutative (a := Tensor a ds) (pointwiseT f) := by
  intro x y
  funext is
  repeat rw [pointwiseT]
  exact comm_f

def Transitive (R:a -> a -> Prop) := ∀{x y z}, R x y -> R y z -> R x z

theorem transitive_pointwiseT {R:a -> a -> Prop} (trans_R:Transitive R) (is:Index ds) : Transitive (a := Tensor a ds) (fun ta tb => pointwiseT R ta tb is) := by
  intro x y z
  intro hxy hyz
  rw [pointwiseT] at *
  exact trans_R hxy hyz


-- checks that every dimension is the same except for dimension k
-- def align_along (k:Nat) (ds1:List Nat) (ds2:List Nat) :=
--   match ds1, ds2, k with
--   | _::ds1, _::ds2, 0 => ds1 = ds2
--   | d1::ds1, d2::ds2, Nat.succ k => d1 = d2 ∧ align_along k ds1 ds2
--   | _, _, _ => False

def align_along (k:Nat) (ds1:List Nat) (ds2:List Nat) :=
  match ds1, ds2, k with
  | _::ds1, _::ds2, 0 => ds1 = ds2
  | d1::ds1, d2::ds2, Nat.succ k => d1 = d2 ∧ align_along k ds1 ds2
  | _, _, _ => False

theorem align_along_comm (k:Nat) : Commutative (align_along k) :=
  fun {ds1 ds2} =>
  match ds1, ds2, k with
  | _::ds1, _::ds2, 0 => by
    rw [align_along, align_along]
    rw [Eq.comm (a := ds1)]
  | d1::ds1, d2::ds2, Nat.succ k => by
    rw [align_along, align_along]
    rw [align_along_comm k]
    rw [Eq.comm (a := d1)]
  | [], d2::ds2, _ => by simp only [align_along]
  | d1::ds1, [], _ => by simp only [align_along]
  | [], [], _ => by simp only [align_along]

def concat_dims (hds: align_along k ds1 ds2) :=
  match ds1, ds2, k with
  | d1::ds1, d2::_, 0 => (d1 + d2)::ds1
  | d1::ds1, _::ds2, Nat.succ k => d1::concat_dims hds.right
  | [], d2::ds2, _ => by simp only [align_along] at hds
  | d1::ds1, [], _ => by simp only [align_along] at hds
  | [], [], _ => by simp only [align_along] at hds

theorem align_along_k_lt_1 (hds: align_along k ds1 ds2) : k < ds1.length :=
  match ds1, ds2, k with
  | d1::ds1, d2::_, 0 => Nat.zero_lt_succ ds1.length
  | d1::ds1, _::ds2, Nat.succ k => by
    rw [List.length]
    apply Nat.succ_lt_succ
    exact align_along_k_lt_1 hds.right
  | [], d2::ds2, _ => by simp only [align_along] at hds
  | d1::ds1, [], _ => by simp only [align_along] at hds
  | [], [], _ => by simp only [align_along] at hds

theorem align_along_k_lt_2 (hds: align_along k ds1 ds2) : k < ds2.length :=
  align_along_k_lt_1 ((align_along_comm k).mp hds)

theorem align_along_same_length (hds: align_along k ds1 ds2) : ds1.length = ds2.length :=
  match ds1, ds2, k with
  | d1::ds1, d2::_, 0 => Nat.succ_inj.mpr (congrArg List.length hds)
  | d1::ds1, _::ds2, Nat.succ k => by
    rw [List.length, List.length]
    apply Nat.add_left_inj.mpr
    exact align_along_same_length hds.right
  | [], d2::ds2, _ => by simp only [align_along] at hds
  | d1::ds1, [], _ => by simp only [align_along] at hds
  | [], [], _ => by simp only [align_along] at hds

def unligned_dimensions_same (hl:l ≠ k) (hds: align_along k ds1 ds2) : ds1[l]? = ds2[l]? :=
  match ds1, ds2, k with
  | d1::ds1, d2::ds2, 0 => by
    repeat rw [List.getElem?_cons]
    repeat rw [if_neg hl]
    exact congrFun (congrArg getElem? hds) (l - 1)
  | d1::ds1, d2::ds2, Nat.succ k => by
    repeat rw [@List.getElem?_cons]
    rcases l with _ | l
    . repeat rw [if_pos (Eq.refl 0)]
      exact Option.some_inj.mpr hds.left
    . repeat rw [if_neg (Nat.add_one_ne_zero l)]
      repeat rw [Nat.add_one_sub_one]
      rw [ne_eq, Nat.add_one_inj] at hl
      exact unligned_dimensions_same hl hds.right
  | [], d2::ds2, _ => by simp only [align_along] at hds
  | d1::ds1, [], _ => by simp only [align_along] at hds
  | [], [], _ => rfl

def concat (k:Fin ds1.length) (hds: align_along k ds1 ds2) (t1:Tensor a ds1) (t2:Tensor a ds2) : Tensor a (concat_dims hds) :=
  let dk1 := ds1.get k
  fun is =>
    if
