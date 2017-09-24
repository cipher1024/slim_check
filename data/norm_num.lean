
import algebra.group_power
import data.rat
import data.num.basic

universes u v w

namespace list

variables {m : Type u → Type v} [applicative m]
variables {α : Type w} {β : Type u}
variables f : α → m β

def traverse : list α → m (list β)
 | [] := pure []
 | (x :: xs) := (::) <$> f x <*> traverse xs

end list

namespace expr

variables {m : Type → Type u} [applicative m]
variables {elab elab' : bool}

variables f : expr elab → m (expr elab')

meta def traverse : expr elab → m (expr elab')
 | (var v)  := pure $ var v
 | (sort l) := pure $ sort l
 | (const n ls) := pure $ const n ls
 | (mvar n n' e) := mvar n n' <$> f e
 | (local_const n n' bi e) := local_const n n' bi <$> f e
 | (app e₀ e₁) := app <$> f e₀ <*> f e₁
 | (lam n bi e₀ e₁) := lam n bi <$> f e₀ <*> f e₁
 | (pi n bi e₀ e₁) := pi n bi <$> f e₀ <*> f e₁
 | (elet n e₀ e₁ e₂) := elet n <$> f e₀ <*> f e₁ <*> f e₂
 | (macro m es) := macro m <$> list.traverse f es

end expr

namespace norm_num

variable {α : Type u}
section pow
variable [monoid α]
lemma pow_bit0 (a : α) (b : ℕ) : a ^ (bit0 b) = (a * a) ^ b :=
by { simp [bit0], rw [← two_mul,pow_mul,pow_succ',pow_one] }

lemma pow_bit0_helper (a t : α) (b : ℕ) (h : (a * a) ^ b = t) : a ^ bit0 b = t :=
by simp [pow_bit0,h]

lemma pow_bit1 (a : α) (b : ℕ) : a ^ (bit1 b) = a * (a * a) ^ b :=
by simp [bit1,pow_add,pow_bit0]

lemma pow_bit1_helper (a t : α) (b : ℕ) (h : (a * a) ^ b = t) : a ^ bit1 b = a * t :=
by simp [pow_bit1,h]

lemma pow_one (a : α) : a^1 = a := pow_one a

lemma pow_zero (a : α) : a^0 = 1 := pow_zero _

lemma pow_eq_pow_nat (p q : ℕ)
: nat.pow p q = pow_nat p q :=
by { induction q, refl,
     simp [nat.pow,pow_nat,has_pow_nat.pow_nat,monoid.pow,ih_1], }

lemma pow_eq_pow_nat_helper (p q k : ℕ)
  (h : pow_nat p q = k)
: nat.pow p q = k :=
by { simp [pow_eq_pow_nat,h] }

end pow

section le
variables [linear_ordered_semiring α]
lemma zero_le_bit0 (a : α) : 0 ≤ a → 0 ≤ bit0 a :=
begin
  intros h,
  simp [bit0], rw ← zero_add (0 : α),
  apply add_le_add h h
end
lemma zero_le_bit1 (a : α) : 0 ≤ a → 0 ≤ bit1 a :=
begin
  intros h,
  simp [bit1], rw ← zero_add (0 : α),
  apply add_le_add,
  apply zero_le_one,
  apply zero_le_bit0 _ h,
end
lemma zero_le_zero : 0 ≤ (0 : α) := by refl
lemma zero_le_one : 0 ≤ (1 : α) := zero_le_one
lemma one_le_bit0 (a : α) : 1 ≤ a → 1 ≤ bit0 a :=
begin
  intros h,
  transitivity (1 + 1 : α),
  { apply le_add_of_nonneg_left, apply zero_le_one },
  simp [bit0],
  apply add_le_add h h
end
lemma one_le_bit1 (a : α) (h : 0 ≤ a) : 1 ≤ bit1 a :=
begin
  simp [bit1],
  apply le_add_of_nonneg_right,
  apply zero_le_bit0 _ h,
end
lemma one_le_one : 1 ≤ (1 : α) := by refl
-- lemma bit0_le_bit1 (a b : α) : a ≤ b → bit0 a ≤ bit1 b :=
-- begin
--   intros h,
--   simp [bit1],
--   transitivity (1 + bit0 a),
--   { apply le_add_of_nonneg_left, apply zero_le_one },
--   apply add_le_add, refl,
--   apply bit0_le_bit0 _ _ h,
-- end
lemma bit0_le_zero (a : α) (h : a ≤ 0) : bit0 a ≤ (0 : α) :=
begin
  simp [bit0],
  rw ← add_zero (0 : α),
  apply add_le_add h h,
end
lemma bit0_le_one (a : α) (h : a ≤ 0) : bit0 a ≤ (1 : α) :=
begin
  simp [bit0],
  rw ← add_zero (1 : α),
  apply add_le_add _ h,
  transitivity (0 : α),
  apply h,
  apply zero_le_one,
end
lemma bit1_le_bit0 (a b : α) : add1 a ≤ b → bit1 a ≤ bit0 b :=
begin
  intros h,
  simp [bit1,bit0],
  apply add_le_add _ h,
  transitivity (add1 a),
  { apply le_add_of_nonneg_right,
    apply zero_le_one },
  apply h
end
-- lemma bit1_le_bit1 (a b : α) : a ≤ b → bit1 a ≤ bit1 b :=
-- begin
--   intros h,
--   simp [bit1],
--   apply add_le_add, refl,
--   apply bit0_le_bit0 _ _ h,
-- end
lemma bit1_le_zero (a : α) (h : add1 a ≤ 0) : bit1 a ≤ (0 : α) :=
begin
  simp [bit1,bit0],
  rw ← add_zero (0 : α),
  apply add_le_add _ h,
  transitivity add1 a,
  apply le_add_of_nonneg_right, apply zero_le_one,
  apply h
end
lemma bit1_le_one (a : α) (h : a ≤ 0) : bit1 a ≤ (1 : α) :=
begin
  simp [bit1],
  apply add_le_of_le_of_nonpos,
  refl,
  apply bit0_le_zero _ h,
end

end le

end norm_num

namespace num
section syntax
-- inductive pos
--  | one : pos
--  | bit0 : pos → pos
--  | bit1 : pos → pos

-- inductive nonneg
--  | zero : nonneg
--  | pos : pos → nonneg

open pos_num (one bit0 bit1)
def add1 : pos_num → pos_num
 | one := pos_num.bit0 one
 | (pos_num.bit0 x) := pos_num.bit1 x
 | (pos_num.bit1 x) := pos_num.bit0 (add1 x)

def add_n : ℕ → pos_num → pos_num
 | 0 x := x
 | (n+1) x := add1 (add_n n x)

def pos_le : pos_num → pos_num → bool
 | one _ := tt
 | _ one := ff
 | (pos_num.bit0 x) (pos_num.bit0 y) := pos_le x y
 | (pos_num.bit0 x) (pos_num.bit1 y) := pos_le x y
 | (pos_num.bit1 x) (pos_num.bit0 y) := pos_le (add1 x) y
 | (pos_num.bit1 x) (pos_num.bit1 y) := pos_le x y

def num_le : num → num → bool
 | zero _ := tt
 | (pos x) zero := ff
 | (pos x) (pos y) := pos_le x y

-- inductive znum
--  | pos : num → znum
--  | neg : num → znum

-- open num.znum

def znum_le : znum → znum → bool
 | znum.zero (znum.neg _) := ff
 | znum.zero _ := tt
 | (znum.pos _) znum.zero := ff
 | _ znum.zero := tt
 | (znum.pos x) (znum.pos y) := pos_le x y
 | (znum.neg x) (znum.pos y) := tt
 | (znum.pos x) (znum.neg y) := ff
 | (znum.neg x) (znum.neg y) := pos_le y x

end syntax

class has_denote (α : inout Type u) (β : Type v) :=
  (denote : α → β)

export has_denote (denote)

variable {α : Type u}

section denote

variables [has_one α][has_add α]
def pos_num.denote : pos_num → α
 | pos_num.one := has_one.one α
 | (pos_num.bit0 x) := bit0 (pos_num.denote x)
 | (pos_num.bit1 x) := bit1 (pos_num.denote x)

instance pos_denote : has_denote pos_num α :=
⟨ pos_num.denote ⟩

variables [has_zero α]

def num.denote : num → α
 | num.zero := (0 : α)
 | (num.pos x) := pos_num.denote x

instance nonneg_denote : has_denote num α :=
⟨ num.denote ⟩

variables [has_neg α]

def znum.denote : znum → α
 | (znum.pos x) := pos_num.denote x
 | znum.zero := 0
 | (znum.neg x) := - pos_num.denote x

instance : has_denote znum α :=
⟨ znum.denote ⟩

end denote

section soundness

section linear_ordered_semiring
variables [linear_ordered_semiring α]

lemma one_le_denote (x : pos_num)
: 1 ≤ @denote pos_num α _ x :=
begin
  induction x ; try { refl }
  ; simp [denote,pos_num.denote,bit0,bit1],
  case pos_num.bit1
  { transitivity (1 + (1 + 1) : α),
    { apply le_add_of_nonneg_right,
      transitivity (1 : α),
      apply le_add_of_nonneg_left,
      all_goals { apply zero_le_one } },
    apply add_le_add_left,
    apply add_le_add ; assumption },
  case pos_num.bit0
  { transitivity (1 + 1 : α),
    apply le_add_of_nonneg_left, apply zero_le_one,
    apply add_le_add ; assumption },
end

lemma denote_add1 (x : pos_num)
: @denote pos_num α _ (add1 x) = norm_num.add1 (@denote pos_num α _ x) :=
by { induction x ; try { refl },
     simp [add1,denote,pos_num.denote] at *,
     simp [ih_1,bit0,bit1,norm_num.add1] }

lemma bit0_le_bit0 (a b : α) : a ≤ b → bit0 a ≤ bit0 b :=
begin
  intros h,
  simp [bit0],
  apply add_le_add h h
end

lemma denote_le_denote_of_pos_num_le {x y : pos_num}
  (h : pos_le x y)
: @denote pos_num α _ x ≤ @denote pos_num α _ y :=
begin
  revert x,
  induction y ; intros x h,
  case pos_num.one
  { cases x,
    { refl },
    { cases h },
    { cases h } },
  case pos_num.bit0 y
  { cases x with x x,
    { apply one_le_denote, },
    case pos_num.bit0
    { unfold denote pos_num.denote,
      apply bit0_le_bit0, apply ih_1 h },
    case pos_num.bit1
    { dsimp [denote,pos_num.denote,bit0,bit1],
      unfold pos_le at h,
      have h' := ih_1 h,
      rw [denote_add1] at h',
      rw [add_assoc],
      apply add_le_add _ h',
      apply le_trans _ h',
      unfold norm_num.add1 denote,
      apply le_add_of_nonneg_right,
      apply zero_le_one, } },
  case pos_num.bit1 y
  { cases x with x x,
    { apply one_le_denote, },
    case pos_num.bit0
    { transitivity @denote pos_num α _ (pos_num.bit0 y),
      { unfold denote pos_num.denote bit0,
        apply add_le_add
        ; apply ih_1 h, },
      { unfold denote pos_num.denote bit1,
        apply le_add_of_nonneg_right,
        apply zero_le_one } },
    case pos_num.bit1
    { unfold denote pos_num.denote bit1,
      apply add_le_add_right,
      apply bit0_le_bit0,
      apply ih_1 h } }
end

lemma zero_le_denote (x : num)
: 0 ≤ denote α x :=
begin
  cases x with x,
  refl,
  transitivity (1 : α),
  apply zero_le_one,
  apply one_le_denote
end

lemma denote_le_denote_of_num_le (x y : num)
  (h : num_le x y)
: denote α x ≤ denote α y :=
begin
  cases x with x ; cases y with y
  ; simp [denote,num.denote]
  ; simp [num_le] at h,
  { apply zero_le_denote (num.pos y) },
  { cases h },
  { apply denote_le_denote_of_pos_num_le h }
end

end linear_ordered_semiring

section linear_ordered_ring

variable [linear_ordered_ring α]

lemma denote_le_denote_of_znum_le (x y : znum)
  (h : znum_le x y = tt)
: denote α x ≤ denote α y :=
begin
  cases x with x x ; cases y with y y
  ; try { cases h  }
  ; simp [denote,num.denote]
  ; simp [znum_le] at h,
  { unfold znum.denote num.denote,
    transitivity (1 : α),
    apply zero_le_one,
    apply one_le_denote },
  { apply denote_le_denote_of_pos_num_le h, },
  { cases h,
    transitivity (0 : α),
    { apply neg_nonpos_of_nonneg,
      transitivity (1 : α), apply zero_le_one,
      apply one_le_denote, },
    { refl }, },
  { transitivity (0 : α),
    { apply neg_nonpos_of_nonneg,
      transitivity (1 : α), apply zero_le_one,
      apply one_le_denote },
    { transitivity (1 : α), apply zero_le_one,
      apply one_le_denote } },
  { apply neg_le_neg,
    apply denote_le_denote_of_pos_num_le h, }
end

end linear_ordered_ring

end soundness

end num

namespace tactic.interactive

open tactic
open lean.parser
open interactive
open interactive.types
local attribute [semireducible] reflected

meta instance has_reflect_num_pos : has_reflect pos_num
 | pos_num.one := `(_)
 | (pos_num.bit0 x) := `(pos_num.bit0 %%(has_reflect_num_pos x))
 | (pos_num.bit1 x) := `(pos_num.bit1 %%(has_reflect_num_pos x))

meta instance has_reflect_num_nonneg : has_reflect num
 | num.zero := `(num.zero)
 | (num.pos x) := `(num.pos _)

meta instance has_reflect_num_num : has_reflect znum
 | (znum.pos x) := `(znum.pos _)
 | znum.zero := `(_)
 | (znum.neg x) := `(znum.neg _)

meta def parse_pos_num : expr → option pos_num
 | `(has_one.one _) := some pos_num.one
 | `(bit0 %%x) := pos_num.bit0 <$> parse_pos_num x
 | `(bit1 %%x) := pos_num.bit1 <$> parse_pos_num x
 | _ := none

meta def parse_num : expr → option num
 | `(has_zero.zero %%t) := some num.zero
 | e := num.pos <$> parse_pos_num e

def znum.to_pos : num → znum
 | (num.pos n) := znum.pos n
 | num.zero := znum.zero

def znum.to_neg : num → znum
 | (num.pos n) := znum.neg n
 | num.zero := znum.zero

meta def parse_znum : expr → option znum
 | `(- %%e) := znum.to_neg <$> parse_num e
 | e := znum.to_pos <$> parse_num e

meta def parse_rw_num {α} [has_reflect α]
    (parse : expr → option α) (e : expr)
  : tactic (α × expr) := do
n ← parse e,
asrt ← to_expr ``(%%e = num.has_denote.denote _ %%(reflect n)),
solve_aux asrt $ do
  `[simp [num.has_denote.denote,num.znum.denote,num.num.denote,num.pos_num.denote]],
  return n

inductive denotation
| znum | num | pos_num

meta def denoted_by (t : expr) : tactic denotation := do
z ← try_core (to_expr ``(linear_ordered_semiring %%t) >>= mk_instance),
if z.is_some then do
  n ← try_core (to_expr ``(linear_ordered_ring %%t) >>= mk_instance),
  if n.is_some
  then return denotation.znum
  else return denotation.num
else return denotation.pos_num

meta def is_literal_expr : expr → bool
 | `(- %%e₀) := is_literal_expr e₀
 | `(%%e₀ * %%e₁) := is_literal_expr e₀ ∧ is_literal_expr e₁
 | `(%%e₀ + %%e₁) := is_literal_expr e₀ ∧ is_literal_expr e₁
 | `(%%e₀ - %%e₁) := is_literal_expr e₀ ∧ is_literal_expr e₁
 -- | `(%%e₀ / %%e₁) := is_literal_expr e₀ ∧ is_literal_expr e₁
 -- | `(%%e₀ % %%e₁) := is_literal_expr e₀ ∧ is_literal_expr e₁
 | e := e.is_numeral

meta def is_literal_pow : expr → bool
 | `(has_pow_nat.pow_nat %%e₀ %%e₁) := e₀.is_numeral ∧ e₁.is_numeral
 | `(pow_nat %%e₀ %%e₁) := e₀.is_numeral ∧ e₁.is_numeral
 | `(nat.pow %%e₀ %%e₁) := e₀.is_numeral ∧ e₁.is_numeral
 | _ := ff

meta def is_literal_le : expr → bool
 | `(%%e₀ ≤ %%e₁) := e₀.is_numeral ∧ e₁.is_numeral
 | _ := ff

meta def derive (e : expr) (tac : itactic) : tactic (expr × expr) := do
t ← infer_type e,
v ← mk_meta_var t,
g ← i_to_expr ``(%%e = %%v),
(_,pr) ← solve_aux g (tac >> try  (exact ``(rfl)) >> done),
prod.mk <$> instantiate_mvars v <*> pure pr

meta def eval_pow (e : expr) : tactic (expr × expr) := do
(e',pr) ← derive e (do
try `[apply norm_num.pow_eq_pow_nat_helper],
repeat (
  `[apply norm_num.pow_bit0_helper] <|>
  `[apply norm_num.pow_bit1_helper] <|>
  `[apply norm_num.pow_zero] <|>
  `[apply norm_num.pow_one])),
(e'',pr') ← norm_num e',
prod.mk e'' <$> to_expr ``(eq.trans %%pr %%pr')

meta def replace_with (e₀ e₁ : expr) (pr : tactic unit) : tactic unit := do
eq ← to_expr ``(%%e₀ = %%e₁),
h ← assert `h eq,
solve1 pr,
tactic.rewrite_target h,
tactic.clear h

#check congr
meta def apply_computation_rule {α} [has_reflect α]
  (parse : expr → option α)
  (e e' : expr)
  (rule' : pexpr) : tactic unit := do
    t ← infer_type e,
    (n,pr)   ← parse_rw_num parse e,
    (n',pr') ← parse_rw_num parse e',
    let en  := reflect n,
    let en' := reflect n',
    -- rw_rule ← to_expr ``(congr %%pr'),
    -- rewrite_target pr,
    -- rewrite_target pr',
    asrt ← to_expr
      ``(  (%%e ≤ %%e')
         = (num.has_denote.denote %%t %%en ≤ num.has_denote.denote %%t %%en')),
    -- trace asrt,
    h' ← assert `h' asrt,
    -- trace_state,
    tactic.applyc `congr,
    tactic.applyc `congr_arg,
    tactic.exact pr,
    tactic.exact pr',
    -- trace_state,
    -- ; (tactic.exact pr <|> tactic.exact pr'),
    rewrite_target h',
    rule ← to_expr rule',
    h ← tactic.note `h none $ expr.mk_app rule [en,en'],
    dunfold [`num.znum_le,`num.num_le,`num.pos_le,`num.add1]
      (loc.ns [h.local_pp_name]),
    h ← get_local `h,
    tactic.revert h,
    tactic.generalize en,
    tactic.generalize en',
    introv [`h3],
    `[apply h3, clear h3, exact rfl]

meta def eval_le (e : expr) : tactic (expr × expr) := do
g ← to_expr ``( %%e ↔ true ),
(_,pr) ← solve_aux g (do
  `[apply iff_true_intro],
  (e,e') ← tactic.target >>= option.to_monad ∘ expr.is_le,
  t ← infer_type e,
  d ← denoted_by t,
  match d with
   | denotation.znum :=
     apply_computation_rule parse_znum e e'
        ``(@num.denote_le_denote_of_znum_le %%t _)
   | denotation.num :=
     apply_computation_rule parse_num e e'
        ``(@num.denote_le_denote_of_num_le %%t _)
   | denotation.pos_num :=
     apply_computation_rule parse_pos_num e e'
        ``(@num.denote_le_denote_of_pos_num_le %%t _)
  end ),
return (`(true),pr)

meta def norm_sub_expr' : expr → tactic expr
| e := do
if e.is_numeral then return e
else do
 e' ← expr.traverse norm_sub_expr' e,
 if is_literal_pow e' then do
  (e'',pr) ← eval_pow e',
  tactic.rewrite_target pr,
  return e''
 else if is_literal_expr e' then do
  (e''',pr) ← norm_num e',
  tactic.rewrite_target pr,
  return e'''
 else if is_literal_le e' then do
  (e'',pr) ← eval_le e',
  tactic.rewrite_target pr,
  return e''
 else return e'

meta def norm_sub_expr : tactic unit :=
target >>= norm_sub_expr' >> skip

example : 374 + (32 - (2 * 8123) : ℤ) - 61 * 50 = 86 + 32 * 32 - 4 * 5000
      ∧ 43 ≤ 74 + (33 : ℤ) :=
by { norm_sub_expr, split, refl, trivial }

example : (1103 : ℤ) ≤ (2102 : ℤ) :=
by { norm_sub_expr, trivial }

example : (11047462383473829263 : ℤ) ≤ (21048574677772382462 : ℤ) :=
by { norm_sub_expr, trivial,  }

example : (210485742382937847263 : ℤ) ≤ (1104857462382937847262 : ℤ) :=
by { norm_sub_expr, trivial }

example : (210485987642382937847263 : ℕ) ≤ (11048512347462382937847262 : ℕ) :=
by { norm_sub_expr, trivial }

example : (210485987642382937847263 : ℚ) ≤ (11048512347462382937847262 : ℚ) :=
by { norm_sub_expr, trivial }

meta def apply_normed (x : parse texpr) : tactic unit := do
x₁ ← to_expr x,
(x₂,_) ← derive x₁ norm_sub_expr,
tactic.exact x₂

local infix ^ := pow_nat

example (x : ℕ) : ℕ :=
 let n : ℕ := by apply_normed (2^32 - 71) in n

#eval by apply_normed (2^32 - 71)

end tactic.interactive
