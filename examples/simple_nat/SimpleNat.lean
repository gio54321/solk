namespace SimpleNat

axiom MyAxiom.{u} : ∀ a: Sort u, ∀ x y : a, x = y → y = x
theorem my_theorem : ∀ a b : Unit, a = b → b = a := MyAxiom Unit

inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | n, zero   => n
  | n, succ m => succ (add n m)

def one : MyNat := succ zero
def two : MyNat := succ one

theorem add_zero (n : MyNat) : add n zero = n := rfl

theorem add_succ (n m : MyNat) : add n (succ m) = succ (add n m) := rfl

theorem zero_add : ∀ n : MyNat, add zero n = n
  | zero   => rfl
  | succ n => congrArg succ (zero_add n)

theorem one_add_one : add one one = two := rfl

end MyNat
end SimpleNat
