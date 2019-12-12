constant subpub: Type
constant sub: subpub
constant pub: subpub

constants ℓ τ δ: Type


section prodsub

  def e := δ × ℕ
  def r := subpub × ℓ × τ
  
  def eb:= list e
  def rb:= list r

  def s := ℓ × set τ
  def p := ℓ × rb × set (eb × τ × set ℓ)
  def br:= ℓ × set (ℓ × τ) × set (τ × ℓ)

  def π := set p × br × set s
   
end prodsub


def timeGrowsAux: ℕ -> eb → Prop 
  | last []     := true
  | last (h::t) := last < h.2 /\ timeGrowsAux h.2 t

def timeGrows (b:eb) :  Prop :=
  timeGrowsAux 0 b




------------------------------ 
------------------------------ 
------------------------------

def tG (last: ℕ) (b: eb) : Prop :=
    --b = []
    --if b = [] then true else false 
    true
