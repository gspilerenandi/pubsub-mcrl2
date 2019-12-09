Require Import Ensembles.

Notation "x ∈ y" := (@In _ y x)(at level 30).

Notation "x ⊆ y" := (Included _ x y)(at level 31).

(*Definition 1: set of data-values*)
Variable  data_value: Type.
Variable D:(Ensemble data_value).

(*Definition 2: timestamps*)
Variable T:(Ensemble nat).


(*Definition 3: Events*)

Definition t_in_T (t: nat)(T:Ensemble nat) := t ∈ T.

Definition d_in_D (d:data_value)(D:Ensemble data_value) := d ∈ D.

Definition e: data_value -> nat -> data_value*nat := fun d t => (d,t).

Print e.

Check e.

Definition prod_cart (U V : Type) (A : Ensemble U) (B : Ensemble V) 
  : Ensemble (U * V)
  := fun x => In _ A (fst x) /\ In _ B (snd x).

Lemma cartesian_inclusion U V A B C D :
  Included U A C /\ Included V B D ->
  Included (U * V) ( prod_cart  _ _ A B) ( prod_cart  _ _ C D).
Proof.
intros [HU HV] [x y] [HA HB].
split.
- now apply HU.
- now apply HV.
Qed.

(*Definition DxT: Ensemble data_value -> Ensemble nat -> Ensemble data_value*Ensemble nat := fun D T => (D,T).*)

Definition DxT: Ensemble(data_value*nat) := prod_cart (data_value)(nat)(D:Ensemble data_value)(T: Ensemble nat).

Definition e_as_Ensemble (e:data_value*nat) := fun e => Ensemble e.

Definition e_in_E (e:data_value*nat)(E: Ensemble(data_value*nat) ) :=  e ∈ E.

Check prod_cart.

Print prod_cart.

Definition E_included_DxT (E:Ensemble(data_value*nat))(DxT:prod_cart(data_value)(nat)(D: Ensemble data_value)(T: Ensemble nat))
  : Prop
  := E ⊆ DxT.

Definition e_in_E := e ∈ E.








