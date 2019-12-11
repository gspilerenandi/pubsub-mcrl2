Require Import Ensembles.

Notation "x ∈ y" := (@In _ y x)(at level 30).

Notation "x ⊆ y" := (Included _ x y)(at level 31).

(*------------------------------------------------------------------------------------------------
  https://stackoverflow.com/questions/56201111/what-is-the-standard-cartesian-product-construction-for-ensemble
-------------------------------------------------------------------------------------------------*)
Definition prod_cart
           (U V : Type)
           (A : Ensemble U)
           (B : Ensemble V) 
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
(*------------------------------------------------------------------------------------------------*)

(*Definition 1: set of data-values*)
Variable  data_value: Type.
Definition d_in_D
           (d: data_value)
           (D: Ensemble data_value)
  := d ∈ D.

(*Definition 2: timestamps*)
Definition t_in_T
           (t: nat)
           (T: Ensemble nat)
  := t ∈ T.

(*Definition 3: Events*)
Definition e
           (d: data_value)
           (t: nat)
  : data_value*nat
  := (d,t).

Definition e_in_E
           (e:data_value*nat)
           (E: Ensemble(data_value*nat))
  :=  e ∈ E.

Definition DxT
           (D: Ensemble data_value)
           (T: Ensemble nat)
  : Ensemble(data_value*nat)
  := prod_cart (data_value)(nat)(D)(T).

Definition E_included_DxT
           (E:Ensemble(data_value*nat))
           (D: Ensemble data_value)
           (T: Ensemble nat)
  : Prop
  := E ⊆ DxT D T.

(*Definition 4: Event-buffers*)
Definition b_included_E
           (b: Ensemble (data_value*nat))
           (E: Ensemble(data_value*nat))
  := b ⊆ E.

(*Definition 5: Topics*)
Variable topic : Type.

Definition τ_in_Tau
           (τ:topic)
           (Tau: Ensemble topic)
  := τ ∈ Tau.

(*Definition 6: Locations*)
Variable location : Type.
Definition l_in_L
           (l:location)
           (L: Ensemble location)
  := l ∈ L.

(*Definition 7: Subscribers*)

Definition s
           (l:location)
           (ψl:Ensemble topic)
           (Tau: Ensemble topic)
           (L: Ensemble location)
           (P: (ψl ⊆ Tau ) /\ (l_in_L l L))
  :=  (l,ψl).






