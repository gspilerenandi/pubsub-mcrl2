Require Import Ensembles.

Notation "x ∈ y" := (@In _ y x)(at level 30).

Notation "x ⊆ y" := (Included _ x y)(at level 31).

(*------------------------------------------------------------------------------------------------
  https://stackoverflow.com/questions/56201111/what-is-the-standard-cartesian-product-construction-for-ensemble
-------------------------------------------------------------------------------------------------*)
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
(*------------------------------------------------------------------------------------------------*)

(*Definition 1: set of data-values*)
Variable  data_value: Type.
Variable D:(Ensemble data_value).

(*Definition 2: timestamps*)
Variable T:(Ensemble nat).


(*Definition 3: Events*)
Definition t_in_T (t: nat) := t ∈ T.
Definition d_in_D (d:data_value) := d ∈ D.

Definition e: data_value -> nat -> data_value*nat := fun d t => (d,t).
Variable E : Ensemble(data_value*nat).

Definition DxT
  : Ensemble(data_value*nat)
  := prod_cart (data_value)(nat)(D)(T).

(*actually needed?*)
Definition e_as_Singleton (e:data_value*nat) := fun e => Singleton e.

Definition e_in_E (e:data_value*nat) :=  e ∈ E.

Definition E_included_DxT
           (E:Ensemble(data_value*nat))
           (*(DxT:prod_cart (data_value)(nat)(D: Ensemble data_value)(T: Ensemble nat))*)
  : Prop
  := E ⊆ DxT.

(*Definition 4: Event-buffers*)
(*will be different from what is described in the document*)
(*??Definition element_to_Ensemble (x:_):= fun x => Ensemble x.??*)
Definition event_buffer_pair_of_pointers
  : nat -> nat -> nat*nat
  := fun b_read b_write => (b_read, b_write).

Definition pointers_ebuffer_as_singleton
           (ebpointer: nat*nat)
  := fun ebpointer => Singleton ebpointer.

Variable event_buffer: Type.

Definition E_U_singleton_pointers_e
           (b_r: nat)(b_w: nat)
  := fun b_r b_w => Union E pointers_ebuffer_as_singleton(event_buffer_pair_of_pointers b_r b_w).


(*Definition 5: Topics*)
Variable topic : Type.
Variable Tau: Ensemble topic.

Definition τ_in_Tau (τ:topic) := τ ∈ Tau.

(*Definition 6: Locations*)
Variable location : Type.
Variable L: Ensemble location.

Definition l_in_L (l:location) := l ∈ L.

(*Definition 7: Subscribers*)

Definition s:
           location ->
           Ensemble topic ->
           location*Ensemble topic
  := forall l ψl, (l_in_L l) /\ (ψl ⊆ Tau) => (l,ψl).






