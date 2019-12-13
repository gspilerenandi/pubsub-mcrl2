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
(*DATA_VALUE denotes the type of data which is gathered by nodes in the system*)
Inductive DATA_VALUE
          (tdv:Type)
  : Type
  := |cdv: tdv -> DATA_VALUE tdv.

(*D is the set of all DATA_VALUE, such that d is an element of it*)
Definition d_in_D
           (tdv: Type)
           (d: DATA_VALUE tdv)
           (D: Ensemble (DATA_VALUE tdv))
  := d ∈ D.

(*Definition 2: timestamps*)
(*TIMESTAMP is the representation of time that is adopted by the system*)
Inductive TIMESTAMP
  := |cdtime: nat -> TIMESTAMP.

(*T is the set of all TIMESTAMPs recorded by the system, such that t is an element of it*)
Definition t_in_Tset
           (t: TIMESTAMP)
           (T: Ensemble TIMESTAMP)
  := t ∈ T.

(*Definition 3: Events*)
(*A pair of a DATA_VALUE and a TIMESTAMP is denoted by e, which stands for event *)
Definition e
           (tdv: Type)
           (d: DATA_VALUE tdv )
           (t: TIMESTAMP)
  : DATA_VALUE tdv *TIMESTAMP
  := (d,t).
(*E is the set of all EVENTs recorded by the system *)
Definition e_in_E
           (tdv: Type)
           (e:DATA_VALUE tdv*TIMESTAMP)
           (E: Ensemble(DATA_VALUE tdv * TIMESTAMP))
  := e ∈ E.

(*DxT is the cartesian product of the sets D by T*)
Definition DxT
           (tdv: Type)
           (D: Ensemble (DATA_VALUE tdv))
           (T: Ensemble TIMESTAMP)
  : Ensemble(DATA_VALUE tdv*TIMESTAMP)
  := prod_cart (DATA_VALUE tdv)(TIMESTAMP)(D)(T).

(*The set E of all events is included in the cartesian product DxT *)
Definition E_included_DxT
           (tdv: Type)
           (E:Ensemble(DATA_VALUE tdv * TIMESTAMP))
           (D: Ensemble (DATA_VALUE tdv))
           (T: Ensemble TIMESTAMP)
  : Prop
  := E ⊆ DxT tdv D T.

(*Definition 4: Event-buffers*)
(*An event buffer is a subset of E, being it denoted by b  *)
Definition b_included_E
           (tdv: Type)
           (b: Ensemble (DATA_VALUE tdv * TIMESTAMP))
           (E: Ensemble(DATA_VALUE tdv * TIMESTAMP))
  := b ⊆ E.

(*B denotes the set of all event buffers, which are themselves sets of events*)
Definition b_in_B
           (tdv: Type)
           (b: Ensemble (DATA_VALUE tdv * TIMESTAMP))
           (B: Ensemble (Ensemble (DATA_VALUE tdv * TIMESTAMP)))
  := b ∈ B.

(*Definition 5: Topics*)
(*A TOPIC is used to categorize DATA_VALUEs *)
Inductive TOPIC
          (tτ: Type)
  : Type
  :=|ctpc: tτ -> TOPIC tτ.

(*Tau denotes the set of all TOPICs*)
Definition τ_in_Tau
           (tτ: Type)
           (τ: TOPIC tτ)
           (Tau: Ensemble (TOPIC tτ))
  := τ ∈ Tau.

(*Definition 6: Locations*)
(*A LOCATION denotes a unique identifier of an entity in the system*)
Inductive LOCATION  
  :=|cloc: nat -> LOCATION.
(*L denotes the set of all LOCATIONs*)
Definition l_in_L
           (l:LOCATION)
           (L: Ensemble LOCATION)
  := l ∈ L.

(*Definition 7: Subscribers*)
(*A subscriber is denoted by s, which is composed by a location l and a set of topics of its interest ψl*)
Definition s
           (l:LOCATION)
           (tτ: Type)
           (ψl:Ensemble (TOPIC tτ))
           (Tau: Ensemble (TOPIC tτ))
           (L: Ensemble LOCATION)
  : (ψl ⊆ Tau ) /\ (l_in_L l L) -> (LOCATION * Ensemble (TOPIC tτ))
  := fun H => (l,ψl).

(*S denotes the set of all subscribers*)
Definition s_in_S
           (l:LOCATION)
           (tτ: Type)
           (ψl:Ensemble (TOPIC tτ))
           (s:LOCATION * Ensemble (TOPIC tτ))
           (S: Ensemble (LOCATION * Ensemble (TOPIC tτ)))
  := s ∈ S.

Notation "∅" := (Empty_set)(at level 0).






