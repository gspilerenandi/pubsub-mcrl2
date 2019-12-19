Require Import Ensembles.
Require List.
Require Import Powerset.

Locate In.

Notation "x ∈ y" := (@In _ y x)(at level 30).

Notation "x ⊆ y" := (Included _ x y)(at level 31).

Notation "∅" := (Empty_set)(at level 0).

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
Record valid_d (tdv: Type):= {d: DATA_VALUE tdv; D: Ensemble (DATA_VALUE tdv); d_in_D: d ∈ D;}.

Print d.

(*Definition 2: timestamps*)
(*TIMESTAMP is the representation of time that is adopted by the system*)
Inductive TIMESTAMP
  := |cdtime: nat -> TIMESTAMP.

(*T is the set of all TIMESTAMPs recorded by the system, such that t is an element of it*)
Record valid_t (t: TIMESTAMP ): Type := {T: Ensemble TIMESTAMP; t_in_T: t ∈ T;}.

(*Definition 3: Events*)
(*A pair of a DATA_VALUE and a TIMESTAMP is denoted by e, which stands for event *)

Record valid_e (tdv: Type) (d: DATA_VALUE tdv) (t: TIMESTAMP): Type := {E: Ensemble(DATA_VALUE tdv * TIMESTAMP); e: d*t; e_in_E: e ∈ E}.

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
(*A subscriber is denoted by s, which is composed by a location l, which should belong to the set of all LOCATIONs L and a set of topics of its interest ψl, which should be a subset of all TOPICs Tau*)
Definition s
           (l:LOCATION)
           (tτ: Type)
           (ψl:Ensemble (TOPIC tτ))
           (Tau: Ensemble (TOPIC tτ))
           (L: Ensemble LOCATION)
  : (ψl ⊆ Tau ) /\ (l_in_L l L) -> (LOCATION * Ensemble (TOPIC tτ))
  := fun H => (l,ψl).


(*Defining the set of all subscribers*)
Definition S
           (tτ: Type)
           (L: Ensemble LOCATION)
           (Tau: Ensemble (TOPIC tτ))
  : Ensemble (Ensemble LOCATION * Ensemble (Ensemble (TOPIC tτ) ) )
  := prod_cart
       ( Ensemble LOCATION)
       ( Ensemble (Ensemble (TOPIC tτ) ) )
       ( Singleton  (Ensemble LOCATION) L )
       ( Singleton (Ensemble (Ensemble (TOPIC tτ) )) (Power_set (TOPIC tτ) (Tau) ) ).

(*S denotes the set of all subscribers*)
Definition s_in_S
           (tτ: Type)
           (s: LOCATION * Ensemble (TOPIC tτ))
           (S: Ensemble (LOCATION * Ensemble (TOPIC tτ)))
  := s ∈ S.

(*Set of pairs of LOCATIONs and TOPICs, which represent the publishers that publish on a topic*)
Definition LxTau
           (tτ: Type)
           (L: Ensemble (LOCATION))
           (Tau: Ensemble (TOPIC tτ))
  : Ensemble(LOCATION * TOPIC tτ)
  := prod_cart (LOCATION)(TOPIC tτ)(L)(Tau).


(*Set of pairs of TOPICs and LOCATIONs, which represent the subscribers that subscribe to a topic*)
Definition TauxL
           (tτ: Type)
           (Tau: Ensemble (TOPIC tτ))
           (L: Ensemble (LOCATION))
  : Ensemble(TOPIC tτ * LOCATION)
  := prod_cart (TOPIC tτ)(LOCATION)(Tau)(L).

(*An instance of a broker defined, brk = (l, {}, {}) *)
Definition brk
           (tτ: Type)
           (l: LOCATION)
           (L: Ensemble LOCATION)
           (Tau: Ensemble(TOPIC tτ))
  : Ensemble ( LOCATION * ( Ensemble (LOCATION * TOPIC tτ) * Ensemble (TOPIC tτ * LOCATION) ) )
  := prod_cart
       (LOCATION)
       ((Ensemble (LOCATION * (TOPIC tτ)) * Ensemble ((TOPIC tτ) * LOCATION)) )
       (Singleton LOCATION l)
       (prod_cart 
          (Ensemble (LOCATION * TOPIC tτ))
          (Ensemble (TOPIC tτ * LOCATION))
          (Singleton (Ensemble (LOCATION * TOPIC tτ)) ( LxTau (tτ)(L)(Tau) ) )
          (Singleton (Ensemble (TOPIC tτ * LOCATION)) ( TauxL (tτ)(Tau)(L) ) )  
       ).

Definition brk_in_BRK
           (tτ: Type)
           (l: LOCATION)
           (L: Ensemble LOCATION)
           (Tau: Ensemble(TOPIC tτ))
           (BRK: Ensemble ( Ensemble ( LOCATION * ( Ensemble (LOCATION * TOPIC tτ) * Ensemble (TOPIC tτ * LOCATION) ) ) ) )
  := term.