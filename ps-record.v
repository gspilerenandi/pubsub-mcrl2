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

(*Definition 1: data values*)
(*DATA_VALUE denotes the type of data which is gathered by nodes in the system*)
Inductive DATA_VALUE (tdv:Type) : Type :=  cdv: tdv -> DATA_VALUE tdv.
(*Being a valid DATA_VALUE means being part of a valid set of DATA_VALUEs, which is given by D*)
Record d (tdv: Type)(D: Ensemble (DATA_VALUE tdv)): Type :=
  {
    d': DATA_VALUE tdv;
    d_in_D: d' ∈ D;
  }.

(*Definition 3: Events*)
(*An event is a pair of a valid data value and a timestamp (nat)*)
Definition e (tdv: Type)(D: Ensemble (DATA_VALUE tdv)) := pair (d _ D)  nat.

Definition e_in_E (tdv: Type)(D: Ensemble (DATA_VALUE tdv))(E: Ensemble (Type*Set)): Prop
  := (e tdv D) ∈ E.

(*Definition 4: Event-buffers*)
(*An event buffer is a subset of E, being it denoted by b*)
Record b (tdv: Type)(E: Ensemble (Type*Set)) :=
  {
    b': Ensemble (Type*Set);
    b_included_E: b' ⊆ E;
  }.


(*B is the superset of all event buffers b*)
(*
Definition b_in_B (tdv: Type)(B: Ensemble (Ensemble (Type*Set)))(E: Ensemble (Type*Set))
  := (b tdv E).(cb) ∈ B.
*)

(*Definition 5: Topics*)
(*A TOPIC is used to categorize DATA_VALUEs *)
Inductive TOPIC (tτ:Type) : Type :=  cτ: tτ -> TOPIC tτ.
Record τ (tτ:Type)(Tau: Ensemble (TOPIC tτ)) :=
  {
    τ': TOPIC tτ;
    τ_in_Tau: τ' ∈ Tau ;
  }.

(*Definition 6: Locations*)
(*A LOCATION denotes a unique identifier of an entity in the system*)
Inductive LOCATION (tl: Set): Set := cl: tl -> LOCATION tl.
Record l (tl: Set)(L: Ensemble (LOCATION tl)): Set :=
  {
    l': LOCATION tl;
    l_in_L: l' ∈ L;
  }.

(*Definition 7: Subscribers*)
(*A subscriber s is a pair of a LOCATION l and a set of TOPICs, which is is given by ψ*)
Definition ψ (tτ: Type)(Tau: Ensemble (TOPIC tτ)) := forall ψl: Ensemble (TOPIC tτ), ψl ⊆ Tau.

Definition s
       (tτ: Type)
       (tl: Set)
       (Tau ψl: Ensemble (TOPIC tτ))
       (L: Ensemble (LOCATION tl))
  : (ψ _ Tau) -> Set*(Ensemble (TOPIC tτ))
  := fun H => pair (l _  L) ψl .

Definition s_in_S
           (tl: Set)
           (tτ: Type)
           (s: tl*(Ensemble (TOPIC tτ)))
           (S: Ensemble (tl*(Ensemble (TOPIC tτ))))
  := s ∈ S.

Definition L_prodcart_Tau
           (tl: Set)
           (tτ: Type)
           (L: Ensemble (LOCATION tl))
           (Tau: Ensemble (TOPIC tτ))
  : Ensemble(LOCATION tl * TOPIC tτ)
  := prod_cart (LOCATION tl)(TOPIC tτ)(L)(Tau).

Definition Tau_prodcart_L
           (tl: Set)
           (tτ: Type)
           (Tau: Ensemble (TOPIC tτ))
           (L: Ensemble (LOCATION tl))
  : Ensemble(TOPIC tτ * LOCATION tl)
  := prod_cart (TOPIC tτ)(LOCATION tl)(Tau)(L).

Definition Brk
           (tl: Set)
           (tτ: Type)
           (L: Ensemble (LOCATION tl))
           (Tau: Ensemble(TOPIC tτ))
  := pair (LOCATION tl)(prod_cart
                          (Ensemble (LOCATION tl * TOPIC tτ))
                          (_)
                          (Singleton (Ensemble (L_prodcart_Tau (_)(_)(L)(Tau))))
                          (Singleton (Ensemble (Tau_prodcart_L (_)(_)(Tau)(L))))
                        ).

(*
(LOCATION tl * TOPIC tτ)
Ensemble (pair (LOCATION tl) (TOPIC tτ))
Ensemble (pair (TOPIC tτ) (LOCATION tl))
(*Set of pairs of LOCATIONs and TOPICs, which represent the publishers that publish on a topic*)

(*An instance of a broker defined, brk ⊆ {l, {}, {}} *)
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

*)
