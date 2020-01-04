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
Inductive DATA_VALUE (tdv:Type) : Type :=  cdv: tdv -> DATA_VALUE tdv.
(*D is the set of all DATA_VALUE, such that d is an element of it*)
Record valid_d (tdv: Type)(D: Ensemble (DATA_VALUE tdv)): Type :=
  {
    d: DATA_VALUE tdv;
    d_in_D: d ∈ D;
  }.

(*Definition 3: Events*)
(*A pair of a DATA_VALUE and a TIMESTAMP is denoted by e, which stands for event *)

Definition valid_e (tdv: Type)(D: Ensemble (DATA_VALUE tdv)) := pair (valid_d _ D)  nat.

Definition valid_e_in_E (tdv: Type)(D: Ensemble (DATA_VALUE tdv))(E: Ensemble (Type*Set)): Prop :=
 (valid_e tdv D) ∈ E.

(*Definition 4: Event-buffers*)
(*An event buffer is a subset of E, being it denoted by b  *)

Record valid_b (tdv: Type)(E: Ensemble (tdv*Set)) :=
  {
    b: Ensemble (tdv*Set);
    b_included_E: b ⊆ E;
  }.

(*Set Printing Projections.*)

(*B denotes the set of all event buffers, which are themselves sets of events*)
(*
Definition valid_b_in_B (tdv: Type)(B: Ensemble (Ensemble (tdv*Set)))(E: Ensemble (tdv*Set))
  := b tdv ∈ B.

Print valid_b.
*)

(*Definition 5: Topics*)
(*A TOPIC is used to categorize DATA_VALUEs *)
Inductive TOPIC (tτ:Type) : Type :=  cτ: tτ -> TOPIC tτ.
Record valid_τ (tτ:Type)(Tau: Ensemble (TOPIC tτ))
  :=
    {
      τ: TOPIC tτ;
      τ_in_Tau: τ ∈ Tau ;
    }.

(*Definition 6: Locations*)
(*A LOCATION denotes a unique identifier of an entity in the system*)
Inductive LOCATION (tl: Set): Set := cl: tl -> LOCATION tl.
Record valid_l (tl: Set)(L: Ensemble (LOCATION tl)): Set
  :=
    {
      l: LOCATION tl;
      l_in_L: l ∈ L;
    }.

Print valid_l.

Set Printing Projections.

(*Definition 7: Subscribers*)

Definition valid_ψ (tτ: Type)(Tau: Ensemble (TOPIC tτ)) := forall ψl: Ensemble (TOPIC tτ), ψl ⊆ Tau.

Definition valid_s
       (tτ: Type)
       (tl: Set)
       (Tau ψl: Ensemble (TOPIC tτ))
       (L: Ensemble (LOCATION tl))
  : (valid_ψ _ Tau) -> Set*(Ensemble (TOPIC tτ))
  := fun H => pair (valid_l tl L) ψl .

Print valid_s.

Definition valid_s_in_S (tl: Set) (tτ: Type)(s: tl*(Ensemble (TOPIC tτ)))(S: Ensemble (tl*(Ensemble (TOPIC tτ))))
  := s ∈ S.

Definition ident := term.

(*
Record subscriber
       (tτ: Type)
       (tl: Set)
       (Tau ψl: Ensemble (TOPIC tτ))
       (L: Ensemble (LOCATION tl))
       (vl: valid_l (tl)(L))
  :=
    {
      ψl_in_Tau: ψl ⊆ Tau;
      s: pair (vl.(l)) (ψl);
    }.


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
