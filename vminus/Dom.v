(** * Dom: Graphs and Graph Dominators *)
(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import List Equalities Orders RelationClasses.
Require Import FSets FMaps.
Import ListNotations.
From Vminus Require Import Util.

(* ################################################################# *)
(** * GRAPH *)
(** Interface for a nonempty graph [t] with: 
     - a set of _vertices_ of type [V], defined by a membership predicate [Mem]
     - a distinguished _entry vertex_ [entry]
     - an _edge relation_ [Succ]
*)

Module Type GRAPH.
  Parameter Inline t V : Type.
  
  Parameter Inline entry : t -> V.
  Parameter Inline Succ : t -> V -> V -> Prop.
  Parameter Inline Mem : t -> V -> Prop.
End GRAPH.

(**  ------------------------------------------------------------------------- *)
(* ################################################################# *)
(** * Specification of Dominators *)

(** This is a relational specification of the graph dominance properties that 
    is convenient for proofs and intuitively captures the definitions. *)

Module Spec (Import G:GRAPH).

(** We first define a _path_ in the graph.

    [path g v1 v2 vs] means that there is a sequence of vertices
    starting from vertex [v1] and ending at [v2] that are connected by
    the [Succ] relation.  The vertices traversed on the path are those
    listed in [vs] (in reverse order).  
*)

  Inductive Path (g:G.t) : V -> V -> list V -> Prop :=
  | path_nil : forall v, 
      Mem g v -> Path g v v [v]
  | path_cons : forall v1 v2 v3 vs,
      Path g v1 v2 vs -> Mem g v3 -> Succ g v2 v3 
      -> Path g v1 v3 (v3::vs).

(**  ------------------------------------------------------------------------- *)  
(* ----------------------------------------------------------------- *)
(** *** Definition of domination *)

  (** Vertex [v1] _dominates_ vertex [v2] if every path starting 
      from the entry of the graph and ending at [v2] goes through [v1]. *)
  
  Definition Dom (g:G.t) (v1 v2: V) : Prop :=
    forall vs, Path g (entry g) v2 vs -> In v1 vs.

  (** Vertex [v1] _strictly dominates_ [v2] if they are distinct and 
     [v1] dominates [v2] *)
  
  Definition SDom (g:G.t) (v1 v2 : V) : Prop :=
    v1 <> v2 /\ Dom g v1 v2.


(**  ------------------------------------------------------------------------- *)  
(* ----------------------------------------------------------------- *)
(** *** Interaction of dominance and Succ *)

  (** The strict dominators of a vertex [v2] also dominate its predecessors. *)
  
  Lemma dom_step : forall g v1 v2,
    Mem g v2 -> Succ g v1 v2 -> forall v', SDom g v' v2 -> Dom g v' v1.
  Proof.
    unfold SDom, Dom. intros g v1 v2 Hmem Hsucc v' [Hneq Hdom] p Hp.
    cut (In v' (v2::p)). inversion 1; subst; intuition. 
    apply Hdom. eapply path_cons; eauto. 
  Qed.

End Spec.

(**  ------------------------------------------------------------------------- *)  
(* ################################################################# *)
(** * Computing Dominance Properties *)

(** As usual, if we want to run the dominance calculation, we need an executable
    version of the specification.  For dominance, we can think of an implementation
    as an function that takes a graph and produces a mapping that sends each
    vertex to its set of strict dominators.  Any correct implementation must be sound 
    (and complete) with respect to the relational spec defined above.  This 
    interface capture the requirements of such an implementation.

    Full soundness follows from an "unrolled" version of the [dom_step] property.
*)

Module Type Algdom (Import G:GRAPH).
  Module Import GS := Spec G.

  Declare Module E : UsualDecidableType with Definition t := V.
  Declare Module NS : FSetInterface.WS with Module E:=E.
  Module L := BoundedSet NS.
  Include EqLeNotation L.

  Parameter calc_sdom : G.t -> option (V -> L.t).

  Axiom entry_sound : forall g sdom,
    calc_sdom g = Some sdom ->
    sdom (entry g) == L.top.

  Axiom successors_sound : forall g sdom n1 n2,
    calc_sdom g = Some sdom ->
    Mem g n1 -> Mem g n2 -> Succ g n1 n2 -> 
    L.union (L.singleton n1) (sdom n1) <= sdom n2.

  Axiom complete : forall g sdom n1 n2,
    calc_sdom g = Some sdom ->
    SDom g n1 n2 -> L.In n1 (sdom n2).

End Algdom.

(**  ------------------------------------------------------------------------- *)  
(* ################################################################# *)
(** * Full Soundness *)

(** The full soundness result follows as a corollary of the [entry_sound] and
    [successors_sound] properties of [Algdom].
*)

Module AlgdomProperties (Import G:GRAPH) (Import A : Algdom G).
  Module Import GS := Spec G.

  Lemma sound : forall g sdom n1 n2,
    calc_sdom g = Some sdom ->              
    L.In n1 (sdom n2) -> Dom g n1 n2.
  Proof.
    red; intros. remember (entry g). induction H1. subst.
    pose proof entry_sound g sdom H. 

    destruct (sdom (entry g)); try contradiction; simpl in *.
      exfalso. rewrite H2 in H0. eapply L.SFacts.empty_iff. eauto.
      
    right. destruct (E.eq_dec v2 n1). subst. inversion H1; intuition.
    apply IHPath; auto.

    destruct (sdom v2) eqn:Heqv2; simpl in *; auto.
    cut (NS.In n1 (NS.union (NS.singleton v2) t0)).
    intro Hin. apply NS.union_1 in Hin as [Hin | Hin]; auto.
    contradict n. apply NS.singleton_1. assumption.

    pose proof successors_sound g sdom v2 v3 as Hss.
    simpl in Hss. rewrite Heqv2 in Hss. simpl in Hss.
    destruct (sdom v3). apply Hss; inversion H1; eauto.
    exfalso. apply Hss; inversion H1; eauto.
  Qed.

End AlgdomProperties.

