Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

(*Require Import core.Semantics.
Require Import core.Certification.*)
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Theorem Relational_id_definedness :
forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)   (forall (c1 : ClassMetamodel_EObject), In c1 (allModelElements cm) -> ClassMetamodel_getId c1 > 0) ->
  (* postcondition *)  (forall (t1 : RelationalMetamodel_EObject), In t1 (allModelElements rm) -> RelationalMetamodel_getId t1 > 0). 
Proof.
  (** Clean context *)
  intros cm rm H Hpre t1 Hintm.  
  remember H as tr.
  clear Heqtr.
  rewrite tr in Hintm.

  (* apply lemma *)
  apply tr_execute_in_elements in Hintm.
  destruct Hintm. destruct H0.

  apply tr_instantiatePattern_in in H1.
  destruct H1. rename x0 into r.
  destruct H1.

  destruct x.
  - crush.
  - unfold instantiateRuleOnPattern in H2.
    unfold instantiateIterationOnPattern in H2.
    destruct c eqn: c_ca.
    destruct c0 eqn: c0_ca.

    (* Class *)
    --  (* find rule for class *)
        unfold matchPattern in H1.
        simpl in H1.
        unfold matchRuleOnPattern in H1.
        simpl in H1.
        destruct x eqn: x_ca.
        --- simpl in H1.
            destruct H1.
            rewrite <- H1 in H2.
            simpl in H2.
            destruct H2.
            + clear H1.
              rewrite <- H2. simpl.
              specialize (Hpre c).
              (* TODO lemma: In sp allTuples -> Incl sp allmodelElem *)
              assert (incl [c] (allModelElements cm)).
              { rewrite <- c_ca in H0. 
                unfold allTuples in H0.
                apply tuples_up_to_n_incl with (n:=(maxArity Class2Relational)). assumption.
              }
              unfold incl in H1.
              specialize (H1 c).
              simpl in H1.
              crush.
            + inversion H2.
            + inversion H1.
        --- simpl in H1. inversion H1.

    (* Attribute *)
    --  (* find rule for attr *) 
        unfold matchPattern in H1.
        simpl in H1.
        unfold matchRuleOnPattern in H1.
        simpl in H1.
        destruct x eqn: x_ca.
        --- simpl in H1.
            destruct (negb (getAttributeDerived c1)) eqn:attr_ca.
            + destruct H1. 
              ++  rewrite <- H1 in H2.
                  simpl in H2.
                  destruct H2.
                  +++ clear H1.
                      rewrite <- H2. simpl.
                      specialize (Hpre c).
                      (* TODO lemma: In sp allTuples -> Incl sp allmodelElem *)
                      assert (incl [c] (allModelElements cm)).
                      { rewrite <- c_ca in H0. 
                        unfold allTuples in H0.
                        apply tuples_up_to_n_incl with (n:=(maxArity Class2Relational)). assumption.
                      }
                      unfold incl in H1.
                      specialize (H1 c).
                      simpl in H1.
                      crush.
                  +++ crush.
              ++  crush.
            + crush.
        --- simpl in H1. inversion H1.
Qed.  
