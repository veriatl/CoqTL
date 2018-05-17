Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.

Set Implicit Arguments.

Class TransformationEngineTypeClass (TransformationDef: Type) (SourceModel: Type) (TargetModel: Type) (RuleDef: Type) (SourceModelElement: Type) (SourceModelLink: Type) (SourceModel: Type) (TargetModelElement: Type) (TargetModelLink: Type) (TargetModel: Type) :=
  {
    executeFun: TransformationDef -> SourceModel -> TargetModel;
    getRulesFun: TransformationDef -> list RuleDef;
    instantiateRuleOnPatternFun: RuleDef -> list SourceModelElement -> SourceModel -> list TargetModelElement; 
    matchPatternFun: TransformationDef -> list SourceModelElement -> SourceModel -> option RuleDef;  
    allSourceModelElements: SourceModel -> list SourceModelElement;
    allTargetModelElements: TargetModel -> list TargetModelElement;

    tr_surj' : 
    forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
      tm = executeFun tr sm -> In t1 (allTargetModelElements tm) ->
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleDef),
        In r (getRulesFun tr) /\
        In t1 tp /\
        instantiateRuleOnPatternFun r sp sm = tp /\
        incl sp (allSourceModelElements sm) /\
        incl tp (allTargetModelElements tm) /\
        matchPatternFun tr sp sm = Some r )
  }.