% File: mk_proof.ml %


% create proofaux theory %
loadf `Proofaux/mk_proofaux1`;;
loadf `Proofaux/mk_proofaux2`;;
close_theory();;

% create Type theory %
loadf `Type/mk_Type1`;;
loadf `Type/Type_convs`;;
loadf `Type/mk_Type2`;;
loadf `defs/ld_pair`;;
loadf `Type/mk_Type3`;;
close_theory();;

% create Pterm theory %
loadf `Pterm/mk_Pterm1`;;
loadf `Pterm/mk_Pterm2`;;
close_theory();;

% create inference theory %
loadf `Inference/mk_inference1`;;
close_theory();;

% create proof theory %
loadf `Proof/proof_convs`;;
loadf `Proof/mk_proof1`;;
loadf `Proof/mk_proof2`;;
loadf `Proof/mk_proof3`;;
close_theory();;

% create derived theory %
loadf `Derived/mk_derived1`;;
loadf `Derived/mk_derived2`;;
close_theory();;

% Extra stuff for automatic proof and pretty-printing %
loadf `Rules/mk_proof_pretty`;;
loadf `Rules/mk_proof_rules1`;;
loadf `Rules/mk_proof_rules2`;;
