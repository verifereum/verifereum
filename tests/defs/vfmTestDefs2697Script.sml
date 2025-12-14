open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2697";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_perturb_g2_by_field_modulus_again.json";
val defs = mapi (define_test "2697") tests;
val () = export_theory_no_docs ();
