open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2651";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_empty_data.json";
val defs = mapi (define_test "2651") tests;
val () = export_theory_no_docs ();
