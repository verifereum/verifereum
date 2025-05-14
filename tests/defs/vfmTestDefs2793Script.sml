open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2793";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_point_match_5.json";
val defs = mapi (define_test "2793") tests;
val () = export_theory_no_docs ();
