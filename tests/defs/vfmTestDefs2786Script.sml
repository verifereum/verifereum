open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2786";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_three_point_match_1.json";
val defs = mapi (define_test "2786") tests;
val () = export_theory_no_docs ();
