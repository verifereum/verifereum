open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2776";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_one_point_with_g2_zero.json";
val defs = mapi (define_test "2776") tests;
val () = export_theory_no_docs ();
