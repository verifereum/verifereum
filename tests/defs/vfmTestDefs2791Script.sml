open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2791";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_points_with_one_g2_zero.json";
val defs = mapi (define_test "2791") tests;
val () = export_theory_no_docs ();
