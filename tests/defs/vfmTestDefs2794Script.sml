open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2794";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_two_point_oog.json";
val defs = mapi (define_test "2794") tests;
val () = export_theory_no_docs ();
