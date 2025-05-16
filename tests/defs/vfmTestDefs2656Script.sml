open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2656";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_one_point_not_in_subgroup.json";
val defs = mapi (define_test "2656") tests;
val () = export_theory_no_docs ();
