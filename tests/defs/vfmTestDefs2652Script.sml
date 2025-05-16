open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2652";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_empty_data_insufficient_gas.json";
val defs = mapi (define_test "2652") tests;
val () = export_theory_no_docs ();
