open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1121";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log3_MaxTopic.json";
val defs = mapi (define_test "1121") tests;
val () = export_theory_no_docs ();
