open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0994";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_MaxTopic.json";
val defs = mapi (define_test "0994") tests;
val () = export_theory_no_docs ();
