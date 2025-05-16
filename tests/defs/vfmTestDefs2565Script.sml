open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2565";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_9935_21000_128.json";
val defs = mapi (define_test "2565") tests;
val () = export_theory_no_docs ();
