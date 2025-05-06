open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2915";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_1-2_0_21000_80.json";
val defs = mapi (define_test "2915") tests;
val () = export_theory_no_docs ();
