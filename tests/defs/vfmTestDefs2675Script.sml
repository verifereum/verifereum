open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2675";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-2_5616_21000_128.json";
val defs = mapi (define_test "2675") tests;
val () = export_theory_no_docs ();
