open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2709";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_5616_21000_128.json";
val defs = mapi (define_test "2709") tests;
val () = export_theory_no_docs ();
