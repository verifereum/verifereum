open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2926";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_1-2_2_21000_96.json";
val defs = mapi (define_test "2926") tests;
val () = export_theory_no_docs ();
