open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2593";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_340282366920938463463374607431768211456_28000_80.json";
val defs = mapi (define_test "2593") tests;
val () = export_theory_no_docs ();
