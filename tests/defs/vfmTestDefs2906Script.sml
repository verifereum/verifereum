open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2906";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_9935_21000_96.json";
val defs = mapi (define_test "2906") tests;
val () = export_theory_no_docs ();
