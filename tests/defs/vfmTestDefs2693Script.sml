open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2693";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_1-3_0_21000_80.json";
val defs = mapi (define_test "2693") tests;
val () = export_theory_no_docs ();
