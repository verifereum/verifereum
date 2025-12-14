open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2408";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToReturn1.json";
val defs = mapi (define_test "2408") tests;
val () = export_theory_no_docs ();
