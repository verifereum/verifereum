open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2352";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/Call10.json";
val defs = mapi (define_test "2352") tests;
val () = export_theory_no_docs ();
