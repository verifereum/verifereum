open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2397";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/doubleSelfdestructTest.json";
val defs = mapi (define_test "2397") tests;
val () = export_theory_no_docs ();
