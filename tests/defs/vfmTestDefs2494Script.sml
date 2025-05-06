open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2494";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/callcodeTo0.json";
val defs = mapi (define_test "2494") tests;
val () = export_theory_no_docs ();
