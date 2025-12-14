open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2386";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/ABAcalls3.json";
val defs = mapi (define_test "2386") tests;
val () = export_theory_no_docs ();
