open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2039";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertSubCallStorageOOG.json";
val defs = mapi (define_test "2039") tests;
val () = export_theory_no_docs ();
