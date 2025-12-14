open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1994";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSStoreTest/sstore_changeFromExternalCallInInitCode.json";
val defs = mapi (define_test "1994") tests;
val () = export_theory_no_docs ();
