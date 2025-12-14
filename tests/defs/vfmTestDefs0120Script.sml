open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0120";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/create/test_create_suicide_during_transaction_create.json";
val defs = mapi (define_test "0120") tests;
val () = export_theory_no_docs ();
