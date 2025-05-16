open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2431";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/CreateTransactionSuccess.json";
val defs = mapi (define_test "2431") tests;
val () = export_theory_no_docs ();
