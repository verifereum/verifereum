open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1088";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/TransactionCreateRandomInitCode.json";
val defs = mapi (define_test "1088") tests;
val () = export_theory_no_docs ();
