open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0929";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashCreatedAndDeletedAccount.json";
val defs = mapi (define_test "0929") tests;
val () = export_theory_no_docs ();
