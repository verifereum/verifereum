open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2558";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/Opcodes_TransactionInit.json";
val defs = mapi (define_test "2558") tests;
val () = export_theory_no_docs ();
