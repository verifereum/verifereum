open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2541";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_TransactionCALL.json";
val defs = mapi (define_test "2541") tests;
val () = export_theory_no_docs ();
