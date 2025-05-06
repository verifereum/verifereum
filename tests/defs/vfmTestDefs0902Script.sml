open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0902";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/TransactionCollisionToEmpty2.json";
val defs = mapi (define_test "0902") tests;
val () = export_theory_no_docs ();
