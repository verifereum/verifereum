open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1094";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/TransactionCreateSuicideInInitcode.json";
val defs = mapi (define_test "1094") tests;
val () = export_theory_no_docs ();
