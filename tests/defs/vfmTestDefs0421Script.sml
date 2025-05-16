open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0421";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/mstoreNonConst.json";
val defs = mapi (define_test "0421") tests;
val () = export_theory_no_docs ();
