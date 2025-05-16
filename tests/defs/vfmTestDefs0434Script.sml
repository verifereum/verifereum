open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0434";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/sstoreNonConst.json";
val defs = mapi (define_test "0434") tests;
val () = export_theory_no_docs ();
