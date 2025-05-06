open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0398";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/calldataloadNonConst.json";
val defs = mapi (define_test "0398") tests;
val () = export_theory_no_docs ();
