open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0420";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/mstore8NonConst.json";
val defs = mapi (define_test "0420") tests;
val () = export_theory_no_docs ();
