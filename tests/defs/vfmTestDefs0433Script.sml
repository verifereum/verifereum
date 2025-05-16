open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0433";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/smodNonConst.json";
val defs = mapi (define_test "0433") tests;
val () = export_theory_no_docs ();
