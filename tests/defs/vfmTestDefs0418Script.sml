open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0418";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/mloadNonConst.json";
val defs = mapi (define_test "0418") tests;
val () = export_theory_no_docs ();
