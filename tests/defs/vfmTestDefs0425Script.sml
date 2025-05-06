open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0425";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stArgsZeroOneBalance/sdivNonConst.json";
val defs = mapi (define_test "0425") tests;
val () = export_theory_no_docs ();
