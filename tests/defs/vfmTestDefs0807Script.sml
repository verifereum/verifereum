open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0807";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCodeCopyTest/ExtCodeCopyTestsParis.json";
val defs = mapi (define_test "0807") tests;
val () = export_theory_no_docs ();
