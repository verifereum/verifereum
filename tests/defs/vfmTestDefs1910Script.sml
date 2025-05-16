open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1910";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrecompiledTouch_nonce.json";
val defs = mapi (define_test "1910") tests;
val () = export_theory_no_docs ();
