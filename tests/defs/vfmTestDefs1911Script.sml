open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1911";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrecompiledTouch_noncestorage.json";
val defs = mapi (define_test "1911") tests;
val () = export_theory_no_docs ();
