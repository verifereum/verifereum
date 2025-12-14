open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0123";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/identity_precompile/test_call_identity_precompile.json";
val defs = mapi (define_test "0123") tests;
val () = export_theory_no_docs ();
