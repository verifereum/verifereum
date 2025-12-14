open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0156";
val tests = json_path_to_tests "../fixtures/blockchain_tests/homestead/identity_precompile/test_identity_return_overwrite.json";
val defs = mapi (define_test "0156") tests;
val () = export_theory_no_docs ();
