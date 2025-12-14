open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0255";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_precompile_before_fork.json";
val defs = mapi (define_test "0255") tests;
val () = export_theory_no_docs ();
