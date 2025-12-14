open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0257";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_valid_gas_g1msm.json";
val defs = mapi (define_test "0257") tests;
val () = export_theory_no_docs ();
