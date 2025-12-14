open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0252";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/test_invalid_zero_length_g2msm.json";
val defs = mapi (define_test "0252") tests;
val () = export_theory_no_docs ();
