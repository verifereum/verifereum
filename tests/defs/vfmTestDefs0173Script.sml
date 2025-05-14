open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0173";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/invalid_length_g2msm.json";
val defs = mapi (define_test "0173") tests;
val () = export_theory_no_docs ();
