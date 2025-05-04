open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs114";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/invalid_gas_g2msm.json";
val defs = mapi (define_state_test "114") tests;
val () = export_theory_no_docs ();
