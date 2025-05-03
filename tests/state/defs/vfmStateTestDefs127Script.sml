open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs127";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/valid_gas_g1msm.json";
val defs = mapi (define_state_test "127") tests;
val () = export_theory_no_docs ();
