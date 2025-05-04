open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs117";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/invalid_length_g2msm.json";
val defs = mapi (define_state_test "117") tests;
val () = export_theory_no_docs ();
