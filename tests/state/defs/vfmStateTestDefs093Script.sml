open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs093";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip2537_bls_12_381_precompiles/bls12_g2msm/call_types.json";
val defs = mapi (define_state_test "093") tests;
val () = export_theory_no_docs ();
