open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs098";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip2537_bls_12_381_precompiles/bls12_g2mul/invalid.json";
val defs = mapi (define_state_test "098") tests;
val () = export_theory_no_docs ();
