open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs111";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp2_to_g2/valid.json";
val defs = mapi (define_state_test "111") tests;
val () = export_theory_no_docs ();
