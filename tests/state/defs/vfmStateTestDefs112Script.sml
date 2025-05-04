open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs112";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip2537_bls_12_381_precompiles/bls12_precompiles_before_fork/precompile_before_fork.json";
val defs = mapi (define_state_test "112") tests;
val () = export_theory_no_docs ();
