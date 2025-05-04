open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs076";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/istanbul/eip152_blake2/blake2/blake2b_large_gas_limit.json";
val defs = mapi (define_state_test "076") tests;
val () = export_theory_no_docs ();
