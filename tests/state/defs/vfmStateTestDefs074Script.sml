open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs074";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/istanbul/eip152_blake2/blake2/blake2b_gas_limit.json";
val defs = mapi (define_state_test "074") tests;
val () = export_theory_no_docs ();
