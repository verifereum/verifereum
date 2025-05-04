open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs077";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/istanbul/eip152_blake2/blake2_delegatecall/blake2_precompile_delegatecall.json";
val defs = mapi (define_state_test "077") tests;
val () = export_theory_no_docs ();
