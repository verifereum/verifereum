open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs071";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/homestead/yul/yul_example/yul.json";
val defs = mapi (define_state_test "071") tests;
val () = export_theory_no_docs ();
