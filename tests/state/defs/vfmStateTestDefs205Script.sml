open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs205";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/homestead/yul/yul_example/yul.json";
val defs = mapi (define_state_test "205") tests;
val () = export_theory_no_docs ();
