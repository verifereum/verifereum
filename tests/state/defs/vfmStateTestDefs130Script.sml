open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs130";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/opcodes/all_opcodes/all_opcodes.json";
val defs = mapi (define_state_test "130") tests;
val () = export_theory_no_docs ();
