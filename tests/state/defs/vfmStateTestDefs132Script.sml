open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs132";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/opcodes/calldatacopy/calldatacopy.json";
val defs = mapi (define_state_test "132") tests;
val () = export_theory_no_docs ();
