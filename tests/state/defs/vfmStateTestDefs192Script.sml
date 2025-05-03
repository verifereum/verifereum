open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs192";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/point_evaluation_precompile/call_opcode_types.json";
val defs = mapi (define_state_test "192") tests;
val () = export_theory_no_docs ();
