open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs007";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/shanghai/eip3860_initcode/with_eof/legacy_create_edge_code_size.json";
val defs = mapi (define_state_test "007") tests;
val () = export_theory_no_docs ();
