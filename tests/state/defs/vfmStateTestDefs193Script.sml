open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs193";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/dynamic_create2_selfdestruct_collision/dynamic_create2_selfdestruct_collision.json";
val defs = mapi (define_state_test "193") tests;
val () = export_theory_no_docs ();
