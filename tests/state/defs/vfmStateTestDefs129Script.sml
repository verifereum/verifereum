open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs129";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/berlin/eip2930_access_list/acl/access_list.json";
val defs = mapi (define_state_test "129") tests;
val () = export_theory_no_docs ();
