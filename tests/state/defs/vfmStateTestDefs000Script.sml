open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs000";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/berlin/eip2930_access_list/acl/access_list.json";
val defs = mapi (define_state_test "000") tests;
val () = export_theory_no_docs ();
