open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs080";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/gas/account_warming.json";
val defs = mapi (define_state_test "080") tests;
val () = export_theory_no_docs ();
