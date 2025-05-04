open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs129";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/prague/eip7702_set_code_tx/gas/account_warming.json";
val defs = mapi (define_state_test "129") tests;
val () = export_theory_no_docs ();
