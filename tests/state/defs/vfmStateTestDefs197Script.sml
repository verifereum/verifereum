open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs197";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip6780_selfdestruct/selfdestruct/self_destructing_initcode.json";
val defs = mapi (define_state_test "197") tests;
val () = export_theory_no_docs ();
