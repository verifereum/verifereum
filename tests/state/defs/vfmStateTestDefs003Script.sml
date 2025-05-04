open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs003";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/basic_tload/basic_tload_gasprice.json";
val defs = mapi (define_state_test "003") tests;
val () = export_theory_no_docs ();
