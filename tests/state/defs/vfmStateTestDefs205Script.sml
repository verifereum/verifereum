open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs205";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/shanghai/eip3860_initcode/initcode/gas_usage.json";
val defs = mapi (define_state_test "205") tests;
val () = export_theory_no_docs ();
