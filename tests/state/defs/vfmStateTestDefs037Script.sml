open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs037";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/point_evaluation_precompile/tx_entry_point.json";
val defs = mapi (define_state_test "037") tests;
val () = export_theory_no_docs ();
