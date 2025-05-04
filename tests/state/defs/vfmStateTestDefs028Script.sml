open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs028";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/invalid_normal_gas.json";
val defs = mapi (define_state_test "028") tests;
val () = export_theory_no_docs ();
