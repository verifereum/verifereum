open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0079";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/point_evaluation_precompile/tx_entry_point.json";
val defs = mapi (define_test "0079") tests;
val () = export_theory_no_docs ();
