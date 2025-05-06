open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0081";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/point_evaluation_precompile_gas/point_evaluation_precompile_gas_usage.json";
val defs = mapi (define_test "0081") tests;
val () = export_theory_no_docs ();
