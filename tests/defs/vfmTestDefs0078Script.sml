open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0078";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/point_evaluation_precompile/precompile_during_fork.json";
val defs = mapi (define_test "0078") tests;
val () = export_theory_no_docs ();
