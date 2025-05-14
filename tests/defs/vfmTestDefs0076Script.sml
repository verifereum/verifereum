open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0076";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/point_evaluation_precompile/external_vectors.json";
val defs = mapi (define_test "0076") tests;
val () = export_theory_no_docs ();
