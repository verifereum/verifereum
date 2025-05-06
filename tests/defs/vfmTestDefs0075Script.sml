open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0075";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/point_evaluation_precompile/external_vectors.json";
val defs = mapi (define_test "0075") tests;
val () = export_theory_no_docs ();
