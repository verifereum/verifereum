open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0083";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip4844_blobs/test_precompile_during_fork.json";
val defs = mapi (define_test "0083") tests;
val () = export_theory_no_docs ();
