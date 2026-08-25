Theory vfmTestDefs0165[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7594_peerdas/test_invalid_max_blobs_per_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7594_peerdas/test_invalid_max_blobs_per_tx.json");
val defs = mapi (define_test "0165") tests;
