Theory vfmTestDefs1167[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/osaka/eip7594_peerdas/max_blob_per_tx/invalid_max_blobs_per_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/osaka/eip7594_peerdas/max_blob_per_tx/invalid_max_blobs_per_tx.json");
val defs = mapi (define_test "1167") tests;
