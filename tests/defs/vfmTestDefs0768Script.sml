Theory vfmTestDefs0768[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP4844_blobtransactions/create_blobhash_tx/create_blobhash_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP4844_blobtransactions/create_blobhash_tx/create_blobhash_tx.json");
val defs = mapi (define_test "0768") tests;
