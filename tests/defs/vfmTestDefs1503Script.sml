Theory vfmTestDefs1503[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP4844_blobtransactions/empty_blobhash_list/empty_blobhash_list.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP4844_blobtransactions/empty_blobhash_list/empty_blobhash_list.json");
val defs = mapi (define_test "1503") tests;
