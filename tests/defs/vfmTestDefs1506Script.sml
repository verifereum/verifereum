Theory vfmTestDefs1506[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP4844_blobtransactions/wrong_blobhash_version/wrong_blobhash_version.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP4844_blobtransactions/wrong_blobhash_version/wrong_blobhash_version.json");
val defs = mapi (define_test "1506") tests;
