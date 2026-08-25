Theory vfmTestDefs0147[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/precompiles/test_precompiles.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/precompiles/test_precompiles.json");
val defs = mapi (define_test "0147") tests;
