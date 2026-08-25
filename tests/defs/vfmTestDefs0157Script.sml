Theory vfmTestDefs0157[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/istanbul/eip1344_chainid/test_chainid.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/istanbul/eip1344_chainid/test_chainid.json");
val defs = mapi (define_test "0157") tests;
