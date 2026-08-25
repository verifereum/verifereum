Theory vfmTestDefs0159[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/istanbul/eip152_blake2/test_blake2b.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/istanbul/eip152_blake2/test_blake2b.json");
val defs = mapi (define_test "0159") tests;
