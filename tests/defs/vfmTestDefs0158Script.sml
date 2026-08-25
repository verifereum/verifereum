Theory vfmTestDefs0158[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/istanbul/eip152_blake2/test_blake2_precompile_delegatecall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/istanbul/eip152_blake2/test_blake2_precompile_delegatecall.json");
val defs = mapi (define_test "0158") tests;
