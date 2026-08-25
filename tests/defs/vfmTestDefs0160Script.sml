Theory vfmTestDefs0160[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/istanbul/eip152_blake2/test_blake2b_gas_limit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/istanbul/eip152_blake2/test_blake2b_gas_limit.json");
val defs = mapi (define_test "0160") tests;
