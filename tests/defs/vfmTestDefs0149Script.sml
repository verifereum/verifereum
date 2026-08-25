Theory vfmTestDefs0149[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/touch/test_zero_gas_price_and_touching.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/touch/test_zero_gas_price_and_touching.json");
val defs = mapi (define_test "0149") tests;
