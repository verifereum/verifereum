Theory vfmTestDefs0150[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/validation/test_gas_limit_below_minimum.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/validation/test_gas_limit_below_minimum.json");
val defs = mapi (define_test "0150") tests;
