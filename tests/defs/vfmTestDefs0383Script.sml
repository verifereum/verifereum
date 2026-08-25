Theory vfmTestDefs0383[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip3651_warm_coinbase/test_warm_coinbase_gas_usage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip3651_warm_coinbase/test_warm_coinbase_gas_usage.json");
val defs = mapi (define_test "0383") tests;
