Theory vfmTestDefs3150[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/shanghai/eip3651_warm_coinbase/warm_coinbase/warm_coinbase_gas_usage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/shanghai/eip3651_warm_coinbase/warm_coinbase/warm_coinbase_gas_usage.json");
val defs = mapi (define_test "3150") tests;
