Theory vfmTestDefs0382[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/shanghai/eip3651_warm_coinbase/test_warm_coinbase_call_out_of_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/shanghai/eip3651_warm_coinbase/test_warm_coinbase_call_out_of_gas.json");
val defs = mapi (define_test "0382") tests;
