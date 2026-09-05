Theory vfmTestDefs2439[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/shanghai/eip3651_warm_coinbase/warm_coinbase/warm_coinbase_call_out_of_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/shanghai/eip3651_warm_coinbase/warm_coinbase/warm_coinbase_call_out_of_gas.json");
val defs = mapi (define_test "2439") tests;
