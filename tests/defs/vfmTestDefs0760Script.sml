Theory vfmTestDefs0760[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP3651_warmcoinbase/coinbase_warm_account_call_gas/coinbase_warm_account_call_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP3651_warmcoinbase/coinbase_warm_account_call_gas/coinbase_warm_account_call_gas.json");
val defs = mapi (define_test "0760") tests;
