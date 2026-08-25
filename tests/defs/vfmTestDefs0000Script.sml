Theory vfmTestDefs0000[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/berlin/eip2929_gas_cost_increases/test_call_insufficient_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/berlin/eip2929_gas_cost_increases/test_call_insufficient_balance.json");
val defs = mapi (define_test "0000") tests;
