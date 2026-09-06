Theory vfmTestDefs0005[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/berlin/eip2929_gas_cost_increases/warm_status_revert/account_warm_status_reverted_by_subcall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/berlin/eip2929_gas_cost_increases/warm_status_revert/account_warm_status_reverted_by_subcall.json");
val defs = mapi (define_test "0005") tests;
