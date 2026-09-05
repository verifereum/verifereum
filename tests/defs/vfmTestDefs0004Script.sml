Theory vfmTestDefs0004[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/berlin/eip2929_gas_cost_increases/warm_status_revert/access_list_slot_warmth_survives_failed_create2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/berlin/eip2929_gas_cost_increases/warm_status_revert/access_list_slot_warmth_survives_failed_create2.json");
val defs = mapi (define_test "0004") tests;
