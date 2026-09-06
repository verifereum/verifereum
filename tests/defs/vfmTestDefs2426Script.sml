Theory vfmTestDefs2426[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs_2/gas_diff_pointer_vs_direct_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs_2/gas_diff_pointer_vs_direct_call.json");
val defs = mapi (define_test "2426") tests;
