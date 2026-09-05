Theory vfmTestDefs2423[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs_2/delegation_replacement_call_previous_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs_2/delegation_replacement_call_previous_contract.json");
val defs = mapi (define_test "2423") tests;
