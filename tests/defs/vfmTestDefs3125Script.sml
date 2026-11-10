Theory vfmTestDefs3125[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip7702_set_code_tx/set_code_txs/tx_into_chain_delegating_set_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip7702_set_code_tx/set_code_txs/tx_into_chain_delegating_set_code.json");
val defs = mapi (define_test "3125") tests;
