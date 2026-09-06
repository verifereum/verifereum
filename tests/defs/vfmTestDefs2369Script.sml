Theory vfmTestDefs2369[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs/delegation_clearing_and_set_preserves_storage.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs/delegation_clearing_and_set_preserves_storage.json");
val defs = mapi (define_test "2369") tests;
