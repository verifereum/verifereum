Theory vfmTestDefs2420[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs_2/call_pointer_to_created_from_create_after_oog_call_again.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs_2/call_pointer_to_created_from_create_after_oog_call_again.json");
val defs = mapi (define_test "2420") tests;
