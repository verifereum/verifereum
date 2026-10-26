Theory vfmTestDefs3147[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip7702_set_code_tx/set_code_txs_2/precompile_call_from_delegated_frame.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip7702_set_code_tx/set_code_txs_2/precompile_call_from_delegated_frame.json");
val defs = mapi (define_test "3147") tests;
