Theory vfmTestDefs2414[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs/set_code_using_valid_synthetic_signatures.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs/set_code_using_valid_synthetic_signatures.json");
val defs = mapi (define_test "2414") tests;
