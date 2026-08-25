Theory vfmTestDefs0374[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_set_code_using_chain_specific_id.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_set_code_using_chain_specific_id.json");
val defs = mapi (define_test "0374") tests;
