Theory vfmTestDefs0322[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_ext_code_on_chain_delegating_set_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_ext_code_on_chain_delegating_set_code.json");
val defs = mapi (define_test "0322") tests;
