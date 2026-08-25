Theory vfmTestDefs0334[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_pointer_contract_pointer_loop.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_pointer_contract_pointer_loop.json");
val defs = mapi (define_test "0334") tests;
