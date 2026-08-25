Theory vfmTestDefs0300[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_address_from_set_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_address_from_set_code.json");
val defs = mapi (define_test "0300") tests;
