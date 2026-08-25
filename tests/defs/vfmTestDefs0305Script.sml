Theory vfmTestDefs0305[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_call_to_pre_authorized_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7702_set_code_tx/test_call_to_pre_authorized_oog.json");
val defs = mapi (define_test "0305") tests;
