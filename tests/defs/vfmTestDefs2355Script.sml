Theory vfmTestDefs2355[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7702_set_code_tx/gas/call_to_pre_authorized_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7702_set_code_tx/gas/call_to_pre_authorized_oog.json");
val defs = mapi (define_test "2355") tests;
