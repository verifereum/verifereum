Theory vfmTestDefs2794[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stSystemOperationsTest/suicide_caller_addres_too_big_right/suicide_caller_addres_too_big_right.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stSystemOperationsTest/suicide_caller_addres_too_big_right/suicide_caller_addres_too_big_right.json");
val defs = mapi (define_test "2794") tests;
