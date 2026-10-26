Theory vfmTestDefs1488[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP2930/manual_create/manual_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP2930/manual_create/manual_create.json");
val defs = mapi (define_test "1488") tests;
