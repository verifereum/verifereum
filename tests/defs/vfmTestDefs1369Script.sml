Theory vfmTestDefs1369[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCreate2/create_message_reverted_oog_in_init2/create_message_reverted_oog_in_init2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCreate2/create_message_reverted_oog_in_init2/create_message_reverted_oog_in_init2.json");
val defs = mapi (define_test "1369") tests;
