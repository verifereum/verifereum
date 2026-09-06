Theory vfmTestDefs1761[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSpecialTest/push32without_byte/push32without_byte.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSpecialTest/push32without_byte/push32without_byte.json");
val defs = mapi (define_test "1761") tests;
