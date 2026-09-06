Theory vfmTestDefs1762[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSpecialTest/selfdestruct_eip2929/selfdestruct_eip2929.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSpecialTest/selfdestruct_eip2929/selfdestruct_eip2929.json");
val defs = mapi (define_test "1762") tests;
