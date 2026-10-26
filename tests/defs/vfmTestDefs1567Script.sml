Theory vfmTestDefs1567[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stLogTests/log3_caller/log3_caller.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stLogTests/log3_caller/log3_caller.json");
val defs = mapi (define_test "1567") tests;
