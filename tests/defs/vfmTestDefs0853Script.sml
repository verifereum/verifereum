Theory vfmTestDefs0853[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stLogTests/log_in_oog_call/log_in_oog_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stLogTests/log_in_oog_call/log_in_oog_call.json");
val defs = mapi (define_test "0853") tests;
