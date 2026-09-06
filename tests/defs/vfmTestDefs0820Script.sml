Theory vfmTestDefs0820[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stLogTests/log1_max_topic/log1_max_topic.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stLogTests/log1_max_topic/log1_max_topic.json");
val defs = mapi (define_test "0820") tests;
