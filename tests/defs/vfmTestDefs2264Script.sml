Theory vfmTestDefs2264[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/vmLogTest/log4/log4.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/vmLogTest/log4/log4.json");
val defs = mapi (define_test "2264") tests;
