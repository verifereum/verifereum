Theory vfmTestDefs2266[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/vmTests/env_info/env_info.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/vmTests/env_info/env_info.json");
val defs = mapi (define_test "2266") tests;
