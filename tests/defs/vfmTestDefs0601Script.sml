Theory vfmTestDefs0601[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2_first_byte_loop/create2_first_byte_loop.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2_first_byte_loop/create2_first_byte_loop.json");
val defs = mapi (define_test "0601") tests;
