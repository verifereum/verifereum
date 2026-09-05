Theory vfmTestDefs0605[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2_init_codes/create2_init_codes.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2_init_codes/create2_init_codes.json");
val defs = mapi (define_test "0605") tests;
