Theory vfmTestDefs1361[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCreate2/create2collision_code2/create2collision_code2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCreate2/create2collision_code2/create2collision_code2.json");
val defs = mapi (define_test "1361") tests;
