Theory vfmTestDefs0646[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreateTest/create_collision_to_empty2/create_collision_to_empty2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreateTest/create_collision_to_empty2/create_collision_to_empty2.json");
val defs = mapi (define_test "0646") tests;
