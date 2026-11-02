Theory vfmTestDefs1365[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stCreate2/create2collision_selfdestructed_oog/create2collision_selfdestructed_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stCreate2/create2collision_selfdestructed_oog/create2collision_selfdestructed_oog.json");
val defs = mapi (define_test "1365") tests;
