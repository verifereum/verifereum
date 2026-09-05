Theory vfmTestDefs0625[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2collision_selfdestructed_revert/create2collision_selfdestructed_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2collision_selfdestructed_revert/create2collision_selfdestructed_revert.json");
val defs = mapi (define_test "0625") tests;
