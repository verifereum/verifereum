Theory vfmTestDefs2055[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_return1_for_dynamic_jump0/call_to_return1_for_dynamic_jump0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/call_to_return1_for_dynamic_jump0/call_to_return1_for_dynamic_jump0.json");
val defs = mapi (define_test "2055") tests;
