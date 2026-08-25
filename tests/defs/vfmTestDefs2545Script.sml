Theory vfmTestDefs2545[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_CALLCODE_ToEmpty_OOGRevert_Paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_CALLCODE_ToEmpty_OOGRevert_Paris.json");
val defs = mapi (define_test "2545") tests;
