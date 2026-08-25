Theory vfmTestDefs2559[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_SUICIDE_ToOneStorageKey_OOGRevert_Paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_SUICIDE_ToOneStorageKey_OOGRevert_Paris.json");
val defs = mapi (define_test "2559") tests;
