Theory vfmTestDefs2555[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_DELEGATECALL_ToOneStorageKey_OOGRevert_Paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_DELEGATECALL_ToOneStorageKey_OOGRevert_Paris.json");
val defs = mapi (define_test "2555") tests;
