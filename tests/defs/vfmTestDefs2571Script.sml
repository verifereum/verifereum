Theory vfmTestDefs2571[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_DELEGATECALL_ToOneStorageKey_Paris.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_DELEGATECALL_ToOneStorageKey_Paris.json");
val defs = mapi (define_test "2571") tests;
