Theory vfmTestDefs2558[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_SUICIDE_ToNonZeroBalance_OOGRevert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_SUICIDE_ToNonZeroBalance_OOGRevert.json");
val defs = mapi (define_test "2558") tests;
