Theory vfmTestDefs2188[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stZeroCallsRevert/zero_value_suicide_oog_revert/zero_value_suicide_oog_revert.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stZeroCallsRevert/zero_value_suicide_oog_revert/zero_value_suicide_oog_revert.json");
val defs = mapi (define_test "2188") tests;
