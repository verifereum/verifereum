Theory vfmTestDefs0708[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_SuicideMiddle.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_SuicideMiddle.json");
val defs = mapi (define_test "0708") tests;
