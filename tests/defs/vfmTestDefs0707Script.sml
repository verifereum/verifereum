Theory vfmTestDefs0707[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_SuicideEnd.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcodecall_110_SuicideEnd.json");
val defs = mapi (define_test "0707") tests;
