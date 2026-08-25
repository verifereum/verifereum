Theory vfmTestDefs0738[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecallcode_011_SuicideEnd.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallDelegateCodesHomestead/callcallcodecallcode_011_SuicideEnd.json");
val defs = mapi (define_test "0738") tests;
