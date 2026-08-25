Theory vfmTestDefs0564[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecall_010_SuicideEnd.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallCodes/callcallcodecall_010_SuicideEnd.json");
val defs = mapi (define_test "0564") tests;
