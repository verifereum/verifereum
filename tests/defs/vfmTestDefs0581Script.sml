Theory vfmTestDefs0581[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcode_checkPC.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCallCodes/callcode_checkPC.json");
val defs = mapi (define_test "0581") tests;
