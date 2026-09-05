Theory vfmTestDefs0429[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCallCodes/callcodecallcodecallcode_111_oogm_after/callcodecallcodecallcode_111_oogm_after.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCallCodes/callcodecallcodecallcode_111_oogm_after/callcodecallcodecallcode_111_oogm_after.json");
val defs = mapi (define_test "0429") tests;
