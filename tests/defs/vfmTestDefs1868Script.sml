Theory vfmTestDefs1868[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stRefundTest/refundSuicide50procentCap.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stRefundTest/refundSuicide50procentCap.json");
val defs = mapi (define_test "1868") tests;
