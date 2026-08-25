Theory vfmTestDefs0283[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7251_consolidations/test_consolidation_requests_negative.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7251_consolidations/test_consolidation_requests_negative.json");
val defs = mapi (define_test "0283") tests;
