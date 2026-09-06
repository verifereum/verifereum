Theory vfmTestDefs2340[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7251_consolidations/consolidations/consolidation_requests_negative.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7251_consolidations/consolidations/consolidation_requests_negative.json");
val defs = mapi (define_test "2340") tests;
