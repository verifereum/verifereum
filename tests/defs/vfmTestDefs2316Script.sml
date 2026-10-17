Theory vfmTestDefs2316[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7251_consolidations/consolidations/consolidation_requests.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7251_consolidations/consolidations/consolidation_requests.json");
val defs = mapi (define_test "2316") tests;
