Theory vfmTestDefs1094[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/scenarios/scenarios/scenarios.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/scenarios/scenarios/scenarios.json");
val defs = mapi (define_test "1094") tests;
