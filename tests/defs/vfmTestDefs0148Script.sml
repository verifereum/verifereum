Theory vfmTestDefs0148[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/frontier/scenarios/test_scenarios.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/frontier/scenarios/test_scenarios.json");
val defs = mapi (define_test "0148") tests;
