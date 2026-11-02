Theory vfmTestDefs1018[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/constantinople/eip1014_create2/deterministic_deployment/deterministic_deployment.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/constantinople/eip1014_create2/deterministic_deployment/deterministic_deployment.json");
val defs = mapi (define_test "1018") tests;
