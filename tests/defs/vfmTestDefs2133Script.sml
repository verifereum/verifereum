Theory vfmTestDefs2133[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecoverCheckLength.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecoverCheckLength.json");
val defs = mapi (define_test "2133") tests;
