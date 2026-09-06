Theory vfmTestDefs1779[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_ab_acalls_suicide1/static_ab_acalls_suicide1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_ab_acalls_suicide1/static_ab_acalls_suicide1.json");
val defs = mapi (define_test "1779") tests;
