Theory vfmTestDefs1922[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcode_check_pc/static_callcode_check_pc.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcode_check_pc/static_callcode_check_pc.json");
val defs = mapi (define_test "1922") tests;
