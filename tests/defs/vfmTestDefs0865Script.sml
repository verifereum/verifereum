Theory vfmTestDefs0865[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryStressTest/callcode_bounds4/callcode_bounds4.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryStressTest/callcode_bounds4/callcode_bounds4.json");
val defs = mapi (define_test "0865") tests;
