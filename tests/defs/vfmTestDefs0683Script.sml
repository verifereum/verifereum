Theory vfmTestDefs0683[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/callcode_output3/callcode_output3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/callcode_output3/callcode_output3.json");
val defs = mapi (define_test "0683") tests;
