Theory vfmTestDefs0679[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/call_output3partial/call_output3partial.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/call_output3partial/call_output3partial.json");
val defs = mapi (define_test "0679") tests;
