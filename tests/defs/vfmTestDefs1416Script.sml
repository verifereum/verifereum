Theory vfmTestDefs1416[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/call_output2/call_output2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/call_output2/call_output2.json");
val defs = mapi (define_test "1416") tests;
