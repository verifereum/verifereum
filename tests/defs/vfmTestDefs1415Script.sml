Theory vfmTestDefs1415[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/call_output1/call_output1.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/call_output1/call_output1.json");
val defs = mapi (define_test "1415") tests;
