Theory vfmTestDefs0613[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/create2_oog_from_call_refunds/create2_oog_from_call_refunds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/create2_oog_from_call_refunds/create2_oog_from_call_refunds.json");
val defs = mapi (define_test "0613") tests;
