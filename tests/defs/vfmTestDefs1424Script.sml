Theory vfmTestDefs1424[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/deleagate_call_after_value_transfer/deleagate_call_after_value_transfer.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/deleagate_call_after_value_transfer/deleagate_call_after_value_transfer.json");
val defs = mapi (define_test "1424") tests;
