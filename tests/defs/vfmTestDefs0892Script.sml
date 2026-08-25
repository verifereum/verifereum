Theory vfmTestDefs0892[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/deleagateCallAfterValueTransfer.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stDelegatecallTestHomestead/deleagateCallAfterValueTransfer.json");
val defs = mapi (define_test "0892") tests;
