Theory vfmTestDefs1427[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/delegatecall_emptycontract/delegatecall_emptycontract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/delegatecall_emptycontract/delegatecall_emptycontract.json");
val defs = mapi (define_test "1427") tests;
