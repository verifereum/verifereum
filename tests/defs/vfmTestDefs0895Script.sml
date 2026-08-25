Theory vfmTestDefs0895[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallEmptycontract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stDelegatecallTestHomestead/delegatecallEmptycontract.json");
val defs = mapi (define_test "0895") tests;
