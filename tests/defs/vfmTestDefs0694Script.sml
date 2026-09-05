Theory vfmTestDefs0694[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/delegatecall_value_check/delegatecall_value_check.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/delegatecall_value_check/delegatecall_value_check.json");
val defs = mapi (define_test "0694") tests;
