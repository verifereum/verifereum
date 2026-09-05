Theory vfmTestDefs0690[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/delegatecall_in_initcode_to_existing_contract/delegatecall_in_initcode_to_existing_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/delegatecall_in_initcode_to_existing_contract/delegatecall_in_initcode_to_existing_contract.json");
val defs = mapi (define_test "0690") tests;
