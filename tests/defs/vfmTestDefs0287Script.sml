Theory vfmTestDefs0287[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7251_consolidations/test_system_contract_errors.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7251_consolidations/test_system_contract_errors.json");
val defs = mapi (define_test "0287") tests;
