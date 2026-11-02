Theory vfmTestDefs0863[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8282_builder_execution_requests/request_predeploys/request_from_set_code_delegated_account.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8282_builder_execution_requests/request_predeploys/request_from_set_code_delegated_account.json");
val defs = mapi (define_test "0863") tests;
