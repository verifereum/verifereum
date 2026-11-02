Theory vfmTestDefs0868[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8282_builder_execution_requests/request_predeploys/value_without_calldata_from_transaction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8282_builder_execution_requests/request_predeploys/value_without_calldata_from_transaction.json");
val defs = mapi (define_test "0868") tests;
