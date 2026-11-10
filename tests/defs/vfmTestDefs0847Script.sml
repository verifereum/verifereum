Theory vfmTestDefs0847[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8282_builder_execution_requests/builder_deposit_disable/builder_deposit_inhibited.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8282_builder_execution_requests/builder_deposit_disable/builder_deposit_inhibited.json");
val defs = mapi (define_test "0847") tests;
