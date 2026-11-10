Theory vfmTestDefs0851[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip8282_builder_execution_requests/builder_exits/builder_exit_backlog_with_new_requests.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip8282_builder_execution_requests/builder_exits/builder_exit_backlog_with_new_requests.json");
val defs = mapi (define_test "0851") tests;
