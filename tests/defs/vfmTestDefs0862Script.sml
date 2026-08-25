Theory vfmTestDefs0862[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterInitCodeReturndata3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCreateTest/CreateOOGafterInitCodeReturndata3.json");
val defs = mapi (define_test "0862") tests;
