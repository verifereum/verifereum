Theory vfmTestDefs1035[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stHomesteadSpecific/contractCreationOOGdontLeaveEmptyContract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stHomesteadSpecific/contractCreationOOGdontLeaveEmptyContract.json");
val defs = mapi (define_test "1035") tests;
