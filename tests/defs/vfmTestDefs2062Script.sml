open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2062";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CREATE_EmptyContractWithStorageAndCallIt_0wei.json";
val defs = mapi (define_test "2062") tests;
val () = export_theory_no_docs ();
