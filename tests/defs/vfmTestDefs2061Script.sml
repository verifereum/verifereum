open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2061";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CREATE_EmptyContractAndCallIt_0wei.json";
val defs = mapi (define_test "2061") tests;
val () = export_theory_no_docs ();
