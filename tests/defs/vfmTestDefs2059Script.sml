open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2059";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CREATE_ContractSuicideDuringInit_ThenStoreThenReturn.json";
val defs = mapi (define_test "2059") tests;
val () = export_theory_no_docs ();
