open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2174";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CREATE_ContractSuicideDuringInit_WithValue.json";
val defs = mapi (define_test "2174") tests;
val () = export_theory_no_docs ();
