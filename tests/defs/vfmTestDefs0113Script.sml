open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0113";
val tests = json_path_to_tests "../fixtures/blockchain_tests/frontier/opcodes/calldatacopy/calldatacopy.json";
val defs = mapi (define_test "0113") tests;
val () = export_theory_no_docs ();
