open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0207";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/calls/delegate_call_targets.json";
val defs = mapi (define_test "0207") tests;
val () = export_theory_no_docs ();
