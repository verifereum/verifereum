open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0084Theory;
val () = new_theory "vfmTest0084";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0084") $ get_result_defs "vfmTestDefs0084";
val () = export_theory_no_docs ();
