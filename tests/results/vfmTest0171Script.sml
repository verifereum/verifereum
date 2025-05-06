open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0171Theory;
val () = new_theory "vfmTest0171";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0171") $ get_result_defs "vfmTestDefs0171";
val () = export_theory_no_docs ();
