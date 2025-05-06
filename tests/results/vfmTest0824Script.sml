open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0824Theory;
val () = new_theory "vfmTest0824";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0824") $ get_result_defs "vfmTestDefs0824";
val () = export_theory_no_docs ();
