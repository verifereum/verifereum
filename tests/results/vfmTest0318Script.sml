open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0318Theory;
val () = new_theory "vfmTest0318";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0318") $ get_result_defs "vfmTestDefs0318";
val () = export_theory_no_docs ();
