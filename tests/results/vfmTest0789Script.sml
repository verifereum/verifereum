open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0789Theory;
val () = new_theory "vfmTest0789";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0789") $ get_result_defs "vfmTestDefs0789";
val () = export_theory_no_docs ();
