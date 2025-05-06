open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0710Theory;
val () = new_theory "vfmTest0710";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0710") $ get_result_defs "vfmTestDefs0710";
val () = export_theory_no_docs ();
