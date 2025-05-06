open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0393Theory;
val () = new_theory "vfmTest0393";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0393") $ get_result_defs "vfmTestDefs0393";
val () = export_theory_no_docs ();
