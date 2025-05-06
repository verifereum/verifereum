open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0466Theory;
val () = new_theory "vfmTest0466";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0466") $ get_result_defs "vfmTestDefs0466";
val () = export_theory_no_docs ();
