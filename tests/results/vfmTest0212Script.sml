open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0212Theory;
val () = new_theory "vfmTest0212";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0212") $ get_result_defs "vfmTestDefs0212";
val () = export_theory_no_docs ();
