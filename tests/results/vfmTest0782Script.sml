open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0782Theory;
val () = new_theory "vfmTest0782";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0782") $ get_result_defs "vfmTestDefs0782";
val () = export_theory_no_docs ();
