open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0674Theory;
val () = new_theory "vfmTest0674";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0674") $ get_result_defs "vfmTestDefs0674";
val () = export_theory_no_docs ();
