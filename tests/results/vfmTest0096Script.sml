open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0096Theory;
val () = new_theory "vfmTest0096";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0096") $ get_result_defs "vfmTestDefs0096";
val () = export_theory_no_docs ();
