open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0127Theory;
val () = new_theory "vfmTest0127";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0127") $ get_result_defs "vfmTestDefs0127";
val () = export_theory_no_docs ();
