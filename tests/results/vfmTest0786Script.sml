open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0786Theory;
val () = new_theory "vfmTest0786";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0786") $ get_result_defs "vfmTestDefs0786";
val () = export_theory_no_docs ();
