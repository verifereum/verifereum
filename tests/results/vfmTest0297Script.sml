open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0297Theory;
val () = new_theory "vfmTest0297";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0297") $ get_result_defs "vfmTestDefs0297";
val () = export_theory_no_docs ();
