open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0267Theory;
val () = new_theory "vfmTest0267";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0267") $ get_result_defs "vfmTestDefs0267";
val () = export_theory_no_docs ();
