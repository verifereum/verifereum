open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0553Theory;
val () = new_theory "vfmTest0553";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0553") $ get_result_defs "vfmTestDefs0553";
val () = export_theory_no_docs ();
