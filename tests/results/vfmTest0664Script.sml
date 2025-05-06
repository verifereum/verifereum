open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0664Theory;
val () = new_theory "vfmTest0664";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0664") $ get_result_defs "vfmTestDefs0664";
val () = export_theory_no_docs ();
