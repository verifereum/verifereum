open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0137Theory;
val () = new_theory "vfmTest0137";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0137") $ get_result_defs "vfmTestDefs0137";
val () = export_theory_no_docs ();
