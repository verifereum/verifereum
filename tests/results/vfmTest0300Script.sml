open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0300Theory;
val () = new_theory "vfmTest0300";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0300") $ get_result_defs "vfmTestDefs0300";
val () = export_theory_no_docs ();
