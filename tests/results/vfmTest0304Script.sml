open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0304Theory;
val () = new_theory "vfmTest0304";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0304") $ get_result_defs "vfmTestDefs0304";
val () = export_theory_no_docs ();
