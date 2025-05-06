open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0077Theory;
val () = new_theory "vfmTest0077";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0077") $ get_result_defs "vfmTestDefs0077";
val () = export_theory_no_docs ();
