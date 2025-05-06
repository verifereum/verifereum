open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0914Theory;
val () = new_theory "vfmTest0914";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0914") $ get_result_defs "vfmTestDefs0914";
val () = export_theory_no_docs ();
