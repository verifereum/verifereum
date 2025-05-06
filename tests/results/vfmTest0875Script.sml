open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0875Theory;
val () = new_theory "vfmTest0875";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0875") $ get_result_defs "vfmTestDefs0875";
val () = export_theory_no_docs ();
