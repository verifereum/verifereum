open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0559Theory;
val () = new_theory "vfmTest0559";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0559") $ get_result_defs "vfmTestDefs0559";
val () = export_theory_no_docs ();
