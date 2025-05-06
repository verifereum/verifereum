open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0328Theory;
val () = new_theory "vfmTest0328";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0328") $ get_result_defs "vfmTestDefs0328";
val () = export_theory_no_docs ();
