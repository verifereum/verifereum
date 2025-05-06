open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0755Theory;
val () = new_theory "vfmTest0755";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0755") $ get_result_defs "vfmTestDefs0755";
val () = export_theory_no_docs ();
