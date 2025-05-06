open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0395Theory;
val () = new_theory "vfmTest0395";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0395") $ get_result_defs "vfmTestDefs0395";
val () = export_theory_no_docs ();
