open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0201Theory;
val () = new_theory "vfmTest0201";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0201") $ get_result_defs "vfmTestDefs0201";
val () = export_theory_no_docs ();
