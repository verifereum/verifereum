open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0250Theory;
val () = new_theory "vfmTest0250";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0250") $ get_result_defs "vfmTestDefs0250";
val () = export_theory_no_docs ();
