open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0976Theory;
val () = new_theory "vfmTest0976";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0976") $ get_result_defs "vfmTestDefs0976";
val () = export_theory_no_docs ();
