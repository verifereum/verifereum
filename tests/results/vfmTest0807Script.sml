open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0807Theory;
val () = new_theory "vfmTest0807";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0807") $ get_result_defs "vfmTestDefs0807";
val () = export_theory_no_docs ();
