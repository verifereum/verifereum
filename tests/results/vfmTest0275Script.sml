open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0275Theory;
val () = new_theory "vfmTest0275";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0275") $ get_result_defs "vfmTestDefs0275";
val () = export_theory_no_docs ();
