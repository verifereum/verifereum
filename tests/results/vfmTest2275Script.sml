open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2275Theory;
val () = new_theory "vfmTest2275";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2275") $ get_result_defs "vfmTestDefs2275";
val () = export_theory_no_docs ();
