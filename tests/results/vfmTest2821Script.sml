open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2821Theory;
val () = new_theory "vfmTest2821";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2821") $ get_result_defs "vfmTestDefs2821";
val () = export_theory_no_docs ();
