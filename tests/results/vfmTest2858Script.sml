open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2858Theory;
val () = new_theory "vfmTest2858";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2858") $ get_result_defs "vfmTestDefs2858";
val () = export_theory_no_docs ();
