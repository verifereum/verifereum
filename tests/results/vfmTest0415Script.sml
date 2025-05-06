open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0415Theory;
val () = new_theory "vfmTest0415";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0415") $ get_result_defs "vfmTestDefs0415";
val () = export_theory_no_docs ();
