open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2712Theory;
val () = new_theory "vfmTest2712";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2712") $ get_result_defs "vfmTestDefs2712";
val () = export_theory_no_docs ();
