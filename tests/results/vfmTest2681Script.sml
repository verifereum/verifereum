open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2681Theory;
val () = new_theory "vfmTest2681";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2681") $ get_result_defs "vfmTestDefs2681";
val () = export_theory_no_docs ();
