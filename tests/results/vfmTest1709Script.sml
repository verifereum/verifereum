open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1709Theory;
val () = new_theory "vfmTest1709";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1709") $ get_result_defs "vfmTestDefs1709";
val () = export_theory_no_docs ();
