open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1820Theory;
val () = new_theory "vfmTest1820";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1820") $ get_result_defs "vfmTestDefs1820";
val () = export_theory_no_docs ();
