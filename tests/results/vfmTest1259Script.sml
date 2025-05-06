open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1259Theory;
val () = new_theory "vfmTest1259";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1259") $ get_result_defs "vfmTestDefs1259";
val () = export_theory_no_docs ();
