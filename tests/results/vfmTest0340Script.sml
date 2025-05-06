open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0340Theory;
val () = new_theory "vfmTest0340";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0340") $ get_result_defs "vfmTestDefs0340";
val () = export_theory_no_docs ();
