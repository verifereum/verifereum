open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0820Theory;
val () = new_theory "vfmTest0820";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0820") $ get_result_defs "vfmTestDefs0820";
val () = export_theory_no_docs ();
