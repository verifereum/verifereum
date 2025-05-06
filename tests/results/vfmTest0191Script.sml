open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0191Theory;
val () = new_theory "vfmTest0191";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0191") $ get_result_defs "vfmTestDefs0191";
val () = export_theory_no_docs ();
