open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0913Theory;
val () = new_theory "vfmTest0913";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0913") $ get_result_defs "vfmTestDefs0913";
val () = export_theory_no_docs ();
