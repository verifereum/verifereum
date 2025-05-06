open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1913Theory;
val () = new_theory "vfmTest1913";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1913") $ get_result_defs "vfmTestDefs1913";
val () = export_theory_no_docs ();
