Theory vfmTest0400[no_sig_docs]
Ancestors vfmTestDefs0400
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0400_0.nsv"];
val thyn = "vfmTestDefs0400";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
