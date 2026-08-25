Theory vfmTest0049[no_sig_docs]
Ancestors vfmTestDefs0049
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0049_0.nsv"];
val thyn = "vfmTestDefs0049";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
