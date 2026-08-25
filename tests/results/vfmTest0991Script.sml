Theory vfmTest0991[no_sig_docs]
Ancestors vfmTestDefs0991
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0991_0.nsv"];
val thyn = "vfmTestDefs0991";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
