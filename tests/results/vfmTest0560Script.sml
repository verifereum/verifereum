Theory vfmTest0560[no_sig_docs]
Ancestors vfmTestDefs0560
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0560_0.nsv"];
val thyn = "vfmTestDefs0560";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
