Theory vfmTest0300[no_sig_docs]
Ancestors vfmTestDefs0300
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0300_0.nsv"];
val thyn = "vfmTestDefs0300";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
