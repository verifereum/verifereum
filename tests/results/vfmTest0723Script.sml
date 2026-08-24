Theory vfmTest0723[no_sig_docs]
Ancestors vfmTestDefs0723
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0723_0.nsv"];
val thyn = "vfmTestDefs0723";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
