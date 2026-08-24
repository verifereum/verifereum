Theory vfmTest0504[no_sig_docs]
Ancestors vfmTestDefs0504
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0504_0.nsv", "result0504_1.nsv"];
val thyn = "vfmTestDefs0504";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
