Theory vfmTest0521[no_sig_docs]
Ancestors vfmTestDefs0521
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0521_0.nsv", "result0521_1.nsv"];
val thyn = "vfmTestDefs0521";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
