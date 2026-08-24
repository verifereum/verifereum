Theory vfmTest0632[no_sig_docs]
Ancestors vfmTestDefs0632
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0632_0.nsv", "result0632_1.nsv"];
val thyn = "vfmTestDefs0632";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
