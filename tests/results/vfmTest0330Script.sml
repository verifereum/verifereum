Theory vfmTest0330[no_sig_docs]
Ancestors vfmTestDefs0330
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0330_0.nsv", "result0330_1.nsv"];
val thyn = "vfmTestDefs0330";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
